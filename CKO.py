#!/usr/bin/env python3
"""
CYFARE Kernel Optimize V2.0  (Debian-only edition)
=================================================

- Latest Linux Kernel (Update Supported Series!)
- BORE scheduler + CachyOS performance patches (with aggressive multi-source
fallback), builds with Clang/LTO/per-CPU tuning, packages as .deb, and
installs it on Debian/Ubuntu/Mint/MX/Pop!_OS/Kali and every other
Debian-based distribution.
- Default released packages use: All Patches + BORE + Full-LTO + x86-64-v3

This edition:
  * Is Debian/apt only — no RPM/pacman/zypper/apk/emerge paths.
  * Performs smart detection of CPU ISA level, RAM, cores, GPU, disk
    type, and boot loader, and picks aggressive-but-safe defaults tuned
    for a responsive gaming/desktop machine.
  * Uses the BORE scheduler + CachyOS patchset pipeline with
    all the hardening (olddefconfig under the same toolchain, patch fuzz
    tolerance, auto-series fallback, BORE verification, etc.).

Requires: PyQt6  (apt: python3-pyqt6 ; pip: PyQt6)
All build dependencies are installed automatically via apt on first run.
"""

from __future__ import annotations

import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

try:
    from PyQt6.QtCore import (
        Qt, QThread, pyqtSignal, QObject, QSize, QTimer,
    )
    from PyQt6.QtGui import QPalette, QColor, QTextCursor
    from PyQt6.QtWidgets import (
        QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
        QFormLayout, QGroupBox, QLabel, QLineEdit, QComboBox, QSpinBox,
        QCheckBox, QPushButton, QPlainTextEdit, QFileDialog, QMessageBox,
        QTabWidget, QStatusBar, QProgressBar, QStyleFactory, QToolButton,
        QDialog, QDialogButtonBox,
    )
except ImportError:
    sys.stderr.write(
        "PyQt6 is required.\n"
        "  Debian/Ubuntu:  sudo apt install python3-pyqt6\n"
        "  pip:            pip install --user PyQt6\n"
    )
    sys.exit(1)

APP_NAME = "CYFARE Kernel Optimize V2.3"
APP_VERSION = "2.3.0"

KERNEL_ORG_BASE = "https://cdn.kernel.org/pub/linux/kernel"
CACHYOS_RAW = "https://raw.githubusercontent.com/CachyOS/kernel-patches/master"
CACHYOS_API = "https://api.github.com/repos/CachyOS/kernel-patches/contents"
BORE_RAW    = "https://raw.githubusercontent.com/firelzrd/bore-scheduler/main"
BORE_API    = "https://api.github.com/repos/firelzrd/bore-scheduler/contents"

# Kernel series we'll walk as fallback when the chosen series has no
# patches yet. Ordered newest -> oldest.
SUPPORTED_SERIES_ORDER = [
    "7.0", "6.19", "6.18", "6.17", "6.16", "6.15", "6.14", "6.13",
    "6.12", "6.11", "6.10", "6.9", "6.8", "6.7", "6.6",
]


# =============================================================================
# Smart system detection
# =============================================================================

@dataclass
class SystemSpecs:
    """Everything we can learn about the host that influences defaults."""
    # CPU
    arch: str = "x86_64"
    cpu_vendor: str = "unknown"          # intel | amd | other
    cpu_model: str = ""
    cpu_cores: int = 1                   # physical cores (best-effort)
    cpu_threads: int = 1                 # logical CPUs
    cpu_flags: frozenset = frozenset()
    isa_level: str = "x86-64"            # x86-64 | x86-64-v2 | v3 | v4
    # Memory
    ram_gb: int = 0
    swap_gb: int = 0
    # GPU
    has_nvidia: bool = False
    has_amdgpu: bool = False
    has_intel_gpu: bool = False
    # Storage
    root_is_ssd: bool = False
    root_is_nvme: bool = False
    # Boot
    uses_systemd_boot: bool = False
    uses_grub: bool = False
    # Distro
    is_debian_family: bool = False
    distro_id: str = ""
    distro_like: str = ""
    # Toolchain availability
    has_clang: bool = False
    has_lld:   bool = False

    # Convenience
    @property
    def is_gaming_class(self) -> bool:
        """Heuristic: >=6 cores AND >=16 GB RAM AND dGPU present."""
        return (self.cpu_threads >= 12 and self.ram_gb >= 16
                and (self.has_nvidia or self.has_amdgpu))


def _read_text(path: str) -> str:
    try:
        return Path(path).read_text(errors="replace")
    except OSError:
        return ""


def detect_distro() -> tuple[str, str]:
    """Return (ID, ID_LIKE) from /etc/os-release."""
    data: dict[str, str] = {}
    for line in _read_text("/etc/os-release").splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            data[k] = v.strip().strip('"').lower()
    return data.get("ID", ""), data.get("ID_LIKE", "")


def is_debian_based() -> bool:
    """True if ID or ID_LIKE contains 'debian' (covers Ubuntu/Mint/Pop!/Kali/MX/etc)."""
    did, like = detect_distro()
    blob = f" {did} {like} "
    return any(x in blob for x in (" debian ", " ubuntu ")) or (
        shutil.which("apt-get") is not None and shutil.which("dpkg") is not None
    )


def _cpuinfo_flags() -> frozenset:
    txt = _read_text("/proc/cpuinfo")
    for line in txt.splitlines():
        if line.startswith("flags") or line.startswith("Features"):
            return frozenset(line.split(":", 1)[1].split())
    return frozenset()


def _cpuinfo_value(key: str) -> str:
    txt = _read_text("/proc/cpuinfo")
    for line in txt.splitlines():
        if line.startswith(key):
            parts = line.split(":", 1)
            if len(parts) == 2:
                return parts[1].strip()
    return ""


def _detect_isa_level(flags: frozenset) -> str:
    """
    Pick the highest psABI x86-64 level the CPU actually supports.

    Matches the gcc/clang -march=x86-64-vN feature sets.
    """
    # v4: AVX-512F + AVX-512BW + AVX-512CD + AVX-512DQ + AVX-512VL
    v4 = {"avx512f", "avx512bw", "avx512cd", "avx512dq", "avx512vl"}
    if v4.issubset(flags):
        return "x86-64-v4"
    # v3: AVX + AVX2 + BMI1 + BMI2 + F16C + FMA + LZCNT + MOVBE + OSXSAVE
    v3 = {"avx", "avx2", "bmi1", "bmi2", "f16c", "fma", "lzcnt", "movbe"}
    # cpuinfo uses 'bmi1'/'bmi2'; some older kernels print 'bmi1' as just 'bmi'
    if v3.issubset(flags) or (v3 - {"bmi1"}).issubset(flags) and "bmi1" in flags:
        return "x86-64-v3"
    # v2: CMPXCHG16B + LAHF-SAHF + POPCNT + SSE3 + SSE4.1 + SSE4.2 + SSSE3
    v2 = {"cx16", "lahf_lm", "popcnt", "pni", "sse4_1", "sse4_2", "ssse3"}
    if v2.issubset(flags):
        return "x86-64-v2"
    return "x86-64"


def _detect_ram_gb() -> int:
    for line in _read_text("/proc/meminfo").splitlines():
        if line.startswith("MemTotal:"):
            try:
                kb = int(line.split()[1])
                return max(1, kb // (1024 * 1024))
            except (ValueError, IndexError):
                break
    return 0


def _detect_swap_gb() -> int:
    for line in _read_text("/proc/meminfo").splitlines():
        if line.startswith("SwapTotal:"):
            try:
                kb = int(line.split()[1])
                return kb // (1024 * 1024)
            except (ValueError, IndexError):
                break
    return 0


def _detect_gpus() -> tuple[bool, bool, bool]:
    out = ""
    if shutil.which("lspci"):
        try:
            out = subprocess.run(["lspci", "-nn"], capture_output=True,
                                 text=True, timeout=5).stdout.lower()
        except Exception:
            out = ""
    nv = "nvidia" in out
    amd = ("amd" in out and ("radeon" in out or "vga" in out)) or "advanced micro devices" in out and "vga" in out
    intel_gpu = "intel" in out and ("graphics" in out or "vga" in out)
    return nv, amd, intel_gpu


def _detect_root_disk() -> tuple[bool, bool]:
    """Return (is_ssd, is_nvme) for the disk backing /."""
    try:
        mnt = subprocess.run(["findmnt", "-n", "-o", "SOURCE", "/"],
                             capture_output=True, text=True, timeout=3).stdout.strip()
        if not mnt:
            return (False, False)
        # Strip /dev/ prefix and partition suffix
        name = Path(mnt).name
        # Walk up to parent block device
        base = re.sub(r"(p?\d+)$", "", name)
        is_nvme = base.startswith("nvme")
        rot_path = f"/sys/block/{base}/queue/rotational"
        rot = _read_text(rot_path).strip()
        is_ssd = (rot == "0") or is_nvme
        return (is_ssd, is_nvme)
    except Exception:
        return (False, False)


def _detect_bootloader() -> tuple[bool, bool]:
    """Return (uses_systemd_boot, uses_grub)."""
    sd = Path("/boot/loader/loader.conf").exists() or shutil.which("bootctl") is not None
    grub = (Path("/boot/grub/grub.cfg").exists()
            or Path("/boot/grub2/grub.cfg").exists()
            or shutil.which("update-grub") is not None
            or shutil.which("grub-mkconfig") is not None)
    return sd, grub


def detect_system() -> SystemSpecs:
    did, like = detect_distro()
    flags = _cpuinfo_flags()
    model = _cpuinfo_value("model name") or _cpuinfo_value("Hardware")
    vendor_raw = _cpuinfo_value("vendor_id").lower()
    if "intel" in vendor_raw:
        vendor = "intel"
    elif "amd" in vendor_raw:
        vendor = "amd"
    else:
        vendor = "other"

    threads = os.cpu_count() or 1
    # Physical cores: count unique (physical id, core id) pairs
    cores = threads
    try:
        pairs: set[tuple[str, str]] = set()
        phys, core = "", ""
        for line in _read_text("/proc/cpuinfo").splitlines():
            if line.startswith("physical id"):
                phys = line.split(":", 1)[1].strip()
            elif line.startswith("core id"):
                core = line.split(":", 1)[1].strip()
                if phys and core:
                    pairs.add((phys, core))
                    phys, core = "", ""
        if pairs:
            cores = len(pairs)
    except Exception:
        pass

    nv, amd_gpu, intel_gpu = _detect_gpus()
    is_ssd, is_nvme = _detect_root_disk()
    sd_boot, grub = _detect_bootloader()

    return SystemSpecs(
        arch = os.uname().machine,
        cpu_vendor = vendor,
        cpu_model = model.strip(),
        cpu_cores = cores,
        cpu_threads = threads,
        cpu_flags = flags,
        isa_level = _detect_isa_level(flags) if os.uname().machine == "x86_64" else "native",
        ram_gb = _detect_ram_gb(),
        swap_gb = _detect_swap_gb(),
        has_nvidia = nv,
        has_amdgpu = amd_gpu,
        has_intel_gpu = intel_gpu,
        root_is_ssd = is_ssd,
        root_is_nvme = is_nvme,
        uses_systemd_boot = sd_boot,
        uses_grub = grub,
        is_debian_family = is_debian_based(),
        distro_id = did,
        distro_like = like,
        has_clang = shutil.which("clang") is not None,
        has_lld   = shutil.which("ld.lld") is not None,
    )


# =============================================================================
# Build configuration
# =============================================================================

@dataclass
class BuildConfig:
    kernel_series: str = "7.0"
    kernel_version: str = ""            # auto-detect when empty
    local_version: str = "-cyfare"
    march: str = "auto"                 # auto | generic | x86-64-v2/v3/v4 | native
    o_level: str = "3"                  # 2 | 3
    preempt: str = "full"               # none | voluntary | full | rt
    hz: str = "1000"                    # 250 | 300 | 500 | 750 | 1000
    tick: str = "idle"                  # periodic | idle | full
    compiler: str = "auto"              # auto | gcc | clang
    lto: str = "auto"                   # auto | thin | full | no
    jobs: int = os.cpu_count() or 4
    config_mode: str = "auto"           # auto | running | localmod | defconfig | file
    config_file: str = ""
    extra_config: str = ""
    patches: bool = True
    auto_fallback_series: bool = True
    verbose: bool = False
    download_only: bool = False
    build_only: bool = False
    workdir: Path = field(default_factory=lambda: Path.home() / "cyfare-build")
    outdir: Path = field(default_factory=lambda: Path.home() / "cyfare-out")
    # Smart-only flags
    nvidia_tweaks: bool = False
    amdgpu_tweaks: bool = False
    # Logging
    log_to_file: bool = True
    log_file_path: str = ""      # empty = auto (outdir/build-YYYYMMDD-HHMMSS.log)


def smart_defaults(cfg: BuildConfig, sp: SystemSpecs) -> BuildConfig:
    """
    Apply aggressive-but-safe defaults for a desktop/gaming workstation,
    derived from detected hardware.

    Heuristics:
      * march:     highest x86-64-vN the CPU actually supports (portable-ish).
      * compiler:  clang if present (+lld), else gcc.
      * LTO:       ThinLTO if clang AND RAM >= 16 GB; none if clang + <8 GB.
                   Full LTO only offered when RAM >= 32 GB (still Thin default).
      * preempt:   full (desktop/gaming).
      * HZ:        1000.
      * tick:      NO_HZ_IDLE.
      * -O level:  3 (requires CachyOS patchset, which we apply).
      * jobs:      bounded by RAM; LTO needs ~1.5 GB/job, non-LTO ~0.8 GB/job.
      * GPU tweaks: enable vendor-specific config tweaks.
    """
    # ISA / march
    if sp.arch == "x86_64":
        cfg.march = sp.isa_level   # 'x86-64'|'x86-64-v2'|'x86-64-v3'|'x86-64-v4'
        if cfg.march == "x86-64":
            cfg.march = "generic"
    else:
        cfg.march = "generic"

    # Compiler + LTO
    if sp.has_clang and sp.has_lld:
        cfg.compiler = "clang"
        if sp.ram_gb >= 16:
            cfg.lto = "thin"
        elif sp.ram_gb >= 8:
            cfg.lto = "thin"     # still fine, just slower to link
        else:
            cfg.lto = "no"
    else:
        cfg.compiler = "gcc"
        cfg.lto = "no"

    # Scheduler/timing — desktop sweet spot
    cfg.preempt = "full"
    cfg.hz = "1000"
    cfg.tick = "idle"
    cfg.o_level = "3"

    # Parallel jobs — bound by RAM so we don't OOM during LTO link
    if cfg.lto in ("thin", "full"):
        # LTO link-phase is memory hungry. Be conservative.
        per_job_gb = 1.8 if cfg.lto == "thin" else 3.0
    else:
        per_job_gb = 0.9
    by_ram = max(1, int(sp.ram_gb / per_job_gb)) if sp.ram_gb else sp.cpu_threads
    cfg.jobs = max(1, min(sp.cpu_threads, by_ram))

    # Config seed — prefer running kernel to keep hardware support identical
    cfg.config_mode = "auto"

    # Patches and fallback — always on in smart mode
    cfg.patches = True
    cfg.auto_fallback_series = True

    # GPU toggles — enable vendor-specific knobs where they exist
    cfg.nvidia_tweaks = sp.has_nvidia
    cfg.amdgpu_tweaks = sp.has_amdgpu

    return cfg


def describe_system(sp: SystemSpecs) -> str:
    gpu_bits = []
    if sp.has_nvidia:    gpu_bits.append("NVIDIA")
    if sp.has_amdgpu:    gpu_bits.append("AMD")
    if sp.has_intel_gpu: gpu_bits.append("Intel iGPU")
    gpu_str = " + ".join(gpu_bits) or "none detected"
    disk_str = []
    if sp.root_is_nvme: disk_str.append("NVMe")
    elif sp.root_is_ssd: disk_str.append("SSD")
    else:               disk_str.append("HDD/unknown")
    boot = "systemd-boot" if sp.uses_systemd_boot else ("GRUB" if sp.uses_grub else "unknown")
    return (
        f"CPU: {sp.cpu_model or sp.cpu_vendor} "
        f"({sp.cpu_cores}c/{sp.cpu_threads}t, ISA: {sp.isa_level})\n"
        f"RAM: {sp.ram_gb} GB + {sp.swap_gb} GB swap\n"
        f"GPU: {gpu_str}\n"
        f"Disk: {'/'.join(disk_str)}   Boot: {boot}\n"
        f"Distro: {sp.distro_id or '?'} (like {sp.distro_like or '?'})   "
        f"Clang+LLD: {'yes' if sp.has_clang and sp.has_lld else 'no'}"
    )


# =============================================================================
# Root-privilege helper (cached password + sudo -S)
# =============================================================================

class Privileged:
    """Run commands as root. Shows a Qt password dialog once and caches."""

    def __init__(self) -> None:
        self._password: Optional[str] = None
        self._verified = False

    def clear(self) -> None:
        self._password = None
        self._verified = False

    def ensure(self, parent=None) -> bool:
        if os.geteuid() == 0:
            return True
        if self._verified:
            return True
        while True:
            dlg = PasswordDialog(parent)
            if dlg.exec() != QDialog.DialogCode.Accepted:
                return False
            pw = dlg.password()
            try:
                p = subprocess.run(
                    ["sudo", "-S", "-p", "", "-v"],
                    input=(pw + "\n").encode(),
                    capture_output=True, timeout=15,
                )
                if p.returncode == 0:
                    self._password = pw
                    self._verified = True
                    return True
                QMessageBox.warning(parent, APP_NAME,
                                    "Incorrect password. Please try again.")
            except FileNotFoundError:
                QMessageBox.critical(parent, APP_NAME, "'sudo' is not installed.")
                return False
            except subprocess.TimeoutExpired:
                QMessageBox.warning(parent, APP_NAME, "sudo timed out. Try again.")

    def wrap(self, argv: list[str]) -> tuple[list[str], Optional[bytes]]:
        if os.geteuid() == 0:
            return argv, None
        assert self._verified and self._password is not None, \
            "Privileged.ensure() must be called before wrap()"
        return (["sudo", "-S", "-p", ""] + argv,
                (self._password + "\n").encode())


class PasswordDialog(QDialog):
    def __init__(self, parent=None) -> None:
        super().__init__(parent)
        self.setWindowTitle("Authentication required")
        self.setModal(True)
        self.setMinimumWidth(420)
        v = QVBoxLayout(self)
        lbl = QLabel(
            f"<b>{APP_NAME}</b> needs administrator privileges to install "
            f"build dependencies and/or the new kernel.<br><br>"
            f"Enter the password for <b>{os.getenv('USER','user')}</b>:"
        )
        lbl.setWordWrap(True)
        v.addWidget(lbl)
        self.pw = QLineEdit()
        self.pw.setEchoMode(QLineEdit.EchoMode.Password)
        self.pw.setPlaceholderText("sudo password")
        v.addWidget(self.pw)
        bb = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok |
                              QDialogButtonBox.StandardButton.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)
        self.pw.returnPressed.connect(self.accept)
        QTimer.singleShot(0, self.pw.setFocus)

    def password(self) -> str:
        return self.pw.text()


# =============================================================================
# Worker thread: runs the whole build off the UI thread
# =============================================================================

class BuildSignals(QObject):
    log = pyqtSignal(str)
    status = pyqtSignal(str)
    progress = pyqtSignal(int, int)
    done = pyqtSignal(bool, str)


class BuildWorker(QThread):
    def __init__(self, cfg: BuildConfig, sp: SystemSpecs,
                 priv: Privileged, actions: list[str]) -> None:
        super().__init__()
        self.cfg = cfg
        self.sp = sp
        self.priv = priv
        self.actions = actions
        self.sig = BuildSignals()
        self._cancel = False
        self._active_proc: Optional[subprocess.Popen] = None
        self.kernel_full_version: str = ""
        self.effective_series: str = cfg.kernel_series
        self.toolchain: str = "gcc"
        self.active_lto: str = "no"
        self.applied_patches: list[str] = []
        self.failed_patches: list[str] = []
        self.bore_in_tree: bool = False
        self._log_fh: Optional[object] = None
        self.log_file_path: Optional[Path] = None
        self._tail_lines: list[str] = []   # ring buffer for failure diagnosis
        self._tail_max = 200

    # --- logging ------------------------------------------------------------
    def _open_log_file(self) -> None:
        """Open the on-disk log file (if enabled) and write a header."""
        if not self.cfg.log_to_file:
            return
        try:
            if self.cfg.log_file_path:
                p = Path(self.cfg.log_file_path)
            else:
                from datetime import datetime
                self.cfg.outdir.mkdir(parents=True, exist_ok=True)
                ts = datetime.now().strftime("%Y%m%d-%H%M%S")
                p = self.cfg.outdir / f"build-{ts}.log"
            p.parent.mkdir(parents=True, exist_ok=True)
            self._log_fh = open(p, "w", buffering=1, encoding="utf-8",
                                errors="replace")
            self.log_file_path = p
            header = (
                f"# {APP_NAME}\n"
                f"# log opened: {p}\n"
                f"# actions: {self.actions}\n"
                f"# --- BuildConfig ---\n"
            )
            for k, v in self.cfg.__dict__.items():
                header += f"#   {k} = {v}\n"
            header += "# --- SystemSpecs ---\n"
            for line in describe_system(self.sp).splitlines():
                header += f"#   {line}\n"
            header += "# -------------------\n\n"
            self._log_fh.write(header)
        except OSError as e:
            self._log_fh = None
            self.log_file_path = None
            # Can't use self.log() here — we're still constructing it
            self.sig.log.emit(f"[warn] could not open log file: {e}\n")

    def _close_log_file(self) -> None:
        if self._log_fh is not None:
            try:
                self._log_fh.flush()
                self._log_fh.close()
            except Exception:
                pass
            self._log_fh = None

    # --- UI helpers ---------------------------------------------------------
    def log(self, msg: str) -> None:
        self.sig.log.emit(msg)
        # mirror to disk
        if self._log_fh is not None:
            try:
                self._log_fh.write(msg)
            except Exception:
                pass
        # keep a rolling tail for failure reporting
        if msg:
            self._tail_lines.append(msg)
            if len(self._tail_lines) > self._tail_max:
                del self._tail_lines[:len(self._tail_lines) - self._tail_max]

    def status(self, msg: str) -> None:
        self.sig.status.emit(msg)

    def cancel(self) -> None:
        self._cancel = True
        p = self._active_proc
        if p and p.poll() is None:
            try:
                p.terminate()
            except Exception:
                pass

    # --- Kconfig helpers ----------------------------------------------------
    def _kconfig_env(self) -> list[str]:
        """Extra `make` args so Kconfig resolves new symbols correctly for the chosen toolchain."""
        return ["LLVM=1"] if self.toolchain == "clang" else []

    def _make_olddefconfig(self, src: Path) -> None:
        self._run(["make", *self._kconfig_env(), "olddefconfig"], cwd=src)

    # --- subprocess wrappers ------------------------------------------------
    def _run(self, argv: list[str], *, cwd: Optional[Path] = None,
             env: Optional[dict] = None, as_root: bool = False,
             stdin_bytes: Optional[bytes] = None,
             check: bool = True) -> int:
        if self._cancel:
            raise RuntimeError("cancelled")

        if as_root:
            argv, pw_bytes = self.priv.wrap(argv)
            if pw_bytes is not None and stdin_bytes is None:
                stdin_bytes = pw_bytes

        run_env = dict(env if env is not None else os.environ)
        run_env.setdefault("TERM", "dumb")
        run_env.setdefault("DEBIAN_FRONTEND", "noninteractive")

        self.log(f"\n$ {' '.join(shlex.quote(a) for a in argv)}\n")
        try:
            self._active_proc = subprocess.Popen(
                argv,
                cwd=str(cwd) if cwd else None,
                env=run_env,
                stdin=subprocess.PIPE if stdin_bytes is not None else subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                bufsize=0,
            )
        except FileNotFoundError as e:
            raise RuntimeError(f"command not found: {argv[0]} ({e})")

        if stdin_bytes is not None and self._active_proc.stdin:
            try:
                self._active_proc.stdin.write(stdin_bytes)
                self._active_proc.stdin.close()
            except BrokenPipeError:
                pass

        assert self._active_proc.stdout is not None
        for raw in iter(self._active_proc.stdout.readline, b""):
            if self._cancel:
                self._active_proc.terminate()
                break
            try:
                line = raw.decode(errors="replace")
            except Exception:
                line = repr(raw)
            # Suppress wget dot-progress lines that clog the log
            if line.lstrip().startswith(tuple("0123456789")) and "K ." in line:
                continue
            self.log(line)
        rc = self._active_proc.wait()
        self._active_proc = None
        if check and rc != 0:
            raise RuntimeError(f"{argv[0]} exited with status {rc}")
        return rc

    def _http_get(self, url: str, dest: Optional[Path] = None,
                  *, stream: bool = False) -> tuple[bool, bytes]:
        self.log(f"  fetching {url}\n")
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "cyfare/2.0"})
            with urllib.request.urlopen(req, timeout=45) as r:
                total = 0
                try:
                    total = int(r.headers.get("Content-Length") or 0)
                except Exception:
                    total = 0
                do_stream = stream or (dest is not None) or (total > 1 << 20)
                if not do_stream:
                    data = r.read()
                    if dest is not None:
                        dest.write_bytes(data)
                    return True, data

                chunk = 256 * 1024
                got = 0
                last_report = 0
                buf = bytearray() if dest is None else None
                fh = open(dest, "wb") if dest is not None else None
                try:
                    while True:
                        if self._cancel:
                            self.log("  [cancelled]\n")
                            return False, b""
                        b = r.read(chunk)
                        if not b:
                            break
                        if fh is not None:
                            fh.write(b)
                        else:
                            buf.extend(b)  # type: ignore
                        got += len(b)
                        step = max(total // 20, 8 << 20) if total else (8 << 20)
                        if got - last_report >= step:
                            if total:
                                pct = 100.0 * got / total
                                self.status(
                                    f"Downloading… {got/1e6:.1f}/{total/1e6:.1f} MB ({pct:.0f}%)"
                                )
                                self.log(f"  … {got/1e6:.1f} / {total/1e6:.1f} MB\n")
                            else:
                                self.status(f"Downloading… {got/1e6:.1f} MB")
                                self.log(f"  … {got/1e6:.1f} MB\n")
                            last_report = got
                    self.log(f"  done: {got/1e6:.1f} MB\n")
                    return True, (bytes(buf) if buf is not None else b"")
                finally:
                    if fh is not None:
                        fh.close()
        except urllib.error.HTTPError as e:
            self.log(f"  HTTP {e.code} for {url}\n")
            return False, b""
        except urllib.error.URLError as e:
            self.log(f"  network error: {e}\n")
            return False, b""
        except Exception as e:
            self.log(f"  fetch error: {e}\n")
            return False, b""

    def _github_listdir(self, api_url: str) -> list[dict]:
        ok, data = self._http_get(api_url)
        if not ok or not data:
            return []
        try:
            j = json.loads(data)
            return j if isinstance(j, list) else []
        except Exception:
            return []

    # --- build pipeline -----------------------------------------------------
    def run(self) -> None:
        self._open_log_file()
        try:
            if not self.sp.is_debian_family:
                raise RuntimeError(
                    "This tool is Debian/Ubuntu-only. "
                    "apt-get and dpkg must be available."
                )
            for action in self.actions:
                if action == "build":
                    self._do_build()
                elif action == "install":
                    self._do_install()
                elif action == "clean":
                    self._do_clean()
            msg = "Done."
            if self.log_file_path:
                msg += f"  Log: {self.log_file_path}"
            self.sig.done.emit(True, msg)
        except RuntimeError as e:
            self._emit_failure(str(e))
        except Exception as e:
            import traceback
            self.log("\n" + traceback.format_exc())
            self._emit_failure(f"{type(e).__name__}: {e}")
        finally:
            self._close_log_file()

    def _emit_failure(self, reason: str) -> None:
        # Include last error lines in the UI log so the user doesn't have to
        # scroll, and point them at the log file.
        self.log("\n========== FAILURE DIAGNOSIS ==========\n")
        self.log(f"Reason: {reason}\n")
        # Heuristic hints for common failures
        tail_text = "".join(self._tail_lines).lower()
        hints: list[str] = []
        if "error 2" in tail_text and ("lto" in tail_text or
                                        self.active_lto in ("thin", "full")):
            hints.append(
                "LTO link stage is the usual suspect when a vmlinux link "
                "fails with a bare 'Error 2'. Try LTO = Disabled, or reduce "
                "-j (memory pressure during ThinLTO linking)."
            )
        if "oom" in tail_text or "killed" in tail_text or "cannot allocate memory" in tail_text:
            hints.append(
                "Out-of-memory signal detected. Reduce -j jobs or disable LTO."
            )
        if "drivers/gpu/drm/amd/amdgpu" in tail_text:
            hints.append(
                "Failure is inside amdgpu. On Debian with a newly-released "
                "kernel this often means a gcc/clang mismatch on a RAS header; "
                "switch toolchain (Clang <-> GCC), or turn off AMDGPU tweaks."
            )
        if "fs/f2fs/checkpoint.c" in tail_text and "no member named 'se'" in tail_text:
            hints.append(
                "CachyOS f2fs patch conflicts with BORE sched_entity on this "
                "kernel. v2.3+ disables F2FS_FS automatically when no f2fs "
                "mount is present — re-run on latest CKO, or manually set "
                "CONFIG_F2FS_FS=n in an extra config fragment."
            )
        if "undefined reference" in tail_text or "undefined symbol" in tail_text:
            hints.append(
                "Undefined reference at link — usually a Kconfig dependency "
                "missing. Re-run with 'defconfig' seed to get a known-good base."
            )
        if not hints:
            hints.append(
                "Re-run with 'Verbose build output' checked; the real compiler "
                "message is usually hidden by parallel make."
            )
        for h in hints:
            self.log(f"  hint: {h}\n")
        if self.log_file_path:
            self.log(f"\nFull log saved to: {self.log_file_path}\n")
        self.log("=======================================\n")
        msg = reason
        if self.log_file_path:
            msg += f"  (log: {self.log_file_path})"
        self.sig.done.emit(False, msg)

    # ---- install build dependencies (apt only) ----------------------------
    def _install_deps(self) -> None:
        self.status("Installing build dependencies via apt…")
        want_clang = self.cfg.compiler in ("auto", "clang")
        clang_pkgs = ["clang", "lld", "llvm"] if want_clang else []

        self._run(["apt-get", "update"], as_root=True, check=False)
        self._run([
            "apt-get", "install", "-y", "--no-install-recommends",
            # core toolchain
            "build-essential", "bc", "bison", "flex",
            # kernel-build libs / tools
            "libelf-dev", "libssl-dev", "libncurses-dev",
            "libdw-dev", "libdwarf-dev", "dwarves",
            "zstd", "xz-utils", "lz4", "cpio", "kmod", "rsync", "perl",
            # source fetching / patching
            "git", "wget", "patch", "ca-certificates",
            # packaging
            "fakeroot", "debhelper", "dh-python", "python3",
            "kernel-wedge",
            # ccache
            "ccache",
        ] + clang_pkgs, as_root=True)

    # ---- toolchain decision -----------------------------------------------
    def _pick_toolchain(self) -> None:
        c = self.cfg.compiler
        if c == "clang" or (c == "auto" and shutil.which("clang") and shutil.which("ld.lld")):
            self.toolchain = "clang"
        else:
            self.toolchain = "gcc"
        lto = self.cfg.lto
        if lto == "auto":
            lto = "thin" if self.toolchain == "clang" else "no"
        if self.toolchain == "gcc" and lto != "no":
            self.log("[warn] LTO requested but toolchain is gcc; disabling LTO\n")
            lto = "no"
        self.active_lto = lto
        self.log(f"[cyfare] toolchain: {self.toolchain}; LTO: {self.active_lto}\n")

    # ---- resolve latest kernel version -----------------------------------
    def _version_key(self, v: str) -> tuple:
        return tuple(int(x) for x in v.split("."))

    def _resolve_version_for_series(self, series: str) -> Optional[str]:
        major = series.split(".")[0]
        url = f"{KERNEL_ORG_BASE}/v{major}.x/"
        try:
            with urllib.request.urlopen(url, timeout=30) as r:
                index = r.read().decode(errors="replace")
        except Exception as e:
            self.log(f"[warn] cannot reach {url}: {e}\n")
            return None
        series_re = re.escape(series)
        matches = re.findall(rf"linux-({series_re}(?:\.[0-9]+)?)\.tar\.xz", index)
        if not matches:
            return None
        return max(set(matches), key=self._version_key)

    def _resolve_version(self) -> None:
        if self.cfg.kernel_version:
            self.kernel_full_version = self.cfg.kernel_version
            parts = self.kernel_full_version.split(".")
            self.effective_series = ".".join(parts[:2])
            return
        self.log(f"[cyfare] resolving latest stable {self.cfg.kernel_series}.x from kernel.org…\n")
        v = self._resolve_version_for_series(self.cfg.kernel_series)
        if not v:
            raise RuntimeError(f"no {self.cfg.kernel_series}.x release found at kernel.org")
        self.kernel_full_version = v
        self.effective_series = self.cfg.kernel_series
        self.log(f"[cyfare] selected kernel {self.kernel_full_version}\n")

    # ---- download sources -------------------------------------------------
    def _fetch_sources_for(self, version: str) -> Path:
        major = version.split(".")[0]
        self.cfg.workdir.mkdir(parents=True, exist_ok=True)
        tarball = self.cfg.workdir / f"linux-{version}.tar.xz"
        if not tarball.exists() or tarball.stat().st_size == 0:
            self.status(f"Downloading linux-{version}.tar.xz…")
            url = f"{KERNEL_ORG_BASE}/v{major}.x/{tarball.name}"
            ok, _ = self._http_get(url, tarball)
            if not ok:
                raise RuntimeError(f"failed to download {url}")
        else:
            self.log(f"[cyfare] {tarball.name} already present\n")

        src = self.cfg.workdir / f"linux-{version}"
        if not src.exists():
            self.status("Extracting kernel source…")
            self._run(["tar", "-xf", str(tarball)], cwd=self.cfg.workdir)
        return src

    # ---- patch discovery --------------------------------------------------
    def _cachyos_patch_urls(self, series: str) -> list[tuple[str, str]]:
        urls: list[tuple[str, str]] = []
        # 1. Combined base patch — one file that carries most of the goodies
        urls.append(("all",
                     f"{CACHYOS_RAW}/{series}/all/0001-cachyos-base-all.patch"))
        # 2. Directory listings via GitHub API
        for subdir in ("all", "", "sched", "misc"):
            api_path = f"{CACHYOS_API}/{series}" + (f"/{subdir}" if subdir else "")
            for entry in self._github_listdir(api_path):
                if entry.get("type") != "file":
                    continue
                name = entry.get("name", "")
                if not name.endswith(".patch"):
                    continue
                if name == "0001-cachyos-base-all.patch":
                    continue
                dl = entry.get("download_url")
                if dl:
                    urls.append((subdir or "root", dl))
        # dedupe
        seen = set(); out = []
        for cat, u in urls:
            if u in seen: continue
            seen.add(u); out.append((cat, u))
        return out

    def _bore_upstream_patch(self, series: str) -> Optional[str]:
        listing = self._github_listdir(f"{BORE_API}/patches/stable")
        if not listing:
            listing = self._github_listdir(f"{BORE_API}/patches")

        def dir_series(name: str) -> Optional[str]:
            m = re.search(r"linux[-_]?(\d+\.\d+)", name)
            return m.group(1) if m else None

        candidates: list[tuple[str, str]] = []
        for entry in listing:
            if entry.get("type") != "dir":
                continue
            n = entry.get("name", "")
            s = dir_series(n)
            if s:
                candidates.append((s, entry.get("url", "")))
        try:
            wanted = self._version_key(series)
        except ValueError:
            return None
        exact = [u for s, u in candidates if s == series]
        older = sorted(
            [(s, u) for s, u in candidates
             if self._version_key(s) <= wanted],
            key=lambda t: self._version_key(t[0]), reverse=True,
        )
        picks = exact + [u for _, u in older]
        for url in picks:
            files = self._github_listdir(url)
            for f in files:
                if f.get("type") == "file" and f.get("name", "").endswith(".patch"):
                    return f.get("download_url")
        return None

    def _fetch_patches_for_series(self, series: str) -> list[Path]:
        pdir = self.cfg.workdir / "patches" / series
        pdir.mkdir(parents=True, exist_ok=True)
        fetched: list[Path] = []
        self.status(f"Discovering CachyOS patches for {series}…")
        for cat, url in self._cachyos_patch_urls(series):
            fn = pdir / f"{cat}__{Path(url).name}"
            if fn.exists() and fn.stat().st_size > 0:
                self.log(f"  cached: {fn.name}\n")
                fetched.append(fn); continue
            ok, _ = self._http_get(url, fn)
            if ok and fn.stat().st_size > 0:
                fetched.append(fn)
            else:
                fn.unlink(missing_ok=True)
        self.status(f"Looking for upstream BORE patch matching {series}…")
        bore_url = self._bore_upstream_patch(series)
        if bore_url:
            fn = pdir / f"bore__{Path(bore_url).name}"
            if not (fn.exists() and fn.stat().st_size > 0):
                ok, _ = self._http_get(bore_url, fn)
                if not (ok and fn.stat().st_size > 0):
                    fn.unlink(missing_ok=True); fn = None  # type: ignore
            if fn and fn.exists():
                fetched.append(fn)
        else:
            self.log("[cyfare] no upstream BORE patch directory matched\n")
        return fetched

    def _fetch_sources_and_patches(self) -> tuple[Path, list[Path]]:
        wanted = self.effective_series
        tried: list[str] = []
        walk = [wanted]
        if self.cfg.auto_fallback_series and not self.cfg.kernel_version:
            try:
                wk = self._version_key(wanted)
                walk += [s for s in SUPPORTED_SERIES_ORDER
                         if s != wanted and self._version_key(s) <= wk]
            except ValueError:
                pass

        chosen_series: Optional[str] = None
        chosen_patches: list[Path] = []
        if self.cfg.patches:
            for s in walk:
                tried.append(s)
                patches = self._fetch_patches_for_series(s)
                if patches:
                    chosen_series = s
                    chosen_patches = patches
                    break
                self.log(f"[cyfare] no patches found for series {s}\n")
        else:
            chosen_series = wanted

        if chosen_series is None:
            self.log(f"[warn] no patches found anywhere (tried {tried}); "
                     f"building vanilla {wanted}\n")
            chosen_series = wanted

        if chosen_series != self.effective_series:
            self.log(f"[cyfare] switching from {self.effective_series} -> "
                     f"{chosen_series} to align with available patches\n")
            v = self._resolve_version_for_series(chosen_series)
            if not v:
                raise RuntimeError(f"cannot resolve latest {chosen_series}.x")
            self.kernel_full_version = v
            self.effective_series = chosen_series
            self.log(f"[cyfare] selected kernel {self.kernel_full_version}\n")

        src = self._fetch_sources_for(self.kernel_full_version)
        return src, chosen_patches

    # ---- apply patches ----------------------------------------------------
    def _apply_patches(self, src: Path, patches: list[Path]) -> None:
        def order_key(p: Path) -> tuple:
            n = p.name.lower()
            score = 50
            if "cachyos-base-all" in n: score = 0
            elif "cachy" in n and "bore" not in n: score = 10
            elif "fixes" in n: score = 20
            elif "bbr" in n: score = 25
            elif "amd" in n or "hdmi" in n or "t2" in n: score = 30
            elif "vmscape" in n or "vesa" in n: score = 35
            elif "sched-ext" in n: score = 40
            elif "bore" in n: score = 90
            return (score, n)

        patches_sorted = sorted(patches, key=order_key)
        for p in patches_sorted:
            self.status(f"Applying {p.name}…")
            self.log(f"[cyfare] applying {p.name}\n")
            dry = subprocess.run(
                ["patch", "-p1", "--dry-run", "--forward",
                 "-l", "--fuzz=3", "--no-backup-if-mismatch", "-i", str(p)],
                cwd=str(src), capture_output=True, text=True,
            )
            if dry.returncode != 0:
                self.log(dry.stdout); self.log(dry.stderr or "")
                self.log(f"[warn] {p.name} does not apply (fuzz=3); skipping\n")
                self.failed_patches.append(p.name)
                continue
            try:
                self._run(["patch", "-p1", "--forward",
                           "-l", "--fuzz=3", "--no-backup-if-mismatch",
                           "-i", str(p)], cwd=src)
                self.applied_patches.append(p.name)
            except RuntimeError as e:
                self.log(f"[warn] {p.name} failed during apply: {e}\n")
                self.failed_patches.append(p.name)

        self.log(f"\n[cyfare] applied {len(self.applied_patches)} patch(es), "
                 f"failed {len(self.failed_patches)}\n")
        for n in self.applied_patches: self.log(f"  + {n}\n")
        for n in self.failed_patches:  self.log(f"  - {n}\n")

    # ---- configure --------------------------------------------------------
    def _has_f2fs_mount(self) -> bool:
        """True iff an f2fs filesystem is currently mounted."""
        try:
            mounts = _read_text("/proc/mounts")
            for line in mounts.splitlines():
                parts = line.split()
                if len(parts) >= 3 and parts[2] == "f2fs":
                    return True
        except Exception:
            pass
        return False

    def _seed_config(self, src: Path) -> None:
        mode = self.cfg.config_mode
        dot = src / ".config"
        running = Path(f"/boot/config-{os.uname().release}")
        proc_cfg = Path("/proc/config.gz")

        def from_file(p: Path) -> None:
            shutil.copy2(p, dot)
            self.log(f"[cyfare] seeded .config from {p}\n")

        if mode == "auto":
            if running.exists():
                from_file(running)
            elif proc_cfg.exists():
                self._run(["sh", "-c", f"zcat {proc_cfg} > {dot}"], cwd=src)
            else:
                self._run(["make", *self._kconfig_env(), "defconfig"], cwd=src)
        elif mode == "running":
            if running.exists():
                from_file(running)
            elif proc_cfg.exists():
                self._run(["sh", "-c", f"zcat {proc_cfg} > {dot}"], cwd=src)
            else:
                raise RuntimeError("no running-kernel config available")
        elif mode == "localmod":
            self._run(["make", *self._kconfig_env(), "defconfig"], cwd=src)
            self._run(["make", *self._kconfig_env(), "localmodconfig"],
                      cwd=src, stdin_bytes=b"")
        elif mode == "defconfig":
            self._run(["make", *self._kconfig_env(), "defconfig"], cwd=src)
        elif mode == "file":
            if not self.cfg.config_file or not Path(self.cfg.config_file).exists():
                raise RuntimeError("config_mode=file but config_file missing")
            from_file(Path(self.cfg.config_file))
        else:
            raise RuntimeError(f"unknown config_mode: {mode}")

        self._make_olddefconfig(src)

    def _tune_config(self, src: Path) -> None:
        self.status("Tuning .config for BORE + performance…")
        cfg_path = src / ".config"
        sc = "./scripts/config"

        def scfg(*args: str) -> None:
            subprocess.run([sc, *args], cwd=str(src),
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

        # identity
        scfg("--set-str", "LOCALVERSION", self.cfg.local_version)
        scfg("--disable", "LOCALVERSION_AUTO")

        # BORE + sched_ext
        scfg("--enable", "SCHED_BORE")
        scfg("--enable", "SCHED_CLASS_EXT")

        # preemption
        for k in ("PREEMPT_NONE", "PREEMPT_VOLUNTARY", "PREEMPT", "PREEMPT_RT",
                  "PREEMPT_DYNAMIC"):
            scfg("--disable", k)
        scfg("--enable",
             {"none": "PREEMPT_NONE", "voluntary": "PREEMPT_VOLUNTARY",
              "full": "PREEMPT", "rt": "PREEMPT_RT"}[self.cfg.preempt])

        # HZ
        for h in ("100", "250", "300", "500", "600", "750", "1000"):
            scfg("--disable", f"HZ_{h}")
        scfg("--enable", f"HZ_{self.cfg.hz}")
        scfg("--set-val", "HZ", self.cfg.hz)

        # tick
        for k in ("HZ_PERIODIC", "NO_HZ_IDLE", "NO_HZ_FULL", "NO_HZ"):
            scfg("--disable", k)
        scfg("--enable",
             {"periodic": "HZ_PERIODIC", "idle": "NO_HZ_IDLE",
              "full": "NO_HZ_FULL"}[self.cfg.tick])
        if self.cfg.tick in ("idle", "full"):
            scfg("--enable", "NO_HZ")
            scfg("--enable", "NO_HZ_COMMON")

        # march (x86-64 levels; only valid with CachyOS patches applied)
        if os.uname().machine == "x86_64":
            for k in ("GENERIC_CPU", "GENERIC_CPU2", "GENERIC_CPU3",
                      "GENERIC_CPU4", "MK8", "MPSC", "MATOM", "MCORE2",
                      "MNATIVE_INTEL", "MNATIVE_AMD"):
                scfg("--disable", k)
            m = self.cfg.march
            if m == "auto":
                m = self.sp.isa_level
                if m == "x86-64":
                    m = "generic"
            if m == "generic":
                scfg("--enable", "GENERIC_CPU")
            elif m == "x86-64-v2":
                scfg("--enable", "GENERIC_CPU2")
            elif m == "x86-64-v3":
                scfg("--enable", "GENERIC_CPU3")
            elif m == "x86-64-v4":
                scfg("--enable", "GENERIC_CPU4")
            elif m == "native":
                if self.sp.cpu_vendor == "amd":
                    scfg("--enable", "MNATIVE_AMD")
                else:
                    scfg("--enable", "MNATIVE_INTEL")

        # -O level (O3 is CachyOS-patch only)
        if self.cfg.o_level == "3":
            scfg("--enable", "CC_OPTIMIZE_FOR_PERFORMANCE_O3")
            scfg("--disable", "CC_OPTIMIZE_FOR_PERFORMANCE")
        else:
            scfg("--enable", "CC_OPTIMIZE_FOR_PERFORMANCE")
            scfg("--disable", "CC_OPTIMIZE_FOR_PERFORMANCE_O3")

        # LTO (clang only)
        if self.toolchain == "clang":
            for k in ("LTO_NONE", "LTO_CLANG_THIN", "LTO_CLANG_FULL"):
                scfg("--disable", k)
            if self.active_lto == "thin":
                scfg("--enable", "LTO_CLANG_THIN")
            elif self.active_lto == "full":
                scfg("--enable", "LTO_CLANG_FULL")
            else:
                scfg("--enable", "LTO_NONE")
        else:
            scfg("--enable", "LTO_NONE")

        # Sensible perf defaults
        scfg("--enable", "TRANSPARENT_HUGEPAGE")
        scfg("--enable", "TRANSPARENT_HUGEPAGE_MADVISE")
        scfg("--disable", "TRANSPARENT_HUGEPAGE_ALWAYS")
        scfg("--enable", "ZSWAP")
        scfg("--enable", "ZSWAP_DEFAULT_ON")
        scfg("--enable", "ZSWAP_COMPRESSOR_DEFAULT_ZSTD")
        scfg("--set-str", "ZSWAP_COMPRESSOR_DEFAULT", "zstd")
        scfg("--enable", "ZSWAP_ZPOOL_DEFAULT_ZSMALLOC")
        scfg("--set-str", "ZSWAP_ZPOOL_DEFAULT", "zsmalloc")
        scfg("--enable", "LRU_GEN"); scfg("--enable", "LRU_GEN_ENABLED")
        scfg("--enable", "TCP_CONG_BBR"); scfg("--set-str", "DEFAULT_TCP_CONG", "bbr")
        scfg("--enable", "TCP_CONG_CUBIC")

        # Storage tuning
        if self.sp.root_is_nvme or self.sp.root_is_ssd:
            # mq-deadline is already default; make sure BFQ is available
            scfg("--enable", "IOSCHED_BFQ")
            scfg("--enable", "MQ_IOSCHED_KYBER")
            scfg("--enable", "MQ_IOSCHED_DEADLINE")

        # GPU-specific
        if self.cfg.amdgpu_tweaks or self.sp.has_amdgpu:
            scfg("--enable", "DRM_AMDGPU")
            scfg("--enable", "DRM_AMDGPU_SI")
            scfg("--enable", "DRM_AMDGPU_CIK")
            scfg("--enable", "DRM_AMDGPU_USERPTR")
        if self.cfg.nvidia_tweaks or self.sp.has_nvidia:
            # Leave NVIDIA proprietary driver out-of-tree, but keep
            # nouveau *off* to avoid conflicts with the proprietary driver.
            scfg("--module-after", "DRM", "DRM_NOUVEAU")
            scfg("--disable", "DRM_NOUVEAU")
        if self.sp.has_intel_gpu:
            scfg("--enable", "DRM_I915")
            scfg("--enable", "DRM_I915_FORCE_PROBE")

        # Slim build: strip debug, drop cert requirements (so we don't need a key)
        scfg("--disable", "DEBUG_INFO")
        scfg("--disable", "DEBUG_INFO_DWARF4")
        scfg("--disable", "DEBUG_INFO_DWARF5")
        scfg("--disable", "DEBUG_INFO_BTF")
        scfg("--enable",  "DEBUG_INFO_NONE")
        scfg("--set-str", "SYSTEM_TRUSTED_KEYS", "")
        scfg("--set-str", "SYSTEM_REVOCATION_KEYS", "")
        scfg("--disable", "MODULE_SIG_ALL")
        scfg("--disable", "MODULE_SIG_FORCE")

        # F2FS: the CachyOS f2fs performance patch accesses
        # `current->se.sum_exec_runtime` which conflicts with BORE's
        # sched_entity layout on some kernel versions, producing:
        #   fs/f2fs/checkpoint.c:31: error: no member named 'se' in
        #   'struct task_struct'
        # Unless the user actually has an f2fs mount, turn it off to
        # dodge the incompatibility. F2FS is primarily for flash cards
        # and Android; desktop Debian users almost never use it.
        if self._has_f2fs_mount():
            self.log("[cyfare] f2fs filesystem detected in /proc/mounts — "
                     "keeping F2FS enabled (may fail to build if CachyOS "
                     "f2fs patch clashes with BORE)\n")
        else:
            self.log("[cyfare] no f2fs mount detected — disabling F2FS_FS "
                     "to avoid CachyOS f2fs patch / BORE sched_entity clash\n")
            scfg("--disable", "F2FS_FS")
            scfg("--disable", "F2FS_STAT_FS")
            scfg("--disable", "F2FS_FS_XATTR")
            scfg("--disable", "F2FS_FS_POSIX_ACL")
            scfg("--disable", "F2FS_FS_SECURITY")
            scfg("--disable", "F2FS_CHECK_FS")
            scfg("--disable", "F2FS_FAULT_INJECTION")
            scfg("--disable", "F2FS_FS_COMPRESSION")
            scfg("--disable", "F2FS_IOSTAT")
            scfg("--disable", "F2FS_UNFAIR_RWSEM")

        # Android binder was causing 'm' warnings on the seed config
        scfg("--disable", "ANDROID_BINDER_IPC")
        scfg("--disable", "BOOTPARAM_SOFTLOCKUP_PANIC")

        # CachyOS convenience symbol (present only if cachy.patch applied)
        scfg("--enable", "CACHY")

        # Extra user fragment
        if self.cfg.extra_config and Path(self.cfg.extra_config).exists():
            with cfg_path.open("a") as out:
                out.write("\n# --- user extra fragment ---\n")
                out.write(Path(self.cfg.extra_config).read_text())
            self.log(f"[cyfare] merged extra fragment: {self.cfg.extra_config}\n")

        # Reconcile and pre-sync with the SAME toolchain as the compile step
        self._make_olddefconfig(src)
        self._run(["make", *self._kconfig_env(), "syncconfig"], cwd=src, check=False)

        # Verify BORE actually made it in
        try:
            conf = cfg_path.read_text(errors="replace")
            self.bore_in_tree = ("\nCONFIG_SCHED_BORE=y" in conf) or conf.startswith("CONFIG_SCHED_BORE=y")
        except OSError:
            self.bore_in_tree = False

        if not self.bore_in_tree:
            self.log("[warn] CONFIG_SCHED_BORE is NOT set in .config — BORE patch likely didn't apply; "
                     "build will be vanilla EEVDF.\n")
        else:
            self.log("[cyfare] verified CONFIG_SCHED_BORE=y in .config\n")

    # ---- compile ----------------------------------------------------------
    def _compile(self, src: Path) -> None:
        self.status(f"Compiling kernel ({self.cfg.jobs} jobs, {self.toolchain})…")
        env = os.environ.copy()
        kcflags = "-pipe"
        if self.cfg.o_level == "3":
            kcflags += " -O3"
        env["KCFLAGS"] = kcflags

        # --output-sync=line keeps each parallel recipe's output contiguous
        # so a failing job's error message isn't interleaved with (and
        # silently dropped by) 20 other jobs' output. This is the single
        # most important flag for diagnosing parallel kbuild failures.
        base = ["make", "--output-sync=line", f"-j{self.cfg.jobs}"]
        if self.toolchain == "clang":
            base += ["LLVM=1"]
        if self.cfg.verbose:
            base += ["V=1"]
        argv = base + ["all"]
        try:
            self._run(argv, cwd=src, env=env)
        except RuntimeError as e:
            # Parallel build failed. Retry serially with V=1 to surface the
            # real compiler/linker error. This is slow but only runs on
            # failure, and the output ends up in the log file.
            self.log("\n[cyfare] parallel build failed; "
                     "retrying with -j1 V=1 to locate the real error…\n")
            retry = ["make", "-j1", "V=1"]
            if self.toolchain == "clang":
                retry += ["LLVM=1"]
            retry += ["all"]
            self._run(retry, cwd=src, env=env)
            # If the serial retry somehow succeeds (rare — flaky race),
            # we're done. Otherwise _run() raises and propagates.
            self.log("[cyfare] serial retry succeeded; parallel failure "
                     "was a race. Consider lowering -j.\n")

    # ---- package (Debian .deb only) ---------------------------------------
    def _package(self, src: Path) -> None:
        if self.cfg.build_only:
            self.log("[cyfare] --build-only: skipping packaging\n")
            return
        self.cfg.outdir.mkdir(parents=True, exist_ok=True)
        self.status("Packaging kernel as .deb…")
        mk = ["make", "--output-sync=line", f"-j{self.cfg.jobs}"]
        if self.toolchain == "clang":
            mk += ["LLVM=1"]
        if self.cfg.verbose:
            mk += ["V=1"]

        try:
            self._run(mk + [
                "bindeb-pkg",
                f"LOCALVERSION={self.cfg.local_version}",
                f"KDEB_PKGVERSION={self.kernel_full_version}-cyfare-1",
            ], cwd=src)
            # .deb files land in src.parent
            for f in src.parent.glob("linux-*.deb"):
                shutil.move(str(f), str(self.cfg.outdir / f.name))
            # any .buildinfo / .changes alongside
            for ext in ("buildinfo", "changes", "ddeb"):
                for f in src.parent.glob(f"linux-*.{ext}"):
                    shutil.move(str(f), str(self.cfg.outdir / f.name))
        except RuntimeError as e:
            self.log(f"[warn] bindeb-pkg failed ({e}); producing tarball instead\n")
            self._run(mk + ["tarxz-pkg", f"LOCALVERSION={self.cfg.local_version}"],
                      cwd=src)
            for f in src.glob("linux-*.tar.xz"):
                shutil.move(str(f), str(self.cfg.outdir / f.name))

        self.log(f"[cyfare] artifacts in: {self.cfg.outdir}\n")
        for art in sorted(self.cfg.outdir.iterdir()):
            self.log(f"  {art.name}\n")

    # ---- top-level build --------------------------------------------------
    def _do_build(self) -> None:
        self.sig.progress.emit(-1, -1)
        self._install_deps()
        self._pick_toolchain()
        self._resolve_version()
        src, patches = self._fetch_sources_and_patches()
        if self.cfg.download_only:
            self.log("[cyfare] --download-only: stopping here\n")
            return
        if patches:
            self._apply_patches(src, patches)
        else:
            self.log("[cyfare] no patches to apply; building vanilla\n")
        self._seed_config(src)
        self._tune_config(src)
        self._compile(src)
        self._package(src)

        self.log("\n============= BUILD SUMMARY =============\n")
        self.log(f"Kernel         : {self.kernel_full_version}{self.cfg.local_version}\n")
        self.log(f"Series used    : {self.effective_series}"
                 f"{' (auto-fallback)' if self.effective_series != self.cfg.kernel_series else ''}\n")
        self.log(f"Toolchain      : {self.toolchain}  LTO: {self.active_lto}\n")
        self.log(f"march / -O     : {self.cfg.march} / -O{self.cfg.o_level}\n")
        self.log(f"Patches        : {len(self.applied_patches)} applied, "
                 f"{len(self.failed_patches)} failed\n")
        self.log(f"BORE scheduler : "
                 f"{'YES (CONFIG_SCHED_BORE=y)' if self.bore_in_tree else 'NO (vanilla EEVDF)'}\n")
        self.log("=========================================\n")

    # ---- install (Debian .deb only) ---------------------------------------
    def _do_install(self) -> None:
        out = self.cfg.outdir
        if not out.exists() or not any(out.iterdir()):
            raise RuntimeError(f"no artifacts in {out}; run Build first")
        self.status("Installing .deb kernel packages via apt…")
        debs = sorted(out.glob("linux-*.deb"))
        if not debs:
            raise RuntimeError("no .deb files found in outdir")
        # Prefer `apt install ./pkg.deb` — it resolves dependencies.
        deb_args = [str(d) for d in debs]
        self._run(["apt-get", "install", "-y", "--no-install-recommends", *deb_args],
                  as_root=True, check=False)
        # Fallback to dpkg -i if apt route failed
        self._run(["dpkg", "-i", *deb_args], as_root=True, check=False)
        self._run(["apt-get", "install", "-f", "-y"], as_root=True, check=False)
        self._refresh_boot()

    def _refresh_boot(self) -> None:
        kver = f"{self.kernel_full_version}{self.cfg.local_version}"
        # Debian's linux-image .deb already regenerates initramfs and updates grub
        # via its postinst hooks, but invoke the tools explicitly as a safety net.
        if shutil.which("update-initramfs"):
            self._run(["update-initramfs", "-u", "-k", kver],
                      as_root=True, check=False)
        if shutil.which("update-grub"):
            self._run(["update-grub"], as_root=True, check=False)
        elif shutil.which("grub-mkconfig"):
            self._run(["grub-mkconfig", "-o", "/boot/grub/grub.cfg"],
                      as_root=True, check=False)
        if self.sp.uses_systemd_boot and shutil.which("bootctl"):
            self._run(["bootctl", "update"], as_root=True, check=False)

    # ---- clean ------------------------------------------------------------
    def _do_clean(self) -> None:
        self.status("Cleaning workdir…")
        if self.cfg.workdir.exists():
            shutil.rmtree(self.cfg.workdir)
            self.log(f"[cyfare] removed {self.cfg.workdir}\n")


# =============================================================================
# GUI
# =============================================================================

DARK_QSS = """
* { font-family: "Inter", "Segoe UI", "Helvetica Neue", sans-serif; font-size: 10.5pt; }
QMainWindow, QWidget { background: #16181d; color: #e6e8ee; }
QGroupBox {
    border: 1px solid #2a2e38; border-radius: 10px;
    margin-top: 14px; padding: 12px;
    background: #1b1e25;
}
QGroupBox::title {
    subcontrol-origin: margin; left: 14px; padding: 0 6px;
    color: #8aa8ff; font-weight: 600;
}
QLabel { color: #c8ccd6; }
QLineEdit, QComboBox, QSpinBox, QPlainTextEdit {
    background: #12141a; border: 1px solid #2a2e38; border-radius: 6px;
    padding: 6px 8px; color: #e6e8ee; selection-background-color: #3b82f6;
}
QLineEdit:focus, QComboBox:focus, QSpinBox:focus, QPlainTextEdit:focus {
    border: 1px solid #3b82f6;
}
QComboBox::drop-down { border: none; width: 22px; }
QCheckBox { spacing: 8px; }
QCheckBox::indicator {
    width: 16px; height: 16px; border-radius: 4px;
    border: 1px solid #3a3f4b; background: #12141a;
}
QCheckBox::indicator:checked {
    background: #3b82f6; border: 1px solid #3b82f6;
}
QPushButton {
    background: #252a35; border: 1px solid #2f3542; border-radius: 8px;
    padding: 8px 16px; color: #e6e8ee; font-weight: 500;
}
QPushButton:hover { background: #2e3340; border-color: #3b82f6; }
QPushButton:pressed { background: #1d2029; }
QPushButton#primary {
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #3b82f6, stop:1 #6366f1);
    border: none; color: white; font-weight: 600;
}
QPushButton#primary:hover {
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #4f8ff7, stop:1 #7c73f2);
}
QPushButton#accent {
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #10b981, stop:1 #22d3ee);
    border: none; color: white; font-weight: 600;
}
QPushButton#accent:hover {
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #22c497, stop:1 #38dff1);
}
QPushButton#danger { background: #b43a3a; border: none; color: white; }
QPushButton#danger:hover  { background: #c84848; }
QPushButton:disabled { background: #1d2029; color: #5a616e; border-color: #2a2e38; }
QTabWidget::pane { border: 1px solid #2a2e38; border-radius: 10px; background: #1b1e25; top: -1px; }
QTabBar::tab {
    background: transparent; color: #9aa1ae; padding: 9px 18px;
    border-top-left-radius: 8px; border-top-right-radius: 8px;
}
QTabBar::tab:selected { background: #1b1e25; color: #e6e8ee; border: 1px solid #2a2e38; border-bottom: none; }
QTabBar::tab:hover:!selected { color: #d0d4de; }
QPlainTextEdit#log {
    background: #0c0d11; color: #cfd3dd; font-family: "JetBrains Mono","Menlo","Consolas",monospace;
    font-size: 9.5pt; border: 1px solid #23262e;
}
QStatusBar { background: #12141a; color: #9aa1ae; }
QProgressBar { background: #12141a; border: 1px solid #2a2e38; border-radius: 6px; text-align: center; color: #e6e8ee; }
QProgressBar::chunk {
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #3b82f6, stop:1 #22d3ee);
    border-radius: 5px;
}
QLabel#hint { color: #7a8196; font-size: 9pt; }
QLabel#h1   { color: #e6e8ee; font-size: 18pt; font-weight: 700; }
QLabel#specs { color: #a7b0c2; font-family: "JetBrains Mono","Menlo","Consolas",monospace; font-size: 9.5pt; }
QDialog     { background: #1b1e25; }
"""


class KernelBuilder(QMainWindow):
    def __init__(self) -> None:
        super().__init__()
        self.setWindowTitle(APP_NAME)
        self.resize(1120, 860)
        self.setMinimumSize(QSize(1000, 700))
        self.priv = Privileged()
        self.worker: Optional[BuildWorker] = None
        self.sp = detect_system()
        self._build_ui()
        self._apply_smart_defaults()   # aggressive defaults on first launch

    # -- layout -------------------------------------------------------------
    def _build_ui(self) -> None:
        central = QWidget()
        root = QVBoxLayout(central)
        root.setContentsMargins(16, 16, 16, 12)
        root.setSpacing(12)

        # Header
        header = QHBoxLayout()
        title = QLabel("CYFARE Kernel Optimize")
        title.setObjectName("h1")
        subtitle = QLabel("V2.0 · Debian-only · BORE + CachyOS · Smart defaults")
        subtitle.setObjectName("hint")
        hcol = QVBoxLayout(); hcol.addWidget(title); hcol.addWidget(subtitle)
        header.addLayout(hcol); header.addStretch()
        env_lbl = QLabel(f"distro: <b>{self.sp.distro_id or '?'}</b>  ·  "
                         f"apt: <b>{'ok' if shutil.which('apt-get') else 'missing'}</b>")
        env_lbl.setObjectName("hint")
        header.addWidget(env_lbl)
        root.addLayout(header)

        # System specs panel
        specs_group = QGroupBox("Detected hardware")
        sg = QHBoxLayout(specs_group)
        self.specs_lbl = QLabel(describe_system(self.sp))
        self.specs_lbl.setObjectName("specs")
        self.specs_lbl.setWordWrap(True)
        sg.addWidget(self.specs_lbl, 1)
        smart_btn = QPushButton("Apply Smart Defaults")
        smart_btn.setObjectName("accent")
        smart_btn.clicked.connect(self._apply_smart_defaults)
        sg.addWidget(smart_btn, 0, Qt.AlignmentFlag.AlignTop)
        root.addWidget(specs_group)

        self.tabs = QTabWidget()
        self.tabs.addTab(self._tab_source(),   "  Source  ")
        self.tabs.addTab(self._tab_cpu(),      "  CPU & Arch  ")
        self.tabs.addTab(self._tab_sched(),    "  Scheduler & Timing  ")
        self.tabs.addTab(self._tab_tool(),     "  Toolchain  ")
        self.tabs.addTab(self._tab_advanced(), "  Advanced  ")
        root.addWidget(self.tabs, 1)

        actions = QHBoxLayout()
        self.btn_preview = QPushButton("Preview config")
        self.btn_preview.clicked.connect(self._preview)
        self.btn_build = QPushButton("Build")
        self.btn_build.setObjectName("primary")
        self.btn_build.clicked.connect(lambda: self._start(["build"]))
        self.btn_bi = QPushButton("Build && Install")
        self.btn_bi.setObjectName("primary")
        self.btn_bi.clicked.connect(lambda: self._start(["build", "install"]))
        self.btn_install = QPushButton("Install only")
        self.btn_install.clicked.connect(lambda: self._start(["install"]))
        self.btn_clean = QPushButton("Clean")
        self.btn_clean.clicked.connect(lambda: self._start(["clean"]))
        self.btn_stop = QPushButton("Stop")
        self.btn_stop.setObjectName("danger"); self.btn_stop.setEnabled(False)
        self.btn_stop.clicked.connect(self._stop)
        for b in (self.btn_preview, self.btn_build, self.btn_bi,
                  self.btn_install, self.btn_clean):
            actions.addWidget(b)
        actions.addStretch(); actions.addWidget(self.btn_stop)
        root.addLayout(actions)

        log_lbl = QLabel("Build log"); log_lbl.setObjectName("hint")
        root.addWidget(log_lbl)
        self.log = QPlainTextEdit(); self.log.setObjectName("log")
        self.log.setReadOnly(True); self.log.setMinimumHeight(240)
        root.addWidget(self.log, 1)

        self.progress = QProgressBar()
        self.progress.setFixedWidth(240); self.progress.setRange(0, 0)
        self.progress.setVisible(False)
        sb = QStatusBar()
        self.status_lbl = QLabel("Ready")
        sb.addWidget(self.status_lbl)
        sb.addPermanentWidget(self.progress)
        self.setStatusBar(sb)
        self.setCentralWidget(central)

        if not self.sp.is_debian_family:
            QMessageBox.critical(
                self, APP_NAME,
                "This tool is Debian/Ubuntu only. "
                "apt-get + dpkg are required.\n\n"
                "If you believe this is wrong (e.g. derivative distro), ensure "
                "/etc/os-release sets ID_LIKE to include 'debian' or 'ubuntu'."
            )

    # -- tabs ---------------------------------------------------------------
    def _tab_source(self) -> QWidget:
        w = QWidget(); v = QVBoxLayout(w)
        g = QGroupBox("Kernel"); f = QFormLayout(g)
        self.kernel_series = QLineEdit("7.0")
        self.kernel_version = QLineEdit()
        self.kernel_version.setPlaceholderText("(empty = auto-detect latest .x)")
        self.local_version = QLineEdit("-cyfare")
        f.addRow("Kernel series:", self.kernel_series)
        f.addRow("Exact version:", self.kernel_version)
        f.addRow("Local version suffix:", self.local_version)

        g2 = QGroupBox("Patches"); gv = QVBoxLayout(g2)
        self.patches_on = QCheckBox("Apply CachyOS patchset + upstream BORE fallback")
        self.patches_on.setChecked(True)
        self.auto_fallback = QCheckBox(
            "Auto-fallback to an older series (e.g. 6.19) if no patches exist "
            "for the chosen series yet — kernel source is re-downloaded to match"
        )
        self.auto_fallback.setChecked(True)
        hint = QLabel(
            "Tries the combined <i>0001-cachyos-base-all.patch</i> first, then "
            "every individual patch in <code>all/</code>, <code>sched/</code>, "
            "<code>misc/</code>. If CachyOS doesn't ship a BORE patch for the "
            "selected series, pulls one directly from "
            "<code>firelzrd/bore-scheduler</code>. Patches are applied with "
            "fuzz=3 tolerance and listed in the build log."
        )
        hint.setWordWrap(True); hint.setObjectName("hint")
        gv.addWidget(self.patches_on)
        gv.addWidget(self.auto_fallback)
        gv.addWidget(hint)

        g3 = QGroupBox("Directories"); gf = QFormLayout(g3)
        self.workdir = QLineEdit(str(Path.home() / "cyfare-build"))
        self.outdir = QLineEdit(str(Path.home() / "cyfare-out"))
        gf.addRow("Build directory:", self.workdir)
        gf.addRow("Output directory:", self.outdir)

        v.addWidget(g); v.addWidget(g2); v.addWidget(g3); v.addStretch(1)
        return w

    def _tab_cpu(self) -> QWidget:
        w = QWidget(); v = QVBoxLayout(w)
        g = QGroupBox("Target CPU micro-architecture"); gv = QVBoxLayout(g)
        self.march = QComboBox()
        self.march.addItem(f"Auto — detected: {self.sp.isa_level}",                 "auto")
        self.march.addItem("generic — any x86-64 CPU (portable, shareable)",        "generic")
        self.march.addItem("x86-64-v2 — Nehalem+ (2008+)",                          "x86-64-v2")
        self.march.addItem("x86-64-v3 — Haswell/Excavator+ (AVX2, 2013+)",          "x86-64-v3")
        self.march.addItem("x86-64-v4 — AVX-512 CPUs",                              "x86-64-v4")
        self.march.addItem("native — THIS machine only (fastest, unshareable)",     "native")
        gv.addWidget(self.march)
        note = QLabel(
            "<b>Auto</b> picks the highest x86-64-vN level your CPU's flags support, "
            "giving you near-native performance while the binary remains runnable on "
            "any compatible CPU.<br>"
            "<b>native</b> targets ONLY the CPU in this box — fastest, but won't boot on "
            "other CPUs."
        )
        note.setWordWrap(True); note.setObjectName("hint")
        gv.addWidget(note)

        g2 = QGroupBox("Compiler optimisation level"); gh = QHBoxLayout(g2)
        self.o_level = QComboBox(); self.o_level.addItems(["2", "3"])
        gh.addWidget(QLabel("Kernel -O level:")); gh.addWidget(self.o_level); gh.addStretch(1)
        hint = QLabel("<b>-O2</b> upstream default · <b>-O3</b> more aggressive (requires CachyOS patchset).")
        hint.setObjectName("hint")
        v.addWidget(g); v.addWidget(g2); v.addWidget(hint); v.addStretch(1)
        return w

    def _tab_sched(self) -> QWidget:
        w = QWidget(); v = QVBoxLayout(w)
        g = QGroupBox("Scheduler"); gf = QFormLayout(g)
        self.sched_bore = QCheckBox("BORE (Burst-Oriented Response Enhancer) — recommended")
        self.sched_bore.setChecked(True)
        gf.addRow(self.sched_bore)
        hint = QLabel("BORE greatly improves desktop/gaming responsiveness. Requires a BORE patch.")
        hint.setObjectName("hint"); gf.addRow(hint)

        g2 = QGroupBox("Preemption"); g2v = QVBoxLayout(g2)
        self.preempt = QComboBox()
        for label, val in [("Full preemption — lowest latency (desktop/gaming)", "full"),
                           ("Voluntary — balanced (default distro)", "voluntary"),
                           ("None — throughput (server)", "none"),
                           ("Real-time (RT)", "rt")]:
            self.preempt.addItem(label, val)
        g2v.addWidget(self.preempt)

        g3 = QGroupBox("Timer frequency (HZ)"); g3v = QVBoxLayout(g3)
        self.hz = QComboBox()
        for v_hz in ("1000", "750", "500", "300", "250"):
            self.hz.addItem(v_hz + (" (desktop default)" if v_hz == "1000" else ""), v_hz)
        g3v.addWidget(self.hz)

        g4 = QGroupBox("Tick mode"); g4v = QVBoxLayout(g4)
        self.tick = QComboBox()
        self.tick.addItem("Idle tickless (NO_HZ_IDLE) — recommended", "idle")
        self.tick.addItem("Full tickless (NO_HZ_FULL) — HPC/RT",       "full")
        self.tick.addItem("Periodic",                                    "periodic")
        g4v.addWidget(self.tick)

        v.addWidget(g); v.addWidget(g2); v.addWidget(g3); v.addWidget(g4); v.addStretch(1)
        return w

    def _tab_tool(self) -> QWidget:
        w = QWidget(); v = QVBoxLayout(w)
        g = QGroupBox("Compiler"); f = QFormLayout(g)
        self.compiler = QComboBox()
        clang_hint = " (detected)" if self.sp.has_clang and self.sp.has_lld else " (not installed yet — will be fetched)"
        self.compiler.addItem(f"Auto-detect (prefer Clang if present){clang_hint}", "auto")
        self.compiler.addItem("GCC",          "gcc")
        self.compiler.addItem("Clang + LLVM", "clang")
        f.addRow("Toolchain:", self.compiler)
        self.lto = QComboBox()
        self.lto.addItem("Auto (ThinLTO if Clang + enough RAM)", "auto")
        self.lto.addItem("ThinLTO — fast link, near-Full quality", "thin")
        self.lto.addItem("Full LTO — best perf, heavy RAM+time",   "full")
        self.lto.addItem("Disabled",                                "no")
        f.addRow("Link-time optimisation:", self.lto)
        hint = QLabel(
            "LTO requires Clang+LLD. <b>ThinLTO</b> is the recommended choice "
            "for desktops — ~5–10% perf uplift at modest link-time cost. "
            "<b>Full LTO</b> wants 32 GB+ RAM."
        )
        hint.setObjectName("hint"); hint.setWordWrap(True)
        f.addRow(hint)

        g2 = QGroupBox("Parallelism"); f2 = QFormLayout(g2)
        self.jobs = QSpinBox(); self.jobs.setRange(1, 256); self.jobs.setValue(self.sp.cpu_threads)
        f2.addRow("Parallel make jobs (-j):", self.jobs)
        ram_hint = QLabel(
            f"Detected {self.sp.cpu_threads} logical CPUs, {self.sp.ram_gb} GB RAM. "
            "Smart defaults bounds -j by RAM so LTO linking doesn't OOM."
        )
        ram_hint.setObjectName("hint"); ram_hint.setWordWrap(True)
        f2.addRow(ram_hint)

        g3 = QGroupBox("GPU-specific tweaks"); g3v = QVBoxLayout(g3)
        self.chk_nvidia = QCheckBox("Disable Nouveau (for NVIDIA proprietary driver users)")
        self.chk_amd    = QCheckBox("Enable amdgpu for legacy SI/CIK GPUs")
        self.chk_nvidia.setChecked(self.sp.has_nvidia)
        self.chk_amd.setChecked(self.sp.has_amdgpu)
        g3v.addWidget(self.chk_nvidia); g3v.addWidget(self.chk_amd)

        v.addWidget(g); v.addWidget(g2); v.addWidget(g3); v.addStretch(1)
        return w

    def _tab_advanced(self) -> QWidget:
        w = QWidget(); v = QVBoxLayout(w)
        g = QGroupBox("Starting .config"); gv = QVBoxLayout(g)
        self.config_mode = QComboBox()
        self.config_mode.addItem("Auto (running kernel → distro → defconfig)", "auto")
        self.config_mode.addItem("Running kernel config",   "running")
        self.config_mode.addItem("localmodconfig (only currently-loaded modules)", "localmod")
        self.config_mode.addItem("defconfig (upstream defaults)", "defconfig")
        self.config_mode.addItem("Load from file…", "file")
        gv.addWidget(self.config_mode)

        row = QHBoxLayout()
        self.config_file = QLineEdit()
        self.config_file.setPlaceholderText("Path to .config (only when 'Load from file')")
        pick = QToolButton(); pick.setText("…"); pick.clicked.connect(self._browse_config)
        row.addWidget(self.config_file, 1); row.addWidget(pick)
        holder = QWidget(); holder.setLayout(row); gv.addWidget(holder)
        self.config_mode.currentIndexChanged.connect(
            lambda _i: self.config_file.setEnabled(self.config_mode.currentData() == "file")
        )
        self.config_file.setEnabled(False)

        g2 = QGroupBox("Extra config fragment"); h2 = QHBoxLayout(g2)
        self.extra_cfg = QLineEdit()
        self.extra_cfg.setPlaceholderText("Optional: file with extra CONFIG_* lines to merge")
        pick2 = QToolButton(); pick2.setText("…"); pick2.clicked.connect(self._browse_extra)
        h2.addWidget(self.extra_cfg, 1); h2.addWidget(pick2)

        g3 = QGroupBox("Behaviour"); g3v = QVBoxLayout(g3)
        self.verbose = QCheckBox("Verbose build output (make V=1 — shows every compiler command)")
        self.download_only = QCheckBox("Download only (fetch sources/patches, don't build)")
        self.build_only = QCheckBox("Build only (don't package)")
        for c in (self.verbose, self.download_only, self.build_only):
            g3v.addWidget(c)

        g4 = QGroupBox("Build log file"); g4v = QVBoxLayout(g4)
        self.log_to_file = QCheckBox(
            "Write full build output to a log file (strongly recommended)"
        )
        self.log_to_file.setChecked(True)
        g4v.addWidget(self.log_to_file)
        row4 = QHBoxLayout()
        self.log_file_path = QLineEdit()
        self.log_file_path.setPlaceholderText(
            "Auto: <outdir>/build-YYYYMMDD-HHMMSS.log"
        )
        pick3 = QToolButton(); pick3.setText("…"); pick3.clicked.connect(self._browse_log)
        row4.addWidget(self.log_file_path, 1); row4.addWidget(pick3)
        holder4 = QWidget(); holder4.setLayout(row4); g4v.addWidget(holder4)
        log_hint = QLabel(
            "Every line shown in the Build log pane is mirrored verbatim to "
            "this file. If a build fails (e.g. generic 'Error 2' at link "
            "time), open this file to find the real compiler/linker message."
        )
        log_hint.setWordWrap(True); log_hint.setObjectName("hint")
        g4v.addWidget(log_hint)
        # Enable/disable the path field based on checkbox
        self.log_to_file.toggled.connect(
            lambda on: self.log_file_path.setEnabled(on)
        )

        v.addWidget(g); v.addWidget(g2); v.addWidget(g3); v.addWidget(g4); v.addStretch(1)
        return w

    # -- helpers ------------------------------------------------------------
    def _apply_smart_defaults(self) -> None:
        """Re-detect hardware and push recommended settings into every widget."""
        self.sp = detect_system()
        self.specs_lbl.setText(describe_system(self.sp))
        cfg = smart_defaults(BuildConfig(), self.sp)

        # Source
        self.kernel_series.setText(cfg.kernel_series)
        self.kernel_version.setText("")   # always auto-latest
        self.local_version.setText(cfg.local_version)
        self.patches_on.setChecked(cfg.patches)
        self.auto_fallback.setChecked(cfg.auto_fallback_series)

        # CPU/Arch
        idx = self.march.findData(cfg.march)
        if idx < 0:
            idx = self.march.findData("auto")
        self.march.setCurrentIndex(max(idx, 0))
        self.o_level.setCurrentText(cfg.o_level)

        # Scheduler/timing
        self.preempt.setCurrentIndex(self.preempt.findData(cfg.preempt))
        self.hz.setCurrentIndex(self.hz.findData(cfg.hz))
        self.tick.setCurrentIndex(self.tick.findData(cfg.tick))

        # Toolchain
        self.compiler.setCurrentIndex(self.compiler.findData(cfg.compiler))
        self.lto.setCurrentIndex(self.lto.findData(cfg.lto))
        self.jobs.setValue(cfg.jobs)
        self.chk_nvidia.setChecked(cfg.nvidia_tweaks)
        self.chk_amd.setChecked(cfg.amdgpu_tweaks)

        # Advanced
        self.config_mode.setCurrentIndex(self.config_mode.findData(cfg.config_mode))
        self.log_to_file.setChecked(cfg.log_to_file)
        self.log_file_path.setText(cfg.log_file_path)
        self.log_file_path.setEnabled(cfg.log_to_file)

        if hasattr(self, "status_lbl"):
            self.status_lbl.setText("Smart defaults applied")

    def _browse_config(self) -> None:
        p, _ = QFileDialog.getOpenFileName(self, "Select kernel .config", "", "All files (*)")
        if p: self.config_file.setText(p)

    def _browse_extra(self) -> None:
        p, _ = QFileDialog.getOpenFileName(self, "Select extra config fragment", "", "All files (*)")
        if p: self.extra_cfg.setText(p)

    def _browse_log(self) -> None:
        p, _ = QFileDialog.getSaveFileName(self, "Choose build log file path",
                                           str(Path.home() / "cyfare-build.log"),
                                           "Log files (*.log);;All files (*)")
        if p: self.log_file_path.setText(p)

    def _collect_config(self) -> BuildConfig:
        return BuildConfig(
            kernel_series = self.kernel_series.text().strip() or "7.0",
            kernel_version = self.kernel_version.text().strip(),
            local_version = self.local_version.text().strip() or "-cyfare",
            march = self.march.currentData(),
            o_level = self.o_level.currentText(),
            preempt = self.preempt.currentData(),
            hz = self.hz.currentData(),
            tick = self.tick.currentData(),
            compiler = self.compiler.currentData(),
            lto = self.lto.currentData(),
            jobs = self.jobs.value(),
            config_mode = self.config_mode.currentData(),
            config_file = self.config_file.text().strip(),
            extra_config = self.extra_cfg.text().strip(),
            patches = self.patches_on.isChecked(),
            auto_fallback_series = self.auto_fallback.isChecked(),
            verbose = self.verbose.isChecked(),
            download_only = self.download_only.isChecked(),
            build_only = self.build_only.isChecked(),
            workdir = Path(self.workdir.text().strip() or str(Path.home() / "cyfare-build")),
            outdir = Path(self.outdir.text().strip() or str(Path.home() / "cyfare-out")),
            nvidia_tweaks = self.chk_nvidia.isChecked(),
            amdgpu_tweaks = self.chk_amd.isChecked(),
            log_to_file = self.log_to_file.isChecked(),
            log_file_path = self.log_file_path.text().strip(),
        )

    def _preview(self) -> None:
        cfg = self._collect_config()
        lines = [
            f"Kernel series      : {cfg.kernel_series}",
            f"Exact version      : {cfg.kernel_version or '(auto)'}",
            f"Local suffix       : {cfg.local_version}",
            f"march / -O         : {cfg.march} / -O{cfg.o_level}",
            f"Scheduler          : BORE (via patchset: {cfg.patches})",
            f"Auto series fallb. : {cfg.auto_fallback_series}",
            f"Preempt / HZ / Tick: {cfg.preempt} / {cfg.hz} / {cfg.tick}",
            f"Compiler / LTO     : {cfg.compiler} / {cfg.lto}",
            f"Jobs               : -j{cfg.jobs}",
            f"GPU tweaks         : nvidia={cfg.nvidia_tweaks}, amdgpu={cfg.amdgpu_tweaks}",
            f"Log to file        : {cfg.log_to_file}"
            + (f" ({cfg.log_file_path})" if cfg.log_file_path else " (auto)"),
            f"Config mode        : {cfg.config_mode}"
            + (f" ({cfg.config_file})" if cfg.config_mode == "file" else ""),
            f"Workdir / Outdir   : {cfg.workdir} / {cfg.outdir}",
            "",
            "--- Detected hardware ---",
            describe_system(self.sp),
        ]
        QMessageBox.information(self, "Build configuration", "\n".join(lines))

    # -- run ----------------------------------------------------------------
    def _start(self, actions: list[str]) -> None:
        if self.worker is not None:
            QMessageBox.warning(self, APP_NAME, "A build is already running.")
            return
        if not self.sp.is_debian_family:
            QMessageBox.critical(self, APP_NAME,
                                 "Non-Debian system detected; refusing to run.")
            return
        cfg = self._collect_config()
        if os.geteuid() != 0:
            if not self.priv.ensure(self):
                return
        self.log.clear()
        self.worker = BuildWorker(cfg, self.sp, self.priv, actions)
        self.worker.sig.log.connect(self._append_log)
        self.worker.sig.status.connect(self.status_lbl.setText)
        self.worker.sig.done.connect(self._on_done)
        self._set_running(True)
        self.worker.start()

    def _stop(self) -> None:
        if self.worker:
            self._append_log("\n[stop requested]\n")
            self.worker.cancel()

    def _on_done(self, ok: bool, msg: str) -> None:
        self._append_log(f"\n[{'success' if ok else 'failed'}] {msg}\n")
        self.status_lbl.setText("Done" if ok else f"Failed: {msg}")
        self._set_running(False)
        if self.worker:
            self.worker.wait()
            self.worker = None

    def _set_running(self, running: bool) -> None:
        for b in (self.btn_build, self.btn_bi, self.btn_install,
                  self.btn_clean, self.btn_preview):
            b.setEnabled(not running)
        self.btn_stop.setEnabled(running)
        self.progress.setVisible(running)
        self.status_lbl.setText("Running…" if running else "Ready")

    def _append_log(self, text: str) -> None:
        self.log.moveCursor(QTextCursor.MoveOperation.End)
        self.log.insertPlainText(text)
        self.log.moveCursor(QTextCursor.MoveOperation.End)

    def closeEvent(self, e) -> None:
        if self.worker is not None:
            r = QMessageBox.question(
                self, APP_NAME,
                "A build is still running. Stop it and quit?",
                QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No)
            if r != QMessageBox.StandardButton.Yes:
                e.ignore(); return
            self._stop()
            if self.worker:
                self.worker.wait(3000)
        self.priv.clear()
        e.accept()


# =============================================================================

def main() -> int:
    app = QApplication(sys.argv)
    app.setStyle(QStyleFactory.create("Fusion"))
    app.setApplicationName(APP_NAME)
    pal = QPalette()
    pal.setColor(QPalette.ColorRole.Window,          QColor("#16181d"))
    pal.setColor(QPalette.ColorRole.WindowText,      QColor("#e6e8ee"))
    pal.setColor(QPalette.ColorRole.Base,            QColor("#12141a"))
    pal.setColor(QPalette.ColorRole.AlternateBase,   QColor("#1b1e25"))
    pal.setColor(QPalette.ColorRole.Text,            QColor("#e6e8ee"))
    pal.setColor(QPalette.ColorRole.Button,          QColor("#252a35"))
    pal.setColor(QPalette.ColorRole.ButtonText,      QColor("#e6e8ee"))
    pal.setColor(QPalette.ColorRole.Highlight,       QColor("#3b82f6"))
    pal.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
    app.setPalette(pal)
    app.setStyleSheet(DARK_QSS)
    win = KernelBuilder(); win.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())
