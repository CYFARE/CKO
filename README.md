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

Pre-Build Releases: https://github.com/CYFARE/CKO/releases

### changelog
- **Parallel builds actually use multiple cores now.** Removed `--output-sync=line` from compile/package commands; switched make subprocesses to buffered stdout and `close_fds=False` so GNU make's jobserver FIFO stays open to sub-makes and writers don't block on a full pipe.
- **Respect CPU affinity/container limits.** Added `_available_cpus()` using `os.sched_getaffinity(0)` / `os.process_cpu_count()` instead of `os.cpu_count()`. `jobs` default and system detection now report the CPUs the process can actually use.
- **Sanitize inherited `MAKEFLAGS`.** Strip external `--output-sync`, `-jN`, and `-O...` flags so a shell/CI setting can't silently serialize the build.
- **Root disk detection** now correctly handles NVMe (`nvme0n1`/`nvme0n1p1`) and eMMC (`mmcblk0pN`) devices.
- **ISA level detection** now accepts `abm` as an alias for `lzcnt` and `bmi` as an alias for `bmi1`, fixing under-detection on modern Intel CPUs.
- **GPU detection** AMD branch now has explicit parentheses for correct operator precedence.
- **SCHED_BORE checkbox** is now wired into `BuildConfig` and honored during config tuning.

### Changed
- Refactored make command construction into `_make_base_cmd()` and `_compile_env()` helpers; packaging now uses the same `KCFLAGS` environment as compilation.
- Subprocess `_run()` now uses buffered I/O by default and escalates cancel from `terminate()` to `kill()` if the process ignores SIGTERM.

### Internal
- Moved `datetime` import to the top-level.
