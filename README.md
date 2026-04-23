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
