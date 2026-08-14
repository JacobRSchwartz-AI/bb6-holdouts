#!/usr/bin/env bash
# Build the busycoq port. Runs INSIDE WSL:
#   wsl.exe -e bash -lc 'bash /mnt/c/Users/JacobSchwartz/Documents/bb6-holdouts/tools/coq-build.sh'
# Copies coq/*.v into the WSL busycoq clone (~/busycoq, github.com/meithecatte/busycoq)
# and compiles the minimal dependency chain plus our files.
set -euo pipefail
REPO=/mnt/c/Users/JacobSchwartz/Documents/bb6-holdouts
VERIFY="$HOME/busycoq/verify"
cp "$REPO"/coq/*.v "$VERIFY"/
cd "$VERIFY"
FILES="LibTactics.v Helper.v Pigeonhole.v TM.v Compute.v Flip.v Permute.v Individual.v BB62.v Individual62.v Odometer.v OdometerDip.v"
coq_makefile -Q . BusyCoq -o Makefile.port $FILES
make -f Makefile.port -j"$(nproc)"
echo "PORT BUILD OK"
