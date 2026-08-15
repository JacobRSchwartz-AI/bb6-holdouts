#!/usr/bin/env bash
# Runs ON the verification instance, as root, via SSM Run Command.
# Env: BUCKET (transfer bucket with coq-src.tgz). Results are uploaded
# to the bucket even on failure; all stdout is also captured by SSM.
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive

WORK=/build
mkdir -p "$WORK"
upload() {
  aws s3 cp "$WORK/assumptions.txt" "s3://$BUCKET/assumptions.txt" 2>/dev/null || true
  aws s3 cp "$WORK/status.txt" "s3://$BUCKET/status.txt" 2>/dev/null || true
}
trap upload EXIT

systemctl stop unattended-upgrades 2>/dev/null || true

# Small swap safety net; the chain peaks under 1GB after the
# small-step refactor.
fallocate -l 4G /swapfile-coq
chmod 600 /swapfile-coq
mkswap /swapfile-coq > /dev/null
swapon /swapfile-coq
free -h
apt-get -o DPkg::Lock::Timeout=600 update -qq
apt-get -o DPkg::Lock::Timeout=600 install -y -qq \
  --no-install-recommends coq git make unzip curl > /dev/null
# noble has no awscli apt package; use the official installer
curl -sS https://awscli.amazonaws.com/awscli-exe-linux-x86_64.zip -o /tmp/awscliv2.zip
unzip -q /tmp/awscliv2.zip -d /tmp
/tmp/aws/install > /dev/null
coqc --version

cd "$WORK"
aws s3 cp "s3://$BUCKET/coq-src.tgz" .
tar xzf coq-src.tgz
git clone --depth 1 https://github.com/meithecatte/busycoq
cd busycoq/verify
cp "$WORK"/coq/*.v .

FILES="LibTactics.v Helper.v Pigeonhole.v TM.v Compute.v Flip.v Permute.v \
Individual.v BB62.v Individual62.v Odometer.v OdometerDip.v \
OdometerOrbit.v OdometerCrisis.v OdometerBase.v OdometerLedger.v"
coq_makefile -Q . BusyCoq -o Makefile.port $FILES
# -j1: parallel make once produced checksum-inconsistent .vo files.
# TIMED=1: per-file wall time in the log.
make -f Makefile.port -j1 TIMED=1

echo 'Require Import BusyCoq.OdometerLedger. Print Assumptions odometer_halts.' > check_axioms.v
coqtop -Q . BusyCoq -batch -l check_axioms.v 2>&1 | tee "$WORK/assumptions.txt"
grep -q 'Closed under the global context' "$WORK/assumptions.txt"
echo 'VERIFY-PASS: odometer_halts is closed under the global context (zero axioms)' \
  | tee "$WORK/status.txt"
