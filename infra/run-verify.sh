#!/usr/bin/env bash
# One-shot cloud verification of `odometer_halts`.
#
#   bash infra/run-verify.sh
#
# Provisions an ephemeral EC2 box with Terraform (no SSH — no ingress at
# all; driven via SSM Run Command, files via a transfer bucket), ships
# this checkout's coq/ sources up, builds the full chain from a clean
# busycoq clone, checks `Print Assumptions odometer_halts` is axiom-free,
# pulls the logs back, and destroys everything it created — including on
# failure or Ctrl-C. ~$0.30/hr while running; typically well under $1.
#
# Needs: terraform >= 1.5, AWS credentials (env/profile/SSO), aws CLI.
set -euo pipefail
cd "$(dirname "$0")"
export TF_IN_AUTOMATION=1

terraform init -input=false > /dev/null

cleanup() {
  rc=$?
  echo '--- destroying the verification stack ---'
  terraform destroy -auto-approve -input=false
  exit $rc
}
trap cleanup EXIT

terraform apply -auto-approve -input=false
IID=$(terraform output -raw instance_id)
BUCKET=$(terraform output -raw bucket)

tar czf /tmp/coq-src.tgz -C .. coq
aws s3 cp /tmp/coq-src.tgz "s3://$BUCKET/coq-src.tgz"

echo "--- waiting for SSM agent on $IID ---"
for _ in $(seq 1 40); do
  PING=$(aws ssm describe-instance-information \
    --filters "Key=InstanceIds,Values=$IID" \
    --query 'InstanceInformationList[0].PingStatus' --output text 2>/dev/null || true)
  [ "$PING" = "Online" ] && break
  sleep 15
done
[ "$PING" = "Online" ] || { echo "SSM agent never came online"; exit 1; }

PARAMS=$(BUCKET="$BUCKET" node -e '
  const fs = require("fs");
  const script = "export BUCKET=" + process.env.BUCKET + "\n"
    + fs.readFileSync("verify-remote.sh", "utf8");
  console.log(JSON.stringify({ executionTimeout: ["21600"], commands: [script] }));
')
CMD_ID=$(aws ssm send-command \
  --instance-ids "$IID" \
  --document-name AWS-RunShellScript \
  --comment "bb6 odometer_halts verification" \
  --output-s3-bucket-name "$BUCKET" \
  --output-s3-key-prefix ssm-logs \
  --parameters "$PARAMS" \
  --query 'Command.CommandId' --output text)
echo "--- SSM command $CMD_ID dispatched; polling (build takes 1-3h) ---"

while :; do
  ST=$(aws ssm get-command-invocation --command-id "$CMD_ID" --instance-id "$IID" \
    --query Status --output text 2>/dev/null || echo Pending)
  case "$ST" in
    Success|Failed|TimedOut|Cancelled|Undeliverable|Terminated) break ;;
  esac
  sleep 60
done
echo "--- SSM command finished: $ST ---"

mkdir -p out
aws s3 cp "s3://$BUCKET/ssm-logs/" out/ --recursive 2>/dev/null || true
find out -name stdout -exec cp {} last-verify.log \; 2>/dev/null || true
aws s3 cp "s3://$BUCKET/assumptions.txt" last-assumptions.txt 2>/dev/null || true
aws s3 cp "s3://$BUCKET/status.txt" last-status.txt 2>/dev/null || true

echo
if [ "$ST" = "Success" ] && grep -q 'Closed under the global context' last-assumptions.txt; then
  echo "RESULT: VERIFY-PASS — odometer_halts is axiom-free."
else
  echo "RESULT: FAILED (SSM status: $ST) — see infra/last-verify.log"
  tail -n 30 last-verify.log 2>/dev/null || true
  exit 1
fi
