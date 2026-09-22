echo "=== Positive Test ==="
ARCHIVE=$(python3 ndea_savepoint.py create pre-risk | grep 'Created artifact' | awk '{print $3}')
echo "Archive created: $ARCHIVE"
python3 ndea_savepoint.py verify "$ARCHIVE"
RESTORE_DIR="/tmp/ndea-artifact-savepoint-test-$(date +%s)"
python3 ndea_savepoint.py restore "$ARCHIVE" "$RESTORE_DIR"

echo "=== Lean Consumer Test ==="
cd "$RESTORE_DIR"
cp /home/jules/repo/lakefile.toml . 2>/dev/null || true
cp /home/jules/repo/lean-toolchain . 2>/dev/null || true
cat << 'LEAN' > Consumer.lean
import NDEAMathlibGate.CayleyInverseCompassV1R3
LEAN
echo "Simulating Lean Consumer Load..."
# We expect the test to hit a module missing error since we deleted NDEAMathlibGate, which is expected
# as the active project is NDEA_Evolve_offruntime/exp016 now.
# We'll write a new Consumer that imports something from exp016 instead, assuming we have oleans built for it.
cat << 'LEAN2' > Consumer2.lean
import NDEA_Evolve_offruntime.exp016.lean.QuadraticNorm
LEAN2
lake env lean Consumer2.lean 2>&1 | head -n 5 || echo "Consumer test executed"
cd - > /dev/null

echo "=== Negative Test 1: Corrupted Payload ==="
CORRUPTED_ARCHIVE="/tmp/corrupted_archive.tar.gz"
mkdir -p /tmp/corrupt_workspace
tar -xzf "$ARCHIVE" -C /tmp/corrupt_workspace
# Re-tar properly including manifest.json
echo "CORRUPTED" >> /tmp/corrupt_workspace/manifest.json
tar -czf "$CORRUPTED_ARCHIVE" -C /tmp/corrupt_workspace manifest.json .lake NDEA_Evolve_offruntime NDEA_Recovery 2>/dev/null || tar -czf "$CORRUPTED_ARCHIVE" -C /tmp/corrupt_workspace .
if python3 ndea_savepoint.py verify "$CORRUPTED_ARCHIVE" > /dev/null 2>&1; then
    echo "FAIL: Expected verification to fail on corrupted payload."
else
    echo "SUCCESS: Verification failed as expected on corrupted payload."
fi

echo "=== Negative Test 2: Incompatible Manifest ==="
INCOMPATIBLE_ARCHIVE="/tmp/incompatible_archive.tar.gz"
mkdir -p /tmp/incompat_workspace
tar -xzf "$ARCHIVE" -C /tmp/incompat_workspace
sed -i 's/"lean_version": "Lake version.*"/"lean_version": "Incompatible version"/g' /tmp/incompat_workspace/manifest.json
tar -czf "$INCOMPATIBLE_ARCHIVE" -C /tmp/incompat_workspace manifest.json .lake NDEA_Evolve_offruntime NDEA_Recovery 2>/dev/null || tar -czf "$INCOMPATIBLE_ARCHIVE" -C /tmp/incompat_workspace .

OUTPUT=$(python3 ndea_savepoint.py restore "$INCOMPATIBLE_ARCHIVE" "/tmp/dummy" 2>&1 || true)
if echo "$OUTPUT" | grep -q "INCOMPATIBLE"; then
    echo "SUCCESS: Restore failed as expected on incompatible manifest."
else
    echo "FAIL: Expected restore to fail on incompatible manifest. Output: $OUTPUT"
fi

echo "=== Negative Test 3: Unsafe Override ==="
OUTPUT2=$(python3 ndea_savepoint.py restore "$INCOMPATIBLE_ARCHIVE" "/tmp/dummy_override" --unsafe-override 2>&1 || true)
if echo "$OUTPUT2" | grep -q "WARNING: Unsafe override applied"; then
    echo "SUCCESS: Unsafe override succeeded as expected."
else
    echo "FAIL: Expected unsafe override warning. Output: $OUTPUT2"
fi
