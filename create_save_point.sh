#!/bin/bash
set -e

# Artifact Save Point prototype
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
ARTIFACT_CLASS=${1:-"development"} # development | pre-risk | qualified
ARTIFACT_DIR="/tmp/artifact_test_ndea_${TIMESTAMP}"
ARCHIVE_NAME="ndea_savepoint_${ARTIFACT_CLASS}_${TIMESTAMP}.tar.gz"

mkdir -p "${ARTIFACT_DIR}"

echo "Creating manifest..."
cat <<MANIFEST > "${ARTIFACT_DIR}/manifest.json"
{
  "timestamp": "${TIMESTAMP}",
  "class": "${ARTIFACT_CLASS}",
  "git_commit": "$(git rev-parse HEAD 2>/dev/null || echo 'unknown')",
  "lean_toolchain": "$(cat lean-toolchain)",
  "compiler_identity": "$(lake --version)"
}
MANIFEST

echo "Gathering source hashes..."
find NDEAMathlibGate paper audit -type f -exec sha256sum {} + > "${ARTIFACT_DIR}/source_hashes.txt"

echo "Copying compiled oleans..."
mkdir -p "${ARTIFACT_DIR}/build"
if [ -d ".lake/build/lib" ]; then
    cp -r .lake/build/lib "${ARTIFACT_DIR}/build/"
fi

echo "Copying audit evidence..."
cp -r audit "${ARTIFACT_DIR}/"

echo "Creating archive..."
tar -czf "/tmp/${ARCHIVE_NAME}" -C "${ARTIFACT_DIR}" .

echo "Artifact SHA-256:"
sha256sum "/tmp/${ARCHIVE_NAME}" > "/tmp/${ARCHIVE_NAME}.sha256"
cat "/tmp/${ARCHIVE_NAME}.sha256"

echo "Artifact save point created at /tmp/${ARCHIVE_NAME}"

# Cleanup staging
rm -rf "${ARTIFACT_DIR}"
