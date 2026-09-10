ARCHIVE_PATH=$1
RESTORE_DIR="/tmp/ndea_restore_test"

echo "Verifying hash..."
cd $(dirname "$ARCHIVE_PATH")
sha256sum -c "${ARCHIVE_PATH}.sha256"

echo "Restoring to ${RESTORE_DIR}..."
rm -rf "${RESTORE_DIR}"
mkdir -p "${RESTORE_DIR}"
tar -xzf "${ARCHIVE_PATH}" -C "${RESTORE_DIR}"

echo "Restored manifest:"
cat "${RESTORE_DIR}/manifest.json"
echo ""
echo "Save point successfully restored to ${RESTORE_DIR}"
