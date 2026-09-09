
# Manifest protocol and causal exclusions

`PAYLOAD_SHA256SUMS` covers every substantive evidence file present before manifest
generation. It is checked by GNU `sha256sum` and by an independent Python parser that
rejects absolute paths, traversal, duplicates, symlinks, missing files, and mismatches.

`SHA256SUMS` then covers that entire payload plus `PAYLOAD_SHA256SUMS` and both stable
payload-verification receipts. `SHA256SUMS.meta` covers `SHA256SUMS` and its GNU
verification log.

Self-reference is impossible: a manifest cannot contain its own final hash, and a
verification log cannot be included in the manifest whose verification it reports.
Accordingly, `SHA256SUMS.meta.verify.txt` is the causal endpoint and is transparently
excluded from the manifest it verifies. Final archive hashes and Chromebook-side
verification are recorded in an adjacent delivery receipt outside the archive.
