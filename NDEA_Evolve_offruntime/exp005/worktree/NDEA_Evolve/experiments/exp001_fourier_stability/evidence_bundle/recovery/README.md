
# Runtime-loss and recovery index

Two ephemeral Colab endpoints were externally lost during this experiment.

1. Original endpoint `m-s-kkb-usc1a1-35dczkazprg9n` was recorded pruned at
   `2026-09-05T10:44:44.202603Z`. Its `/content` filesystem and Git objects were
   lost. The historical baseline commit
   `01ac3a3837f221a378e71f4d8de4f02534238532` and tag
   `baseline-verified-lean4.31-mathlib-v4.31.0` are identities in preserved history,
   not objects recovered from that VM. No unavailable baseline-report bytes were
   fabricated.

2. Replacement endpoint `m-s-kkb-usc1b1-2rn1s57wbiaz9` first returned 404 at
   `2026-09-05T11:48:04.285Z`, immediately before a checkpoint command could run.
   Its accepted Lean source and complete verbose log had already been downloaded,
   and the Julia-green Git/tar checkpoint was already independently verified locally.

3. CPU endpoint `m-s-kkb-euw4b0-37wn4k0g8orsh` restored the verified checkpoint,
   reconstructed the exact toolchain, reran Julia, direct Lean checking, a fresh
   verbose build, controls, signatures, logical-dependency audit, and all assurance
   gates. Preclosure reached 79/79 PASS and was then downloaded and safely verified
   off-runtime before final documentation began.

Evidence map:

- `original_cli_history_through_loss.jsonl` — frozen original history, SHA-256
  `2f19b2e966bdcb4a4fd088f8d1e9ec7f09415eeef6ea135db38e9fda2480c8f7`
- `historical_execution_index.json` and `historical_execution_transcripts/`
- `runtime_loss_events.json`, `runtime_loss_002.json`, and `runtime_loss_002.md`
- `colab_lifecycle_sanitized.json` — credential-free lifecycle fields only; the raw
  CLI debug log is deliberately excluded because it contains transient proxy tokens
- off-runtime remote/local checkpoint receipts in this directory

“Runtime identity continuity PASS” means the captured identity was stable within a
single endpoint interval. It does not claim that different endpoint VMs were the
same machine.
