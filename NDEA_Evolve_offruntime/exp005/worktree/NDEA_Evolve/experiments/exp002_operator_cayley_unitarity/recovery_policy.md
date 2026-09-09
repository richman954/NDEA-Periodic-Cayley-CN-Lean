# Recovery and checkpoint policy

Colab `/content` and Git repositories stored there are ephemeral. A runtime commit is
not a durable checkpoint.

For each milestone—preflight, Julia-green, Lean-green, preclosure, and final—the
following sequence is mandatory:

1. Check that no Experiment 001 tracked path differs from its verified final tag.
2. Commit Experiment 002-owned changes and create a named tag.
3. Create a complete Git bundle and a milestone artifact archive outside the repo.
4. Record remote sizes and SHA-256 hashes.
5. Download both artifacts and the remote receipt to the Chromebook.
6. Reject absolute paths, traversal, symlinks, hardlinks, devices, FIFOs, duplicate
   paths, and conflicting writes before local extraction.
7. Independently verify the Git commit/tag and every available internal manifest.
8. Write an adjacent local verification receipt.

If the endpoint disappears, restore only from the latest locally verified Git bundle,
reinstall the pinned toolchain, recheck dependency revisions, and rerun every
execution-dependent gate performed after that checkpoint. Never recreate unavailable
evidence bytes or equate endpoint identity with mathematical provenance.

Raw Colab CLI logs that may contain proxy credentials must never enter an evidence
bundle. Only sanitized lifecycle records may be preserved.
