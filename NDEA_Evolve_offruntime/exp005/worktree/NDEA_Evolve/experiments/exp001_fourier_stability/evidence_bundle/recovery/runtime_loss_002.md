# Runtime loss 002 and verified recovery

The second CPU endpoint `m-s-kkb-usc1b1-2rn1s57wbiaz9` first returned 404 at
`2026-09-05T11:48:04.285000+00:00` while a Git checkpoint command was being submitted; that command
did not execute. A new CPU endpoint `m-s-kkb-euw4b0-37wn4k0g8orsh` was created.

Recovery used the already downloaded and locally verified Julia-green Git bundle
(`ca86486d0b20c558d953512304fd3419d82fc3f0fe32082fe5a0d4361b577d6a`) and tar checkpoint (`168d48bfc03dff1a1f2d4072d17e73f3fd444005a14dd9b91ba2a040741833f9`). The tar was
path-safety checked and all 19 regular-file payloads were compared
byte-for-byte with the Git restore. The complete verbose production build log had
also been downloaded before loss and was restored at its unchanged hash
`9ca34494c57e057619e39c908e8d1fcc425f5f3f98cdcb4ff998f1e7b63841c6`.

The historical baseline evidence directory was not fabricated or replaced. Lean,
Lake, elan and Mathlib were reconstructed at their exact pins; Julia 1.12.6 was
preinstalled and was not reinstalled.
