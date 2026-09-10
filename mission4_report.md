## Mission 4: Recovery Robustness Review

1. **Checkpoints/Watcher Coverage**: There are no background checkpoint watcher scripts currently in the repository (e.g. `cron`, `systemd`, or custom python daemon files). Thus, there's no automated savepoint mechanism that could overwrite newer drafts.
2. **Hard-coded Experiment Numbers**: The repository directory `NDEAMathlibGate/` contains scripts with versions like `V1`, `V2`, `V3R`, `V6R`, `V8_20260712_053434_060974` which appear to be hard-coded point-in-time snapshots of experiments.
3. **Restoration Hazard**: As demonstrated in the Artifact Save Point prototype, without a specific isolated sandbox environment, restoring a tarball directly over the working directory might overwrite uncommitted drafts. The script `restore_save_point.sh` mitigates this by extracting to `/tmp/ndea_restore_test` rather than the active workspace.
4. **PID reuse / Missing source checks**: Not applicable since there are no active watcher daemons.
5. **Local vs Remote Git reconciliation**: Git is generally relied upon for remote syncing.
