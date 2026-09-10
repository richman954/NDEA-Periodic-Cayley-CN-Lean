## Mission 4: Recovery Robustness Review (Updated)

Based on the actual recovery infrastructure found in `NDEA_Recovery/` and `NDEA_Evolve_offruntime/`:

1. **Watcher Coverage and Stale RUNNING statuses (IMPORTANT)**:
   - `TASK_STATE.json` reveals the presence of several previous watchers (e.g. `94110`, `59441`, `27367`, and currently `9546`).
   - The watcher `27367` stopped with an explicit error: `ValueError('Invalid GitHub evidence file... SPATIAL_REFINEMENT_PREPARE.diff')`. This indicates the watcher accurately transitions to `failed` and doesn't get stuck in `RUNNING`.

2. **PID Reuse (CLEANUP)**:
   - Previous watchers list low PID numbers (e.g. `pid: 2`, `pid: 3`), implying they run in disposable shells/containers where PID reuse is highly probable if state files aren't cleaned.

3. **Experiment-number hard coding (CRITICAL)**:
   - The recovery state explicitly uses `active_experiment: exp016` and `active_experiment: exp014`. While it is correctly updating in `TASK_STATE.json`, many scripts likely hardcode the `exp016` path based on the directory structure `NDEA_Evolve_offruntime/exp016/`.

4. **Restoration over newer drafts (IMPORTANT)**:
   - The `on_resume` instruction correctly enforces: "Read active Exp016 task state and actual receipts... preserve sealed Exp013-015... Actual saved state already contains 50 accepted Exp016 modules; continue it, do not restart."
   - However, a blind archive restore would obliterate the 6 follow-on drafts. Proper savepoints (Mission 2) must explicitly capture dirty state to avoid this.

5. **Build Artifact Restore (CLEANUP)**:
   - Recovery payloads currently archive `.zip` snapshots of `exp016/`, but do not universally bind the Lean compiler hash or the explicit `build/lib` `.olean` files alongside them. Adding Artifact Save Points (Mission 2) solves this.
