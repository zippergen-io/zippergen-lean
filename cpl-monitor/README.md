# CPL Monitor — Lean Formalization

Lean 4 formalization for the paper
"Runtime Verification with Causal Past Logic".

## Contents

| File | Contents |
|---|---|
| `CPLMonitor/MSC.lean` | Abstract MSC interface: lifelines, causal order, local indices, latest-visible, previous-local |
| `CPLMonitor/CPLSyntax.lean` | CPL terms, atoms, and formulas |
| `CPLMonitor/CPLSemantics.lean` | Denotational MSC semantics (`Sat`), since recurrence |
| `CPLMonitor/MonitorState.lean` | Monitor state (vector clocks, views, stores, old values) and local evaluator |
| `CPLMonitor/LocalEval.lean` | Coherent pre-evaluation invariant and local evaluation correctness |
| `CPLMonitor/EventUpdate.lean` | Receive-merge, prepare-eval bridge, writeback, and end-to-end correctness |

## Main result

`SnapshotCoherent.monitor_correct_after_update`: for any event processed by
a valid local or receive update path, the owner-lifeline formula view agrees
with the denotational CPL semantics at that event.

## Building

```
cd cpl-monitor
lake build
```

Requires Lean 4 / Mathlib toolchain (see `lake-manifest.json`).
