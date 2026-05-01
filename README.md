# CAPLean(Capability Access Protocol with Lean) — Proved Capability Envelope for Agentic Coding Pipelines

## What it is
A Lean 4 library that models agentic coding tools as free monads over
a declared operation set, and proves three families of safety theorems
over traces of those monads.

## Three layers
| Layer | File | Theorem | What it catches |
|---|---|---|---|
| Capability | `SafetySpine.lean` | `capabilityEnvelope` | Ops outside declared capability |
| Sandbox | `Sandbox.lean` | `sandboxContainment` | Effects outside declared path boundary |
| Trust | `TrustLattice.lean` | `trustMonotonicity` | Packages below trust floor |

## Honest scope
The capability layer enforces containment **by construction**: `AgentM` is
indexed by a `Capability`, and each operation carries a compile-time proof
that it is within scope. Programs containing out-of-scope ops are rejected
by the type checker — no runtime check is needed.

The sandbox layer proves that *if* an `EffectAnnotation` is correct,
containment holds — it does not verify the annotation itself.

The trust layer proves that *if* the declared dependency graph is accurate,
every install meets the trust floor or was explicitly approved.
It does not verify the graph against a live registry.

## Running
```bash
lake build   # proves all theorems, ~30s
```
