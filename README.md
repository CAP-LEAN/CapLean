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
Theorems check **declared** behaviour against policies.
The sandbox layer proves that *if* an `EffectAnnotation` is correct,
containment holds — it does not verify the annotation itself.
The capability layer does post-hoc trace checking, not prevention by construction.

## Running
\`\`\`bash
lake build   # proves all theorems, ~30s
\`\`\`
