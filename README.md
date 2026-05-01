# CAPLean(Capability Access Protocol with Lean) — Proved Capability Envelope for Agentic Coding Pipelines

## What it is
A Lean 4 library that models agentic coding tools as free monads over
a declared operation set, and proves three families of safety theorems
over traces of those monads.

## Three layers
| Layer | File | Theorem | What it catches |
|---|---|---|---|
| Capability | `SafetySpine.lean` | `capabilityEnvelope` | Ops outside declared capability |
| Sandbox | `Sandbox.lean` | `sandboxContainment`, `canonicalContainment`, `conservativeContainment`, `certifiedSandboxContainment`, `fullEnvelope` | Effects outside declared path boundary |
| Trust | `TrustLattice.lean` | `trustMonotonicity` | Packages below trust floor |

## Honest scope

**Capability layer (Layer 1)** — enforces containment **by construction**.
`AgentM` is indexed by a `Capability`, and each operation carries a
compile-time proof that it is within scope. Programs containing
out-of-scope ops are rejected by the type checker — no runtime check needed.

**Sandbox layer (Layer 2)** — three tiers of trust for effect containment:

| Tier | Mechanism | Trust assumption |
|---|---|---|
| **Transparent ops** | `canonicalEffects` derives effects structurally from the op (file I/O, network) | None — correctness is definitional |
| **Conservative mode** | `maximalBound sb` assumes opaque ops can do *anything the sandbox allows* | None per-op — the sandbox boundary is the bound |
| **Certified mode** | Custom `OpaqueBound` paired with `RuntimeEnforces` axiom (`CertifiedBound`) | Explicit — the axiom appears in every proof term that depends on it |

File paths are normalized (`.` and `..` resolved) before prefix checking,
so traversal attacks like `/workspace/../../etc/passwd` are rejected.

`fullEnvelope` combines Layer 1 + Layer 2 into a single theorem: an
`AgentM` program is both capability-safe and sandbox-safe.

**Trust layer (Layer 3)** — proves that *if* the declared dependency graph
is accurate, every install meets the trust floor or was explicitly approved.
It does not verify the graph against a live registry.

## Running
```bash
lake build   # proves all theorems, ~30s
```
