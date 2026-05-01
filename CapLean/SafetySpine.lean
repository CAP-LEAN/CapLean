import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability

namespace CapLean

/--
Bridge lemma (still useful for external trace checking):
`traceWithinScopeBool = true` unfolds to `withinScopeBool op cap = true` for every op.
-/
theorem traceWithinScope_iff (t : Trace) (cap : Capability) :
    traceWithinScope t cap ↔ ∀ op ∈ t, withinScope op cap := by
  simp [traceWithinScope, traceWithinScopeBool, withinScope,
        List.all_eq_true, List.mem_iff_get]

/--
**Capability Envelope Theorem (by construction)**

Every operation in an `AgentM cap` program's trace is within scope by construction
No hypothesis needed — the proof extracts the `withinScope` evidence
carried by each `step` constructor.
-/
theorem capabilityEnvelope
    (prog : AgentM cap α)
    : ∀ op ∈ prog.collectTrace, withinScope op cap := by
  induction prog with
  | pure _ => simp
  | step op h _ ih =>
    simp [AgentM.collectTrace]
    exact ⟨h, ih⟩

end CapLean
