import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability

namespace CapLean

/--
The bridge lemma: `traceWithinScopeBool = true`
unfolds to `withinScopeBool op cap = true` for every op.
-/
theorem traceWithinScope_iff (t : Trace) (cap : Capability) :
    traceWithinScope t cap ↔ ∀ op ∈ t, withinScope op cap := by
  simp [traceWithinScope, traceWithinScopeBool, withinScope,
        List.all_eq_true, List.mem_iff_get]

/--
**Capability Envelope Theorem**
If a program's trace passes the capability check,
every operation in the trace is individually within scope.
-/
theorem capabilityEnvelope
    (prog : AgentM α)
    (cap  : Capability)
    (h    : traceWithinScope prog.collectTrace cap)
    : ∀ op ∈ prog.collectTrace, withinScope op cap :=
  (traceWithinScope_iff prog.collectTrace cap).mp h

end CapLean
