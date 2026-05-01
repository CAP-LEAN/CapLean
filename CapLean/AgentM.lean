import CapLean.AgentOp
import CapLean.CapCore

namespace CapLean

/-!
## AgentM — Capability-Indexed Free Monad

**Purpose:** Models agent programs as a free monad whose constructors carry
proofs of capability scope, so out-of-scope programs fail to type-check.

**Key definitions:**
- `AgentM cap α` — inductive program tree (`pure` / `step`)
- `AgentM.bind`, `Monad` instance — sequential composition
- `AgentM.liftOp` — lifts a single op given a scope proof
- `op!` macro — discharges the scope proof via `native_decide`

**Key theorems:** none directly here — `capabilityEnvelope` lives in `SafetySpine`.

**Assumptions:** Scope proofs are decided via `native_decide`; users may
supply manual proofs when the decision procedure cannot reduce.
-/

/--
`AgentM` is a capability-indexed free-monad-style program tree.
Every `step` carries a proof that the operation is within the
declared capability scope, so out-of-scope programs are rejected
at compile time — capability containment holds by construction.
-/
inductive AgentM (cap : Capability) : Type → Type where
  | pure : α → AgentM cap α
  | step : (op : AgentOp) → withinScope op cap → AgentM cap α → AgentM cap α

@[simp]
def AgentM.bind : AgentM cap α → (α → AgentM cap β) → AgentM cap β
  | .pure a,      k => k a
  | .step op h m, k => .step op h (AgentM.bind m k)

instance : Monad (AgentM cap) where
  pure  := AgentM.pure
  bind  := AgentM.bind

/-- Lift a single op into the monad, requiring a proof of scope -/
def AgentM.liftOp (op : AgentOp) (h : withinScope op cap) : AgentM cap Unit :=
  .step op h (.pure ())

/-- Convenience macro: discharge the scope proof automatically via `native_decide` -/
macro "op!" op:term : term =>
  `(AgentM.liftOp $op (by native_decide))

end CapLean
