import CapLean.AgentOp
import CapLean.AgentM

namespace CapLean

/-!
## Trace — Operation Sequence Extraction

**Purpose:** Extracts the sequence of ops an `AgentM` program would perform,
so external checks (capability, sandbox, trust) can be stated against a list.

**Key definitions:**
- `Trace` — alias for `List AgentOp`
- `AgentM.collectTrace` — folds an `AgentM` program into its op list

**Key theorems:**
- `collectTrace_pure`, `collectTrace_step` — definitional unfolding (`@[simp]`)
- `collectTrace_bind_pure`, `collectTrace_bind_step` — distribute trace over `>>=`

**Assumptions:** The trace is purely syntactic — it captures the ops the
program declares, not what runtime evaluation produces.
-/

/-- A trace is the linear sequence of ops a program declares. -/
abbrev Trace := List AgentOp

/-- Walk an `AgentM` program and collect the ops it would perform, in order. -/
def AgentM.collectTrace : AgentM cap α → Trace
  | .pure _      => []
  | .step op _ m => op :: m.collectTrace

@[simp]
theorem collectTrace_pure (a : α) :
    (AgentM.pure a : AgentM cap α).collectTrace = [] := rfl

@[simp]
theorem collectTrace_step (op : AgentOp) (h : withinScope op cap) (m : AgentM cap α) :
    (AgentM.step op h m).collectTrace = op :: m.collectTrace := rfl

@[simp]
theorem collectTrace_bind_pure (a : α) (f : α → AgentM cap β) :
    (AgentM.pure a >>= f).collectTrace = (f a).collectTrace := by
  simp [Bind.bind, AgentM.bind]

@[simp]
theorem collectTrace_bind_step (op : AgentOp) (h : withinScope op cap) (m : AgentM cap α) (f : α → AgentM cap β) :
    (AgentM.step op h m >>= f).collectTrace =
    op :: (m >>= f).collectTrace := by
  simp [Bind.bind, AgentM.bind]

end CapLean
