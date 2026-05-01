import CapLean.AgentOp
import CapLean.AgentM

namespace CapLean

abbrev Trace := List AgentOp

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
