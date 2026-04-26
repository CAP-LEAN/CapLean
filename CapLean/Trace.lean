import CapLean.AgentOp
import CapLean.AgentM

namespace CapLean

abbrev Trace := List AgentOp

def AgentM.collectTrace : AgentM α → Trace
  | .pure _    => []
  | .step op m => op :: m.collectTrace

@[simp]
theorem collectTrace_pure (a : α) :
    (AgentM.pure a : AgentM α).collectTrace = [] := rfl

@[simp]
theorem collectTrace_step (op : AgentOp) (m : AgentM α) :
    (AgentM.step op m).collectTrace = op :: m.collectTrace := rfl

@[simp]
theorem collectTrace_bind_pure (a : α) (f : α → AgentM β) :
    (AgentM.pure a >>= f).collectTrace = (f a).collectTrace := by
  simp [Bind.bind, AgentM.bind]

@[simp]
theorem collectTrace_bind_step (op : AgentOp) (m : AgentM α) (f : α → AgentM β) :
    (AgentM.step op m >>= f).collectTrace =
    op :: (m >>= f).collectTrace := by
  simp [Bind.bind, AgentM.bind]

end CapLean
