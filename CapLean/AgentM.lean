import CapLean.AgentOp

namespace CapLean

/--
`AgentM` is a simple free-monad-style program tree where every
`AgentOp` returns `Unit`. This sidesteps the existential-type
issue that makes `collectTrace` require `unsafeCast`.
For trace-level safety proofs this is sufficient — we only care
which ops appear, not what values they return.
-/
inductive AgentM : Type → Type where
  | pure : α → AgentM α
  | step : AgentOp → AgentM α → AgentM α   -- op, then continue with rest

@[simp]
def AgentM.bind : AgentM α → (α → AgentM β) → AgentM β
  | .pure a,    k => k a
  | .step op m, k => .step op (AgentM.bind m k)

instance : Monad AgentM where
  pure  := AgentM.pure
  bind  := AgentM.bind

/-- Lift a single op into the monad -/
def AgentM.liftOp (op : AgentOp) : AgentM Unit :=
  .step op (.pure ())

end CapLean
