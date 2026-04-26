import CapLean.AgentOp
import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability
import CapLean.SafetySpine

-- CapLean/Examples.lean
namespace CapLean

-- A sample capability: read/write under /workspace only, no exec, no network
def workspaceCap : Capability := {
  allowRead     := true
  allowWrite    := true
  allowExec     := false
  allowEval     := true
  allowNetwork  := false
  allowInstall  := false
  readPrefixes  := ["/workspace"]
  writePrefixes := ["/workspace"]
  minTrust      := .verified
}

-- A safe agent program
def safeAgent : AgentM Unit := do
  AgentM.liftOp (AgentOp.readFile "/workspace/main.py")
  AgentM.liftOp (AgentOp.writeFile "/workspace/main.py" "patched content")
  AgentM.liftOp (AgentOp.evalCode "import pytest; pytest.main()")

-- Compute its trace
#eval safeAgent.collectTrace
-- Expected: [readFile "/workspace/main.py", writeFile "/workspace/main.py" ..., evalCode ...]

-- An unsafe agent (tries to read /etc/passwd — outside allowed prefixes)
def attackAgent : AgentM Unit := do
  AgentM.liftOp (AgentOp.readFile "/etc/passwd")

-- This trace should NOT satisfy workspaceCap
example : ¬ traceWithinScope attackAgent.collectTrace workspaceCap := by native_decide

-- Negative example: attack trace is rejected
example : ¬ traceWithinScope attackAgent.collectTrace workspaceCap := by
  native_decide

-- Positive example: safe trace is accepted
example : traceWithinScope safeAgent.collectTrace workspaceCap := by
  native_decide

-- Spine theorem: every op in safe trace is individually within scope
example : ∀ op ∈ safeAgent.collectTrace, withinScope op workspaceCap :=
  capabilityEnvelope safeAgent workspaceCap (by native_decide)
  
/-! ### Runtime enforcement — #eval to see the attack agent rejected -/

-- Bool check: is the safe agent's trace within scope?
#eval traceWithinScopeBool safeAgent.collectTrace workspaceCap
-- Expected: true

-- Bool check: is the attack agent's trace within scope?
#eval traceWithinScopeBool attackAgent.collectTrace workspaceCap
-- Expected: false

-- Which operation violated the capability?
#eval firstViolation attackAgent.collectTrace workspaceCap
-- Expected: some (AgentOp.readFile "/etc/passwd")

-- Full enforcement: try to run attack agent under workspaceCap
#eval do
  match enforceCapability attackAgent workspaceCap with
  | .ok ()   => pure "Agent completed successfully"
  | .error op => pure s!"BLOCKED: operation {repr op} is outside the declared capability"
-- Expected: "BLOCKED: operation AgentOp.readFile \"/etc/passwd\" is outside the declared capability"

-- Full enforcement: safe agent passes
#eval do
  match enforceCapability safeAgent workspaceCap with
  | .ok ()   => pure "Agent completed successfully"
  | .error op => pure s!"BLOCKED: operation {repr op} is outside the declared capability"
-- Expected: "Agent completed successfully"

end CapLean
