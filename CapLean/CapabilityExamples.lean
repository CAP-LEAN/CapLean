import CapLean.AgentOp
import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability
import CapLean.SafetySpine

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

-- A safe agent program — each op carries a compile-time scope proof via `op!`
def safeAgent : AgentM workspaceCap Unit := do
  op! (AgentOp.readFile "/workspace/main.py")
  op! (AgentOp.writeFile "/workspace/main.py" "patched content")
  op! (AgentOp.evalCode "import pytest; pytest.main()")

-- Compute its trace
#eval safeAgent.collectTrace

/-!
### Negative example — attack agent cannot be represented since it violates the capability and would fail to compile
-- The example is kept for illustrative purposes only

The following definition would fail to compile because `native_decide`
cannot prove `withinScope (readFile "/etc/passwd") workspaceCap`:

```
def attackAgent : AgentM workspaceCap Unit := do
  op! (AgentOp.readFile "/etc/passwd")   -- ERROR: proof obligation fails
```

This is the payoff of by-construction capability containment:
the bad program simply cannot be expressed as a well-typed term.
-/

-- We can still demonstrate the attack as a raw trace for the external checker
def attackTrace : Trace := [AgentOp.readFile "/etc/passwd"]

-- The raw trace is rejected by the external trace checker
example : ¬ traceWithinScope attackTrace workspaceCap := by native_decide

-- The safe trace passes the external checker too
example : traceWithinScope safeAgent.collectTrace workspaceCap := by
  native_decide

-- Spine theorem: every op in safe trace is individually within scope
-- Now proved without any hypothesis — containment follows from the type
example : ∀ op ∈ safeAgent.collectTrace, withinScope op workspaceCap :=
  capabilityEnvelope safeAgent

/-! ### Runtime enforcement on external traces -/

-- Bool check: is the safe agent's trace within scope?
#eval traceWithinScopeBool safeAgent.collectTrace workspaceCap
-- Expected: true

-- Bool check: is the attack trace within scope?
#eval traceWithinScopeBool attackTrace workspaceCap
-- Expected: false

-- Which operation violated the capability?
#eval firstViolation attackTrace workspaceCap
-- Expected: some (AgentOp.readFile "/etc/passwd")

-- Enforce on external trace: attack trace is blocked
#eval do
  match enforceTrace attackTrace workspaceCap with
  | .ok ()   => pure "Trace passed"
  | .error op => pure s!"BLOCKED: operation {repr op} is outside the declared capability"
-- Expected: "BLOCKED: operation AgentOp.readFile \"/etc/passwd\" is outside the declared capability"

-- Enforce on external trace: safe agent's trace passes
#eval do
  match enforceTrace safeAgent.collectTrace workspaceCap with
  | .ok ()   => pure "Trace passed"
  | .error op => pure s!"BLOCKED: operation {repr op} is outside the declared capability"
-- Expected: "Trace passed"

end CapLean
