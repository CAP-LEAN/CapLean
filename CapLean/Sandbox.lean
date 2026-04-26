import CapLean.AgentOp
import CapLean.Trace
import CapLean.Capability

namespace CapLean

/-!
## Layer 2 — Sandbox Containment

This layer specialises `EvalCode` and `ExecShell`.
Even if Layer 1 permits these ops, Layer 2 constrains what the
*executed code* can reach at runtime: which file paths it may touch
and which syscall categories it may invoke.

The key abstraction is an **EffectAnnotation** — a declared mapping from
each `AgentOp` to the low-level effects it will produce. The containment
theorem says: if every declared effect is within the sandbox boundary,
the agent is sandbox-safe.
-/

-- ────────────────────────────────────────────
-- 1. Effect type — what executed code can do
-- ────────────────────────────────────────────

/-- Low-level effects that code execution produces at runtime -/
inductive Effect where
  | fsRead  : String → Effect    -- read a file path
  | fsWrite : String → Effect    -- write a file path
  | netConn : String → Effect    -- open a network connection to host
  | spawn   : String → Effect    -- spawn a subprocess
  deriving Repr, DecidableEq, BEq

abbrev EffectTrace := List Effect

-- ────────────────────────────────────────────
-- 2. Sandbox — the declared boundary
-- ────────────────────────────────────────────

/-- A sandbox declares what executed code may touch -/
structure Sandbox where
  allowedPaths    : List String  -- fsRead/fsWrite must start with one of these
  allowedSyscalls : List String  -- "NetConn" | "Spawn" to allow those categories
  deriving Repr

-- ────────────────────────────────────────────
-- 3. Containment predicate (Bool + Prop)
-- ────────────────────────────────────────────

/-- Is a single effect within the sandbox boundary? -/
def effectWithinSandbox : Effect → Sandbox → Bool
  | .fsRead path,  sb => sb.allowedPaths.any (path.startsWith ·)
  | .fsWrite path, sb => sb.allowedPaths.any (path.startsWith ·)
  | .netConn _,    sb => sb.allowedSyscalls.contains "NetConn"
  | .spawn _,      sb => sb.allowedSyscalls.contains "Spawn"

/-- Are all effects in a trace within the sandbox? -/
def effectTraceWithinSandbox (t : EffectTrace) (sb : Sandbox) : Bool :=
  t.all (effectWithinSandbox · sb)

/-- Prop version — used in theorem statements -/
def effectTraceContained (t : EffectTrace) (sb : Sandbox) : Prop :=
  effectTraceWithinSandbox t sb = true

instance (t : EffectTrace) (sb : Sandbox) : Decidable (effectTraceContained t sb) :=
  inferInstanceAs (Decidable (effectTraceWithinSandbox t sb = true))

-- ────────────────────────────────────────────
-- 4. Effect annotation + trace expansion
-- ────────────────────────────────────────────

/--
An effect annotation maps each `AgentOp` to the effects it will produce.
This is the user-declared contract: "when this op runs, these are the
effects it will have." The sandbox checks this contract.
-/
abbrev EffectAnnotation := AgentOp → EffectTrace

/-- Expand a trace into its full effect trace using the annotation -/
def traceAnnotatedEffects (t : Trace) (ann : EffectAnnotation) : EffectTrace :=
  (t.map ann).flatten

-- ────────────────────────────────────────────
-- 5. Containment theorem
-- ────────────────────────────────────────────

/--
**Sandbox Containment Theorem**

If every effect declared by the annotation is within the sandbox,
then for every op in the trace, every effect that op may produce
is individually sandbox-safe.

The proof is structural: `traceAnnotatedEffects` is a flatMap over
the trace, so membership in the full effect trace implies membership
in some individual op's annotation.
-/
theorem sandboxContainment
    (t : Trace) (sb : Sandbox) (ann : EffectAnnotation)
    (h : effectTraceContained (traceAnnotatedEffects t ann) sb)
    : ∀ op ∈ t, ∀ eff ∈ ann op, effectWithinSandbox eff sb = true := by
  simp only [effectTraceContained, effectTraceWithinSandbox,
             List.all_eq_true, traceAnnotatedEffects] at h
  intro op hop eff heff
  apply h
  simp only [List.mem_flatten, List.mem_map]
  exact ⟨ann op, ⟨op, hop, rfl⟩, heff⟩

-- ────────────────────────────────────────────
-- 6. Demo sandbox + attack scenarios
-- ────────────────────────────────────────────

/-- The demo sandbox: only /workspace paths, no network, no spawn -/
def workspaceSandbox : Sandbox where
  allowedPaths    := ["/workspace"]
  allowedSyscalls := []

/-- Agent that only runs EvalCode -/
def evalAgent : AgentM Unit :=
  AgentM.liftOp (.evalCode "run_tests()")

/-- Agent that tries ExecShell -/
def shellAgent : AgentM Unit :=
  AgentM.liftOp (.execShell "bash" ["-i"])

-- Effect annotations for each scenario

/-- SAFE: eval reads and writes only workspace files -/
def safeEvalAnn : EffectAnnotation
  | .evalCode _ => [.fsRead "/workspace/test.py",
                    .fsWrite "/workspace/result.txt"]
  | _           => []

/-- ATTACK 1: eval tries to read /etc/passwd -/
def etcPasswdAnn : EffectAnnotation
  | .evalCode _ => [.fsRead "/etc/passwd"]
  | _           => []

/-- ATTACK 2: eval tries to open a network connection -/
def netExfilAnn : EffectAnnotation
  | .evalCode _ => [.netConn "attacker.com"]
  | _           => []

/-- ATTACK 3: exec spawns an interactive shell -/
def shellEscapeAnn : EffectAnnotation
  | .execShell _ _ => [.spawn "/bin/bash"]
  | _              => []

-- ────────────────────────────────────────────
-- 7. Runtime checks (#eval)
-- ────────────────────────────────────────────

-- Safe eval: contained → true
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace safeEvalAnn) workspaceSandbox

-- /etc/passwd attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace etcPasswdAnn) workspaceSandbox

-- Network exfil attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects evalAgent.collectTrace netExfilAnn) workspaceSandbox

-- Shell escape attack → false
#eval effectTraceWithinSandbox
  (traceAnnotatedEffects shellAgent.collectTrace shellEscapeAnn) workspaceSandbox

-- ────────────────────────────────────────────
-- 8. Formal proofs
-- ────────────────────────────────────────────

-- Safe agent: formally proved contained
example : effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace safeEvalAnn)
    workspaceSandbox := by native_decide

-- Attack 1: /etc/passwd read is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace etcPasswdAnn)
    workspaceSandbox := by native_decide

-- Attack 2: network exfil is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects evalAgent.collectTrace netExfilAnn)
    workspaceSandbox := by native_decide

-- Attack 3: shell escape is blocked
example : ¬ effectTraceContained
    (traceAnnotatedEffects shellAgent.collectTrace shellEscapeAnn)
    workspaceSandbox := by native_decide

-- Spine theorem fires: safe eval satisfies containment per-op
example : ∀ op ∈ evalAgent.collectTrace,
    ∀ eff ∈ safeEvalAnn op, effectWithinSandbox eff workspaceSandbox = true :=
  sandboxContainment _ _ _ (by native_decide)

end CapLean
