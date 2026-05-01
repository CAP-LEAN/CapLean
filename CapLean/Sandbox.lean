import CapLean.AgentOp
import CapLean.AgentM
import CapLean.Trace
import CapLean.Capability
import CapLean.SafetySpine

namespace CapLean

/-!
## Sandbox — Layer 2 Containment

**Purpose:** Even if Layer 1 permits `evalCode` / `execShell`, Layer 2
constrains what the *executed code* may touch — file paths and syscall
categories.

**Key definitions:**
- `Effect`, `EffectTrace`, `Sandbox` — boundary description
- `normalizePath` — collapses `.` / `..` so prefix checks defeat traversal
- `effectWithinSandbox`, `effectTraceContained` — containment predicates
- `EffectAnnotation`, `traceAnnotatedEffects` — user-declared op→effects map
- `canonicalEffects` — library-defined transparent-op effects
- `OpaqueBound`, `fullAnnotation` — user-declared bound for opaque ops only
- `maximalBound` — sandbox-derived worst-case bound (no per-op declaration)
- `RuntimeEnforces` (axiom), `CertifiedBound`, `certifiedAnnotation`

**Key theorems:**
- `sandboxContainment` — Layer 2 envelope (relative to user annotation)
- `canonicalContainment` — specialization for transparent ops, no trust needed
- `conservativeContainment` — specialization for `maximalBound`
- `certifiedSandboxContainment` — adds `RuntimeEnforces` to conclusion
- `fullEnvelope` — Layer 1 + Layer 2 in one shot

**Assumptions:** Effects of opaque ops (`evalCode`, `execShell`) come from
the user-supplied `OpaqueBound` — that is the trust boundary for Layer 2.
Canonical effects for transparent ops are definitional and cannot be lied about.

Demos and `#eval` blocks live in `CapLean.SandboxExamples`.
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
-- 2a. Path normalization
-- ────────────────────────────────────────────

/-- Collapse `.` and `..` segments so prefix checking is immune to traversal -/
def normalizePath (p : String) : String :=
  let parts := p.splitOn "/"
  let folded := parts.foldl (fun acc seg =>
    if seg == ".." then acc.dropLast
    else if seg == "." || seg == "" then acc
    else acc ++ [seg]) []
  "/" ++ "/".intercalate folded

-- ────────────────────────────────────────────
-- 3. Containment predicate (Bool + Prop)
-- ────────────────────────────────────────────

/-- Is a single effect within the sandbox boundary? -/
def effectWithinSandbox : Effect → Sandbox → Bool
  | .fsRead path,  sb => sb.allowedPaths.any (fun pre => (normalizePath path).startsWith pre)
  | .fsWrite path, sb => sb.allowedPaths.any (fun pre => (normalizePath path).startsWith pre)
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
-- 5. Canonical effects — correct by construction
-- ────────────────────────────────────────────

/--
Derives effects structurally from the op itself. For transparent ops
(file I/O, network), the effects are deterministic. For opaque ops
(evalCode, execShell), canonical effects capture only what is
statically visible (e.g. spawn for execShell); the rest comes from
`OpaqueBound`.
-/
def canonicalEffects : AgentOp → EffectTrace
  | .readFile path      => [.fsRead path]
  | .writeFile path _   => [.fsWrite path]
  | .networkCall url    => [.netConn url]
  | .execShell cmd _    => [.spawn cmd]
  | .evalCode _         => []
  | .installPkg _       => []
  | .explicitApprove _  => []

/--
User-declared bound on additional effects for opaque ops only.
This is the sole trust assumption — canonical effects for transparent
ops are definitional and cannot be overridden.
-/
structure OpaqueBound where
  evalEffects : CodeSnippet → EffectTrace
  execEffects : Cmd → List String → EffectTrace

/-- Combines canonical (structural) effects with the opaque bound -/
def fullAnnotation (ob : OpaqueBound) : EffectAnnotation := fun op =>
  canonicalEffects op ++ match op with
    | .evalCode snippet    => ob.evalEffects snippet
    | .execShell cmd args  => ob.execEffects cmd args
    | _                    => []

-- ────────────────────────────────────────────
-- 6. Containment theorems
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

/--
**Canonical Containment Theorem**

For transparent ops, containment holds with NO trust assumption on any
user-supplied annotation. The hypothesis only references `canonicalEffects`,
which is library-defined and correct by construction.
-/
theorem canonicalContainment
    (t : Trace) (sb : Sandbox)
    (h : effectTraceContained (traceAnnotatedEffects t canonicalEffects) sb)
    : ∀ op ∈ t, ∀ eff ∈ canonicalEffects op, effectWithinSandbox eff sb = true :=
  sandboxContainment t sb canonicalEffects h

-- ────────────────────────────────────────────
-- 6a. Conservative (sandbox-derived) bound
-- ────────────────────────────────────────────

/--
Derives a worst-case `OpaqueBound` from the sandbox itself: every opaque
op is assumed to produce reads and writes to every allowed path, plus
network and spawn effects if the sandbox permits those syscall categories.

The user never has to enumerate paths — the sandbox boundary is the
finite, known thing, so this is always sound (though over-approximate).
-/
def maximalBound (sb : Sandbox) : OpaqueBound where
  evalEffects _ :=
    sb.allowedPaths.flatMap (fun p => [.fsRead p, .fsWrite p])
    ++ (if sb.allowedSyscalls.contains "NetConn" then [.netConn "*"] else [])
    ++ (if sb.allowedSyscalls.contains "Spawn"   then [.spawn "*"]   else [])
  execEffects _ _ :=
    sb.allowedPaths.flatMap (fun p => [.fsRead p, .fsWrite p])
    ++ (if sb.allowedSyscalls.contains "NetConn" then [.netConn "*"] else [])
    ++ (if sb.allowedSyscalls.contains "Spawn"   then [.spawn "*"]   else [])

/--
**Conservative Containment Theorem**

Specialises `sandboxContainment` to `maximalBound sb`: if opaque ops
may do *anything the sandbox allows*, containment still holds — no
custom per-op annotation needed.
-/
theorem conservativeContainment
    (t : Trace) (sb : Sandbox)
    (h : effectTraceContained
           (traceAnnotatedEffects t (fullAnnotation (maximalBound sb))) sb)
    : ∀ op ∈ t, ∀ eff ∈ (fullAnnotation (maximalBound sb)) op,
        effectWithinSandbox eff sb = true :=
  sandboxContainment t sb _ h

-- ────────────────────────────────────────────
-- 6b. Certified bound (explicit runtime axiom)
-- ────────────────────────────────────────────

/--
An irrefutable axiom marking that a given `OpaqueBound` is enforced by
a runtime monitor. Because it is an `axiom` (not a `def`), it cannot be
proved by `rfl` or `native_decide` — the only way to inhabit it is to
explicitly construct a `CertifiedBound` with the evidence field
-/
axiom RuntimeEnforces : OpaqueBound → Prop

/-- Pairs an `OpaqueBound` with evidence that a runtime monitor enforces it -/
structure CertifiedBound where
  bound    : OpaqueBound
  evidence : RuntimeEnforces bound

/-- Annotation derived from a certified bound — identical to `fullAnnotation` -/
def certifiedAnnotation (cb : CertifiedBound) : EffectAnnotation :=
  fullAnnotation cb.bound

/--
**Certified Sandbox Containment Theorem**

Like `sandboxContainment`, but the conclusion additionally carries
`RuntimeEnforces cb.bound`.
-/
theorem certifiedSandboxContainment
    (t : Trace) (sb : Sandbox) (cb : CertifiedBound)
    (h : effectTraceContained (traceAnnotatedEffects t (certifiedAnnotation cb)) sb)
    : (∀ op ∈ t, ∀ eff ∈ (certifiedAnnotation cb) op,
        effectWithinSandbox eff sb = true)
      ∧ RuntimeEnforces cb.bound :=
  ⟨sandboxContainment t sb _ h, cb.evidence⟩

-- ────────────────────────────────────────────
-- 6c. Combined Layer 1 + Layer 2 theorem
-- ────────────────────────────────────────────

/--
**Full Envelope Theorem (Layer 1 + Layer 2)**

Pairs `capabilityEnvelope` (every op is within declared capability) with
`sandboxContainment` (every declared effect is within the sandbox) into
a single result: an `AgentM` program is both capability-safe and sandbox-safe.
-/
theorem fullEnvelope
    (prog : AgentM cap α) (sb : Sandbox) (ann : EffectAnnotation)
    (h : effectTraceContained (traceAnnotatedEffects prog.collectTrace ann) sb)
    : (∀ op ∈ prog.collectTrace, withinScope op cap)
    ∧ (∀ op ∈ prog.collectTrace, ∀ eff ∈ ann op, effectWithinSandbox eff sb = true) :=
  ⟨capabilityEnvelope prog, sandboxContainment prog.collectTrace sb ann h⟩

end CapLean
