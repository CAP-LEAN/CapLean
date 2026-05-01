import Check.TraceJSON

/-!
## Check.Main — CLI Trace Verifier

**Purpose:** Command-line entry point. Reads an externally-produced trace
(JSONL) and a policy config (JSON), then runs all three safety layers
against them. Exit code is 0 on pass, 1 on policy violation, 2 on parse error.

**Usage:**
```
caplean-check --trace TRACE.jsonl --config CONFIG.json
```
Defaults: `/tmp/caplean_trace.jsonl`, `/tmp/caplean_config.json`.

**Layers checked:**
1. `enforceTrace` — every op within declared capability
2. `effectTraceWithinSandbox` on `canonicalEffects` — no opaque-bound trust assumption
3. `traceInstallsSafe` — every install meets the trust floor or is explicitly approved

**Assumptions:** Layer 2 here is intentionally conservative — it uses
`canonicalEffects` only, so `evalCode` / `execShell` contribute no extra
effects. A stricter check (with `OpaqueBound`) is the caller's job.
-/

open CapLean CapLean.Check

def parseArgs (args : List String) : String × String :=
  let rec go : List String → String → String → String × String
    | "--trace"  :: path :: rest, _, cfg => go rest path cfg
    | "--config" :: path :: rest, tr, _  => go rest tr path
    | _ :: rest, tr, cfg                 => go rest tr cfg
    | [], tr, cfg                        => (tr, cfg)
  go args "/tmp/caplean_trace.jsonl" "/tmp/caplean_config.json"

def reprOp : AgentOp → String
  | .readFile path       => s!"readFile \"{path}\""
  | .writeFile path _    => s!"writeFile \"{path}\""
  | .execShell cmd _     => s!"execShell \"{cmd}\""
  | .evalCode snippet    => s!"evalCode \"{snippet}\""
  | .installPkg name     => s!"installPkg \"{name}\""
  | .networkCall url     => s!"networkCall \"{url}\""
  | .explicitApprove name => s!"explicitApprove \"{name}\""

def findFailedInstalls (t : Trace) (g : DepGraph) (cap : Capability) : List String :=
  t.filterMap fun op =>
    match op with
    | .installPkg name =>
      let approved := t.any (· == .explicitApprove name)
      let trusted := match g.lookup name with
        | some pkg => pkgAllowedBool pkg g cap
        | none     => false
      if approved || trusted then none else some name
    | _ => none

def main (args : List String) : IO UInt32 := do
  let (tracePath, configPath) := parseArgs args

  let traceContents ← try IO.FS.readFile tracePath catch e => do
    IO.eprintln s!"[Parse error] Cannot read trace file {tracePath}: {e}"
    return (2 : UInt32)
  let configContents ← try IO.FS.readFile configPath catch e => do
    IO.eprintln s!"[Parse error] Cannot read config file {configPath}: {e}"
    return (2 : UInt32)

  let trace ← match parseTrace traceContents with
    | .ok t    => pure t
    | .error e => do IO.eprintln s!"[Parse error] Trace: {e}"; return (2 : UInt32)
  let (cap, sb, graph) ← match parseConfig configContents with
    | .ok cfg  => pure cfg
    | .error e => do IO.eprintln s!"[Parse error] Config: {e}"; return (2 : UInt32)

  let mut failed := false

  -- Layer 1: Capability
  match enforceTrace trace cap with
  | .ok () =>
    IO.println s!"[Layer 1] PASS: all {trace.length} ops within capability scope"
  | .error op =>
    IO.println s!"[Layer 1] FAIL: {reprOp op} is outside declared capability"
    failed := true

  -- Layer 2: Sandbox (canonical effects only — no trust assumption)
  if effectTraceWithinSandbox (traceAnnotatedEffects trace canonicalEffects) sb then
    IO.println s!"[Layer 2] PASS: all canonical effects within sandbox"
  else
    IO.println s!"[Layer 2] FAIL: canonical effects escape sandbox boundary"
    failed := true

  -- Layer 3: Trust
  if traceInstallsSafe trace graph cap then
    IO.println s!"[Layer 3] PASS: all installs meet trust floor or are explicitly approved"
  else
    let names := findFailedInstalls trace graph cap
    let detail := ", ".intercalate (names.map (s!"\"{·}\""))
    IO.println s!"[Layer 3] FAIL: install(s) below trust floor without approval: {detail}"
    failed := true

  return (if failed then 1 else 0)
