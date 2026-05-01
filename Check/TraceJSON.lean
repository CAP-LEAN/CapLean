import Lean.Data.Json
import CapLean

namespace CapLean.Check

open Lean

def parseTrustLevel (s : String) : Except String TrustLevel :=
  match s with
  | "verified"        => .ok .verified
  | "unreviewed"      => .ok .unreviewed
  | "knownVulnerable" => .ok .knownVulnerable
  | other             => .error s!"unknown trust level: {other}"

def parseAgentOp (j : Json) : Except String AgentOp := do
  let op ← j.getObjValAs? String "op"
  match op with
  | "ReadFile" =>
    return .readFile (← j.getObjValAs? String "path")
  | "WriteFile" =>
    let path ← j.getObjValAs? String "path"
    let content := (j.getObjValAs? String "content").toOption.getD ""
    return .writeFile path content
  | "ExecShell" =>
    let cmd ← j.getObjValAs? String "cmd"
    let args := (j.getObjValAs? (List String) "args").toOption.getD []
    return .execShell cmd args
  | "EvalCode" =>
    return .evalCode (← j.getObjValAs? String "snippet")
  | "InstallPkg" =>
    return .installPkg (← j.getObjValAs? String "pkg")
  | "NetworkCall" =>
    return .networkCall (← j.getObjValAs? String "url")
  | "ExplicitApprove" =>
    return .explicitApprove (← j.getObjValAs? String "pkg")
  | other => .error s!"unknown op type: {other}"

def parseTrace (contents : String) : Except String Trace :=
  let lines := contents.splitOn "\n" |>.filter (fun l => !l.trimAscii.isEmpty)
  lines.mapM fun line => do
    let j ← Json.parse line
    parseAgentOp j

def parseCapability (j : Json) : Except String Capability := do
  let trustStr ← j.getObjValAs? String "minTrust"
  let minTrust ← parseTrustLevel trustStr
  return {
    allowRead     := ← j.getObjValAs? Bool "allowRead"
    allowWrite    := ← j.getObjValAs? Bool "allowWrite"
    allowExec     := ← j.getObjValAs? Bool "allowExec"
    allowEval     := ← j.getObjValAs? Bool "allowEval"
    allowNetwork  := ← j.getObjValAs? Bool "allowNetwork"
    allowInstall  := ← j.getObjValAs? Bool "allowInstall"
    readPrefixes  := ← j.getObjValAs? (List String) "readPrefixes"
    writePrefixes := ← j.getObjValAs? (List String) "writePrefixes"
    minTrust
  }

def parseSandboxConfig (j : Json) : Except String Sandbox := do
  return {
    allowedPaths    := ← j.getObjValAs? (List String) "allowedPaths"
    allowedSyscalls := ← j.getObjValAs? (List String) "allowedSyscalls"
  }

def parsePackage (j : Json) : Except String Package := do
  let trustStr ← j.getObjValAs? String "trust"
  let trust ← parseTrustLevel trustStr
  return { name := ← j.getObjValAs? String "name", trust }

def parseDepGraph (j : Json) : Except String DepGraph := do
  let arr ← j.getArr?
  let entries ← arr.toList.mapM fun elem => do
    let pkg ← parsePackage elem
    let depNames ← elem.getObjValAs? (List String) "deps"
    return (pkg, depNames)
  entries.mapM fun (pkg, depNames) => do
    let deps ← depNames.mapM fun name =>
      match entries.find? (fun (p, _) => p.name == name) with
      | some (p, _) => .ok p
      | none        => .error s!"depGraph references unknown package: {name}"
    return (pkg, deps)

def parseConfig (contents : String) : Except String (Capability × Sandbox × DepGraph) := do
  let j ← Json.parse contents
  let cap ← parseCapability (← j.getObjVal? "capability")
  let sb  ← parseSandboxConfig (← j.getObjVal? "sandbox")
  let dg  ← parseDepGraph (← j.getObjVal? "depGraph")
  return (cap, sb, dg)

end CapLean.Check
