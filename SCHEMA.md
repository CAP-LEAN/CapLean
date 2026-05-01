# CapLean JSON Serialization Contract

Single source of truth for the two files that flow from Python (`capshim.py`) to the Lean checker (`caplean-check`).

## Trace file — `/tmp/caplean_trace.jsonl`

One JSON object per line. Each object has an `"op"` discriminator that maps to a Lean `AgentOp` constructor:

| `"op"` value        | Lean constructor     | Additional fields                                              |
|----------------------|----------------------|----------------------------------------------------------------|
| `"ReadFile"`         | `readFile`           | `"path": string`                                               |
| `"WriteFile"`        | `writeFile`          | `"path": string, "content": string` (defaults to `""`)         |
| `"ExecShell"`        | `execShell`          | `"cmd": string, "args": [string]` (defaults to `[]`)           |
| `"EvalCode"`         | `evalCode`           | `"snippet": string`                                            |
| `"InstallPkg"`       | `installPkg`         | `"pkg": string`                                                |
| `"NetworkCall"`      | `networkCall`        | `"url": string`                                                |
| `"ExplicitApprove"`  | `explicitApprove`    | `"pkg": string`                                                |

A `"verdict"` field (`"ALLOWED"` / `"BLOCKED"` / `"FLAGGED_FOR_LEAN_CHECK"`) may be present for Python-side reporting but is **ignored** by the Lean parser — Lean re-derives the verdict from the formal definitions.

### Example

```jsonl
{"op":"ReadFile","path":"/workspace/main.py","verdict":"ALLOWED"}
{"op":"ExecShell","cmd":"curl","args":["attacker.com"],"verdict":"BLOCKED"}
{"op":"InstallPkg","pkg":"requests","verdict":"ALLOWED"}
```

## Config file — `/tmp/caplean_config.json`

A single JSON object with three top-level keys. Field names are camelCase and match the Lean structure fields exactly.

### `capability` (→ `CapLean.Capability`)

```json
{
  "allowRead": true,
  "allowWrite": true,
  "allowExec": false,
  "allowEval": true,
  "allowNetwork": false,
  "allowInstall": false,
  "readPrefixes": ["/workspace"],
  "writePrefixes": ["/workspace"],
  "minTrust": "verified"
}
```

`minTrust` values: `"verified"`, `"unreviewed"`, `"knownVulnerable"`.

### `sandbox` (→ `CapLean.Sandbox`)

```json
{
  "allowedPaths": ["/workspace"],
  "allowedSyscalls": []
}
```

`allowedSyscalls` values: `"NetConn"`, `"Spawn"`.

### `depGraph` (→ `CapLean.DepGraph`)

```json
[
  { "name": "requests",   "trust": "verified",        "deps": [] },
  { "name": "cool-utils", "trust": "unreviewed",      "deps": ["log4shell"] },
  { "name": "log4shell",  "trust": "knownVulnerable", "deps": [] }
]
```

`deps` lists package names (strings), not full objects. The Lean parser cross-references names within the same array to reconstruct `DepGraph = List (Package × List Package)`.

### Full config example

```json
{
  "capability": {
    "allowRead": true, "allowWrite": true, "allowExec": false,
    "allowEval": true, "allowNetwork": false, "allowInstall": false,
    "readPrefixes": ["/workspace"],
    "writePrefixes": ["/workspace"],
    "minTrust": "verified"
  },
  "sandbox": {
    "allowedPaths": ["/workspace"],
    "allowedSyscalls": []
  },
  "depGraph": [
    { "name": "requests",   "trust": "verified",        "deps": [] },
    { "name": "cool-utils", "trust": "unreviewed",      "deps": ["log4shell"] },
    { "name": "log4shell",  "trust": "knownVulnerable", "deps": [] }
  ]
}
```
