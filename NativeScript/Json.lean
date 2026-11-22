import Json
import NativeScript.Syntax

/-!
# The `cardano-cli` JSON format

```json
{ "type": "atLeast", "required": 2,
  "scripts": [ { "type": "sig", "keyHash": "…" }, { "type": "after", "slot": 1000 } ] }
```

Parsing and printing use [lean-json](https://github.com/paulbutcher/lean-json),
whose parser and printer are proved correct against the RFC 8259 grammar. Its
strict defaults reject duplicate object keys, which matters here:
`{"type": "sig", "type": "any", …}` would otherwise mean different scripts to
different tools.
-/

namespace NativeScript

private def field (j : _root_.Json) (k : String) : Except String _root_.Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error s!"missing field \"{k}\" in {Json.compress j}"

private def withContext {α : Type} (ctx : String) : Except String α → Except String α
  | .ok a => .ok a
  | .error e => .error s!"{ctx}: {e}"

partial def Script.fromJson? (j : _root_.Json) : Except String Script := do
  let ty ← withContext "\"type\"" ((← field j "type").getStr?)
  let nat (k : String) : Except String Nat := do withContext s!"\"{k}\"" ((← field j k).getNat?)
  let subs : Unit → Except String (List Script) := fun _ => do
    let arr ← withContext "\"scripts\"" ((← field j "scripts").getArr?)
    arr.toList.mapM Script.fromJson?
  match ty with
  | "sig" => return .sig (← withContext "\"keyHash\"" ((← field j "keyHash").getStr?)).toLower
  | "all" => return .all (← subs ())
  | "any" => return .any (← subs ())
  | "atLeast" => return .atLeast (← nat "required") (← subs ())
  | "after" => return .after (← nat "slot")
  | "before" => return .before (← nat "slot")
  | other => throw s!"unknown native script type \"{other}\""

/-- Fields in the order `cardano-cli` writes them. -/
partial def Script.toJson : Script → _root_.Json
  | .sig k => Json.mkObj [("type", "sig"), ("keyHash", k)]
  | .all ss => Json.mkObj [("type", "all"), ("scripts", .arr (ss.map toJson).toArray)]
  | .any ss => Json.mkObj [("type", "any"), ("scripts", .arr (ss.map toJson).toArray)]
  | .atLeast n ss => Json.mkObj
      [("type", "atLeast"), ("required", Json.ofNat n),
       ("scripts", .arr (ss.map toJson).toArray)]
  | .after t => Json.mkObj [("type", "after"), ("slot", Json.ofNat t)]
  | .before t => Json.mkObj [("type", "before"), ("slot", Json.ofNat t)]

def Script.parse (input : String) : Except String Script := do
  match Json.parse input with
  | .ok j => Script.fromJson? j
  | .error e => .error s!"invalid JSON: {e}"

end NativeScript
