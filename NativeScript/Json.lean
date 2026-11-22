import Lean.Data.Json
import NativeScript.Syntax

/-!
# The `cardano-cli` JSON format

```json
{ "type": "atLeast", "required": 2,
  "scripts": [ { "type": "sig", "keyHash": "…" }, { "type": "after", "slot": 1000 } ] }
```
-/

namespace NativeScript
open Lean

partial def Script.fromJson? (j : Json) : Except String Script := do
  let ty ← j.getObjValAs? String "type"
  let subs : Unit → Except String (List Script) := fun _ => do
    let arr ← (← j.getObjVal? "scripts").getArr?
    arr.toList.mapM Script.fromJson?
  match ty with
  | "sig" => return .sig (← j.getObjValAs? String "keyHash").toLower
  | "all" => return .all (← subs ())
  | "any" => return .any (← subs ())
  | "atLeast" => return .atLeast (← j.getObjValAs? Nat "required") (← subs ())
  | "after" => return .after (← j.getObjValAs? Nat "slot")
  | "before" => return .before (← j.getObjValAs? Nat "slot")
  | other => throw s!"unknown native script type '{other}'"

partial def Script.toJson : Script → Json
  | .sig k => Json.mkObj [("type", "sig"), ("keyHash", k)]
  | .all ss => Json.mkObj [("type", "all"), ("scripts", Json.arr (ss.map toJson).toArray)]
  | .any ss => Json.mkObj [("type", "any"), ("scripts", Json.arr (ss.map toJson).toArray)]
  | .atLeast n ss => Json.mkObj
      [("type", "atLeast"), ("required", Lean.toJson n),
       ("scripts", Json.arr (ss.map toJson).toArray)]
  | .after t => Json.mkObj [("type", "after"), ("slot", Lean.toJson t)]
  | .before t => Json.mkObj [("type", "before"), ("slot", Lean.toJson t)]

def Script.parse (input : String) : Except String Script := do
  Script.fromJson? (← Json.parse input)

end NativeScript
