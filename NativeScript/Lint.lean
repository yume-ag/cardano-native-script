import NativeScript.Analysis
import NativeScript.Hash
import NativeScript.Simplify

/-! # Warnings about suspicious scripts (heuristics, not proved) -/

namespace NativeScript

def validKeyHash (k : KeyHash) : Bool :=
  k.length == 56 && k.toList.all fun c => (hexVal c).isSome

partial def lintNode (path : String) (s : Script) : List String :=
  let own := lintShape path s
  let explained := own.any (·.startsWith s!"{path}: ")
  (if path != "root" && !explained && (dnf s).isEmpty then
    [s!"{path}: this branch can never be satisfied by a transaction with a valid interval"]
   else []) ++ own
where
  lintShape (path : String) : Script → List String
  | .sig k =>
    if validKeyHash k then [] else [s!"{path}: key hash '{k}' is not 56 hex characters"]
  | .all ss =>
    (if ss.isEmpty then [s!"{path}: `all []` is always true"] else []) ++ children path ss
  | .any ss =>
    (if ss.isEmpty then [s!"{path}: `any []` can never be satisfied"] else []) ++ children path ss
  | .atLeast n ss =>
    (if n > ss.length then
      [s!"{path}: requires {n} of only {ss.length} sub-scripts, so it can never be satisfied"]
     else []) ++
    (if n == 0 then [s!"{path}: `atLeast 0` is always true"] else []) ++
    (if ss.eraseDups.length < ss.length then
      [s!"{path}: repeated sub-scripts; `atLeast` counts each copy separately, so one signature can count more than once"]
     else []) ++ children path ss
  | .before 0 => [s!"{path}: `before 0` can never be satisfied"]
  | _ => []
  children (path : String) (ss : List Script) : List String :=
    (ss.zipIdx.map fun (s, i) => lintNode s!"{path}.{i}" s).flatten

def lint (s : Script) : List String :=
  lintNode "root" s ++
    (match minSigners s with
     | none => ["the script can never be satisfied by any transaction"]
     | some 0 => ["the script can be satisfied with NO signatures (inside its time window): anyone can spend/mint"]
     | _ => [])

end NativeScript
