import NativeScript.Semantics

/-!
# Simplification

`simplify` rewrites a script into a smaller one with the same meaning. The
rewrites it uses:

* flatten nested `all`-in-`all` and `any`-in-`any`, and drop duplicate children;
* `all []` is true and `any []` is false, and these get propagated;
* `atLeast n`: drop true and false children and adjust `n`; `atLeast 1` becomes
  `any`, `atLeast (length)` becomes `all`, and `n > length` becomes false;
* combine time locks: in an `all`, keep the largest `after` and the smallest
  `before`; in an `any`, keep the smallest `after` and the largest `before`;
* an `all` whose time locks contradict each other (`after a`, `before b` with
  `a ≥ b`), and `before 0`, become false.

The last rule only holds for **valid** intervals. A transaction with
`invalidBefore = 10, invalidHereafter = 5` satisfies `all [after 10, before 5]`
as far as `evalTimelock` is concerned, but no slot lies in that interval, so it
can never be applied. That is why `simplify_sound` assumes `Interval.Valid`.
-/

namespace NativeScript

def trueS : Script := .all []
def falseS : Script := .any []

def Script.isTrue : Script → Bool
  | .all [] => true
  | _ => false

def Script.isFalse : Script → Bool
  | .any [] => true
  | _ => false

/-- Splice the children of nested `all` nodes (this also drops `all []`). -/
def flattenAll : List Script → List Script
  | [] => []
  | .all xs :: ss => xs ++ flattenAll ss
  | s :: ss => s :: flattenAll ss

/-- Splice the children of nested `any` nodes (this also drops `any []`). -/
def flattenAny : List Script → List Script
  | [] => []
  | .any xs :: ss => xs ++ flattenAny ss
  | s :: ss => s :: flattenAny ss

def afterSlots (ss : List Script) : List Slot :=
  ss.filterMap fun | .after t => some t | _ => none

def beforeSlots (ss : List Script) : List Slot :=
  ss.filterMap fun | .before t => some t | _ => none

def nonTime (ss : List Script) : List Script :=
  ss.filter fun | .after _ | .before _ => false | _ => true

/-- Smart constructor for `all`, assuming its children are already simplified. -/
def mkAll (ss : List Script) : Script :=
  let ss := flattenAll ss
  if ss.any Script.isFalse then falseS else
  let lo := (afterSlots ss).max?
  let hi := (beforeSlots ss).min?
  let contradictory := match hi with
    | some h => decide (h ≤ lo.getD 0)
    | none => false
  if contradictory then falseS else
  match (nonTime ss).eraseDups ++ (lo.map .after).toList ++ (hi.map .before).toList with
  | [] => trueS
  | [s] => s
  | ss => .all ss

/-- Smart constructor for `any`, assuming its children are already simplified. -/
def mkAny (ss : List Script) : Script :=
  let ss := flattenAny ss
  if ss.any Script.isTrue then trueS else
  let lo := (afterSlots ss).min?
  let hi := (beforeSlots ss).max?
  match (nonTime ss).eraseDups ++ (lo.map .after).toList ++ (hi.map .before).toList with
  | [] => falseS
  | [s] => s
  | ss => .any ss

/-- Smart constructor for `atLeast`, assuming its children are already
simplified. Duplicates are *not* removed: `atLeast` counts positions. -/
def mkAtLeast (n : Nat) (ss : List Script) : Script :=
  let trues := ss.countP Script.isTrue
  let ss := ss.filter fun s => !s.isTrue && !s.isFalse
  if n ≤ trues then trueS else
  let n := n - trues
  if ss.length < n then falseS
  else if n = 1 then mkAny ss
  else if n = ss.length then mkAll ss
  else .atLeast n ss

mutual
def simplify : Script → Script
  | .all ss => mkAll (simplifyList ss)
  | .any ss => mkAny (simplifyList ss)
  | .atLeast n ss => mkAtLeast n (simplifyList ss)
  | .before 0 => falseS
  | s => s

def simplifyList : List Script → List Script
  | [] => []
  | s :: ss => simplify s :: simplifyList ss
end

/-- **Simplification preserves meaning** for every transaction that could
actually be applied. Prove the smart constructors correct one by one (`mkAll`,
`mkAny`, `mkAtLeast` against `Satisfies` of `.all` / `.any` / `.atLeast`), then
put them together by mutual structural recursion. `omega` handles the time-lock
merging. -/
theorem simplify_sound {env : Env} (hv : env.validity.Valid) (s : Script) :
    Satisfies env (simplify s) ↔ Satisfies env s := by
  sorry

end NativeScript
