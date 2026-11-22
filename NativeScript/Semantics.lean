import NativeScript.Syntax

/-!
# Semantics

`Satisfies` is the specification: a declarative relation written to be read
next to the ledger spec. `eval` is the implementation: it follows the ledger's
`evalTimelock`. `eval_iff` connects the two, which gives a `Decidable` instance,
so `decide (Satisfies env s)` runs the spec.
-/

namespace NativeScript

/-- The declarative semantics of native scripts.

Time locks are judged against the transaction's validity interval, not a slot:
`after t` needs a lower bound that is present and `≥ t`, and `before t` needs an
upper bound that is present and `≤ t`. An absent bound never satisfies a time
lock, so `after 0` is not trivially true. -/
inductive Satisfies (env : Env) : Script → Prop where
  | sig {k : KeyHash} :
      k ∈ env.signers → Satisfies env (.sig k)
  | all {ss : List Script} :
      (∀ s ∈ ss, Satisfies env s) → Satisfies env (.all ss)
  | any {ss : List Script} (s : Script) :
      s ∈ ss → Satisfies env s → Satisfies env (.any ss)
  | atLeast {n : Nat} {ss : List Script} (sub : List Script) :
      sub.Sublist ss → n ≤ sub.length → (∀ s ∈ sub, Satisfies env s) →
      Satisfies env (.atLeast n ss)
  | after {t lo : Slot} :
      env.validity.invalidBefore = some lo → t ≤ lo → Satisfies env (.after t)
  | before {t hi : Slot} :
      env.validity.invalidHereafter = some hi → hi ≤ t → Satisfies env (.before t)

mutual
/-- The executable semantics, following `evalTimelock` in cardano-ledger. -/
def eval (env : Env) : Script → Bool
  | .sig k => env.signers.contains k
  | .all ss => (evalList env ss).all id
  | .any ss => (evalList env ss).any id
  | .atLeast n ss => decide (n ≤ (evalList env ss).count true)
  | .after t =>
    match env.validity.invalidBefore with
    | some lo => decide (t ≤ lo)
    | none => false
  | .before t =>
    match env.validity.invalidHereafter with
    | some hi => decide (hi ≤ t)
    | none => false

def evalList (env : Env) : List Script → List Bool
  | [] => []
  | s :: ss => eval env s :: evalList env ss
end

theorem evalList_eq_map (env : Env) (ss : List Script) :
    evalList env ss = ss.map (eval env) := by
  induction ss with
  | nil => simp [evalList]
  | cons s ss ih => simp [evalList, ih]

/-- **Implementation meets spec.** Prove it with mutual structural recursion
over `Script` / `List Script` (the `induction` tactic doesn't handle nested
inductives), or by strong induction on `sizeOf s`. The `atLeast` case is the
interesting one: counting `true`s versus picking a sublist. -/
theorem eval_iff (env : Env) (s : Script) : eval env s = true ↔ Satisfies env s := by
  sorry

instance (env : Env) (s : Script) : Decidable (Satisfies env s) :=
  decidable_of_iff _ (eval_iff env s)

/-- More signers never hurt. -/
theorem Satisfies.mono_signers {env env' : Env} {s : Script}
    (hsub : ∀ k ∈ env.signers, k ∈ env'.signers) (hval : env.validity = env'.validity)
    (h : Satisfies env s) : Satisfies env' s := by
  sorry

end NativeScript
