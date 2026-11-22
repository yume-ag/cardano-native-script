import NativeScript.Semantics

/-!
# Shared lemmas

* `Script.induct`: an induction principle for `Script` that gives an induction
  hypothesis for every element of a list of sub-scripts. It is proved once, by
  mutual structural recursion as in `eval_iff`, so later proofs can just write
  `induction s using Script.induct`.
* Equations for `eval` on each constructor, stated with `List.map` instead of
  `evalList`. Together with `eval_iff` these let proofs about `Satisfies` be
  done as computations on `Bool`.
-/

namespace NativeScript

mutual
theorem Script.induct {motive : Script → Prop}
    (sig : ∀ k, motive (.sig k))
    (all : ∀ ss, (∀ s ∈ ss, motive s) → motive (.all ss))
    (any : ∀ ss, (∀ s ∈ ss, motive s) → motive (.any ss))
    (atLeast : ∀ n ss, (∀ s ∈ ss, motive s) → motive (.atLeast n ss))
    (after : ∀ t, motive (.after t))
    (before : ∀ t, motive (.before t)) :
    (s : Script) → motive s
  | .sig k => sig k
  | .all ss => all ss (Script.induct_list sig all any atLeast after before ss)
  | .any ss => any ss (Script.induct_list sig all any atLeast after before ss)
  | .atLeast n ss => atLeast n ss (Script.induct_list sig all any atLeast after before ss)
  | .after t => after t
  | .before t => before t

theorem Script.induct_list {motive : Script → Prop}
    (sig : ∀ k, motive (.sig k))
    (all : ∀ ss, (∀ s ∈ ss, motive s) → motive (.all ss))
    (any : ∀ ss, (∀ s ∈ ss, motive s) → motive (.any ss))
    (atLeast : ∀ n ss, (∀ s ∈ ss, motive s) → motive (.atLeast n ss))
    (after : ∀ t, motive (.after t))
    (before : ∀ t, motive (.before t)) :
    (ss : List Script) → ∀ s ∈ ss, motive s
  | [] => by simp
  | s :: ss => by
    have hd := Script.induct sig all any atLeast after before s
    have tl := Script.induct_list sig all any atLeast after before ss
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact tl x hx
end

/-! ## `eval` on each constructor -/

@[simp] theorem eval_sig (env : Env) (k : KeyHash) :
    eval env (.sig k) = env.signers.contains k := by simp [eval]

@[simp] theorem eval_all (env : Env) (ss : List Script) :
    eval env (.all ss) = true ↔ ∀ s ∈ ss, eval env s = true := by
  simp [eval, evalList_eq_map]

@[simp] theorem eval_any (env : Env) (ss : List Script) :
    eval env (.any ss) = true ↔ ∃ s ∈ ss, eval env s = true := by
  simp [eval, evalList_eq_map]

@[simp] theorem eval_atLeast (env : Env) (n : Nat) (ss : List Script) :
    eval env (.atLeast n ss) = true ↔ n ≤ (ss.map (eval env)).count true := by
  simp [eval, evalList_eq_map]

@[simp] theorem eval_after (env : Env) (t : Slot) :
    eval env (.after t) = true ↔ ∃ lo, env.validity.invalidBefore = some lo ∧ t ≤ lo := by
  simp only [eval]
  cases env.validity.invalidBefore <;> simp

@[simp] theorem eval_before (env : Env) (t : Slot) :
    eval env (.before t) = true ↔ ∃ hi, env.validity.invalidHereafter = some hi ∧ hi ≤ t := by
  simp only [eval]
  cases env.validity.invalidHereafter <;> simp

/-- `Satisfies` as a statement about `eval`. -/
theorem satisfies_iff_eval (env : Env) (s : Script) :
    Satisfies env s ↔ eval env s = true := (eval_iff env s).symm

end NativeScript
