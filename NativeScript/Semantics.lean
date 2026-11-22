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

theorem count_map_eq {α : Type} (p : α → Bool) (l : List α) :
    (l.map p).count true = (l.filter p).length := by
      induction l with
        | nil => rfl
        | cons head tail ih => cases h : p head <;> simp [h, ih]

/--
If a proposition p holds true for n elements of a list, there there is a sublist
of length n where the proposition is identically true.
-/
theorem count_sublist {α : Type} (p : α → Bool) (n : Nat) (l : List α) :
    n ≤ (l.map p).count true ↔
      ∃ sub : List α, sub.Sublist l ∧ n ≤ sub.length ∧ ∀ x ∈ sub, p x = true := by
  constructor
  · intro h
    refine ⟨l.filter p, ?_, ?_, ?_⟩
    · exact List.filter_sublist
    · rw [<-count_map_eq]; exact h
    · intro x hx; exact (List.mem_filter.mp hx).2
  · intro ⟨sub, hsub, hlen, hall⟩
    have h1 : (sub.map p).count true = sub.length := by
      rw [count_map_eq]
      exact List.length_filter_eq_length_iff.mpr hall
    have h2 : (sub.map p).count true ≤ (l.map p).count true := (hsub.map p).count_le true
    omega

mutual
/-- **Implementation meets spec.** `eval`, which follows the ledger's
`evalTimelock`, agrees with the declarative `Satisfies` on every script. -/
theorem eval_iff (env : Env) : (s : Script) -> (eval env s = true ↔ Satisfies env s)
  | .sig k => by
    simp [eval]
    constructor
    · exact .sig
    · intro h; cases h with
      | sig h1 => exact h1
  | .all ss => by
    have ih := evalList_iff env ss
    constructor
    · intro h; simp [eval, evalList_eq_map] at h
      apply Satisfies.all
      intro s hs
      exact (ih s hs).mp (h s hs)
    · intro h; cases h with
      | all h1 =>
        simp [eval, evalList_eq_map]
        intro s hs
        exact (ih s hs).mpr (h1 s hs)
  | .any ss => by
    have ih := evalList_iff env ss
    constructor
    · intro h; simp [eval, evalList_eq_map] at h
      obtain ⟨s, hs, he⟩ := h
      have t :=  (ih s hs).mp he
      exact Satisfies.any s hs t
    · intro h; simp [eval, evalList_eq_map]
      cases h with
      | any s hs hx =>
        exact ⟨s, hs, (ih s hs).mpr hx⟩
  | .atLeast n ss => by
    have ih := evalList_iff env ss
    constructor
    · intro h; simp [eval, evalList_eq_map] at h
      obtain ⟨sub, hsub, hlen, hall⟩ := (count_sublist _ _ _).mp h
      have f : ∀ s ∈ sub, Satisfies env s :=
        fun s hs => (ih s (hsub.mem hs)).mp (hall s hs)
      exact .atLeast sub hsub hlen f
    · intro h; cases h with
      | atLeast sub hsub hlen hall =>
        simp [eval, evalList_eq_map]
        exact (count_sublist _ n _).mpr
          ⟨sub, hsub, hlen, fun s hs => (ih s (hsub.mem hs)).mpr (hall s hs)⟩
  | .after t => by
    constructor
    · intro h
      cases p : env.validity.invalidBefore with
      | some b0 => simp [eval, p] at h; exact .after p h
      | none => simp [eval, p] at h
    . intro h
      cases h with
      | @after t lo ht hlo =>
        simp [eval, ht]
        exact hlo
  | .before t => by
    constructor
    · intro h
      cases p : env.validity.invalidHereafter with
      | some b0 => simp [eval, p] at h; exact .before p h
      | none => simp [eval, p] at h
    . intro h
      cases h with
      | before ht hlo =>
        simp [eval, ht]
        exact hlo

theorem evalList_iff (env : Env) :
    (ss : List Script) → ∀ s ∈ ss, (eval env s = true ↔ Satisfies env s)
  | [] => by simp
  | s :: ss => by
    have hhd : eval env s = true ↔ Satisfies env s := eval_iff env s
    have htl : ∀ s1 ∈ ss, (eval env s1 = true ↔ Satisfies env s1) := evalList_iff env ss
    intro h hx
    simp at hx
    rcases hx with rfl | hx
    · exact hhd
    · exact (htl _ hx)

end

instance (env : Env) (s : Script) : Decidable (Satisfies env s) :=
  decidable_of_iff _ (eval_iff env s)

/-- More signers never hurt. -/
theorem Satisfies.mono_signers {env env' : Env} {s : Script}
  (hsub : ∀ k ∈ env.signers, k ∈ env'.signers) (hval : env.validity = env'.validity)
  (h : Satisfies env s) : Satisfies env' s := by
    induction h with
      | sig hk => exact (.sig <| hsub _ hk)
      | all _ ih => exact (.all ih)
      | any s hs _ ih => exact (.any s hs ih)
      | atLeast sub hsl hlen _ ih =>
        exact (.atLeast sub hsl hlen ih)
      | @after t lo ht hlo =>
        have ht' : env'.validity.invalidBefore = some lo := by
          rw [<-hval]
          exact ht
        exact (.after ht' hlo)
      | before ht hhi =>
        /- This does the same as the 'after' proof above, in abbreviated form -/
        exact (.before (hval ▸ ht) hhi)
end NativeScript
