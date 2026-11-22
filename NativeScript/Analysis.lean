import NativeScript.Dnf

/-!
# Analyses

The questions the CLI answers, each defined from the normal form and specified
directly against `Satisfies`.
-/

namespace NativeScript

/-! ## Minimum number of signers -/

/-- The fewest distinct keys that can satisfy the script, or `none` if no
transaction can ever satisfy it. -/
def minSigners (s : Script) : Option Nat :=
  ((dnf s).map (·.keys.length)).min?

theorem minSigners_none_iff (s : Script) :
    minSigners s = none ↔ ∀ env : Env, env.validity.Valid → ¬ Satisfies env s := by
  sorry

/-- The bound is attained. -/
theorem minSigners_sound {s : Script} {n : Nat} (h : minSigners s = some n) :
    ∃ env : Env, env.validity.Valid ∧ env.signers.Nodup ∧ env.signers.length = n ∧
      Satisfies env s := by
  sorry

/-- No smaller set of signers works. -/
theorem minSigners_optimal {s : Script} {n : Nat} {env : Env} (h : minSigners s = some n)
    (hv : env.validity.Valid) (hnd : env.signers.Nodup) (hs : Satisfies env s) :
    n ≤ env.signers.length := by
  sorry

/-! ## Minimal signer sets -/

def subsetOf (a b : List KeyHash) : Bool := a.all (b.contains ·)

/-- The key sets that can satisfy the script (with a suitable validity
interval) and that have no proper subset that also can, sorted. -/
def signerSets (s : Script) : List (List KeyHash) :=
  let sets := (dnf s).map fun c => c.keys.mergeSort (fun a b => decide (a ≤ b))
  (sets.foldl (fun acc ks =>
    if acc.any (subsetOf · ks) then acc
    else ks :: acc.filter (fun d => !subsetOf ks d)) []).reverse

theorem signerSets_sound {s : Script} {ks : List KeyHash} (h : ks ∈ signerSets s) :
    ∃ i : Interval, i.Valid ∧ Satisfies ⟨ks, i⟩ s := by
  sorry

theorem signerSets_complete {s : Script} {env : Env} (hv : env.validity.Valid)
    (hs : Satisfies env s) : ∃ ks ∈ signerSets s, ∀ k ∈ ks, k ∈ env.signers := by
  sorry

/-- The result is an antichain: no set in it contains another. -/
theorem signerSets_minimal {s : Script} {ks ks' : List KeyHash}
    (h : ks ∈ signerSets s) (h' : ks' ∈ signerSets s) (hsub : ∀ k ∈ ks', k ∈ ks) :
    ks = ks' := by
  sorry

/-! ## Time windows -/

/-- A half-open range of slots `[start, stop)`. -/
structure Window where
  start : Slot
  stop : Option Slot
  deriving Repr, DecidableEq, Inhabited

def Window.Contains (w : Window) (t : Slot) : Prop :=
  w.start ≤ t ∧
    match w.stop with
    | none => True
    | some h => t < h

instance (w : Window) (t : Slot) : Decidable (w.Contains t) := by
  unfold Window.Contains; split <;> infer_instance

def Clause.window (c : Clause) : Window := ⟨c.lo.getD 0, c.hi⟩

/-- The slots at which some transaction can satisfy the script. -/
def windows (s : Script) : List Window := (dnf s).map Clause.window

/-- The slots at which a transaction signed by `keys` can satisfy the script. -/
def windowsFor (keys : List KeyHash) (s : Script) : List Window :=
  ((dnf s).filter fun c => subsetOf c.keys keys).map Clause.window

/-- A transaction applied at slot `t` can satisfy `s` exactly when `t` is in one
of its windows. The `←` direction picks the interval `[t, t+1)`. -/
theorem windows_spec (s : Script) (t : Slot) :
    (∃ env : Env, env.validity.Valid ∧ env.validity.Contains t ∧ Satisfies env s) ↔
      ∃ w ∈ windows s, w.Contains t := by
  sorry

theorem windowsFor_spec (keys : List KeyHash) (s : Script) (t : Slot) :
    (∃ i : Interval, i.Valid ∧ i.Contains t ∧ Satisfies ⟨keys, i⟩ s) ↔
      ∃ w ∈ windowsFor keys s, w.Contains t := by
  sorry

/-- Sort by start slot, then merge windows that overlap or touch. -/
def mergeWindows (ws : List Window) : List Window :=
  let sorted := ws.mergeSort (fun a b => decide (a.start ≤ b.start))
  (sorted.foldl (fun acc w =>
    match acc with
    | [] => [w]
    | p :: rest =>
      match p.stop with
      | none => p :: rest
      | some e =>
        if w.start ≤ e then
          let stop := match w.stop with
            | none => none
            | some e' => some (max e e')
          ⟨p.start, stop⟩ :: rest
        else w :: p :: rest) []).reverse

theorem mergeWindows_spec (ws : List Window) (t : Slot) :
    (∃ w ∈ mergeWindows ws, w.Contains t) ↔ ∃ w ∈ ws, w.Contains t := by
  sorry

/-! ## What's missing? -/

/-- For signers who can't satisfy the script: the smallest set of extra keys
that would let them, if any exists. -/
def missingKeys (keys : List KeyHash) (s : Script) : Option (List KeyHash) :=
  let gaps := (dnf s).map fun c => c.keys.filter (fun k => !keys.contains k)
  gaps.foldl (fun best g =>
    match best with
    | none => some g
    | some b => if g.length < b.length then some g else some b) none

end NativeScript
