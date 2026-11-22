import NativeScript.Dnf

/-!
# Analyses

The questions the CLI answers, each defined from the normal form and specified
directly against `Satisfies`.
-/

namespace NativeScript

/-! ## Witnesses

Every clause of the normal form can be met by a real transaction: sign with its
keys, and use its time bounds as the validity interval. This turns `dnf_sound`
into existence statements.

Note for `omega`: it does not see through `abbrev Slot := Nat`, so goals over
`Slot` go to `grind` instead.
-/


/-- The interval `[lo, hi)` read off a clause, with the lower bound always set. -/
def Clause.interval (c : Clause) : Interval :=
  { invalidBefore := some (c.lo.getD 0), invalidHereafter := c.hi }

theorem Clause.interval_valid {c : Clause} (h : c.feasible = true) : c.interval.Valid := by
  obtain ⟨k, lo, hi⟩ := c
  cases hi <;> simp_all [Clause.interval, Interval.Valid, Clause.feasible]

theorem Clause.holds_of_subset {c : Clause} {ks : List KeyHash} (h : ∀ k ∈ c.keys, k ∈ ks) :
    c.Holds ⟨ks, c.interval⟩ := by
  obtain ⟨k, lo, hi⟩ := c
  refine ⟨h, ?_, ?_⟩
  · cases lo <;> simp [Clause.interval, LoOk]
  · cases hi <;> simp [Clause.interval, HiOk]

theorem dnf_witness {s : Script} {c : Clause} (hc : c ∈ dnf s) {ks : List KeyHash}
    (h : ∀ k ∈ c.keys, k ∈ ks) : c.interval.Valid ∧ Satisfies ⟨ks, c.interval⟩ s :=
  ⟨Clause.interval_valid (dnf_feasible hc), dnf_sound hc (Clause.holds_of_subset h)⟩

theorem dnf_eq_nil_iff (s : Script) :
    dnf s = [] ↔ ∀ env : Env, env.validity.Valid → ¬ Satisfies env s := by
  constructor
  · intro h env hv hs
    obtain ⟨c, hc, -⟩ := dnf_complete hv hs
    simp [h] at hc
  · intro h
    match hd : dnf s with
    | [] => rfl
    | c :: _ =>
      have hc : c ∈ dnf s := by simp [hd]
      obtain ⟨hv, hs⟩ := dnf_witness hc (ks := c.keys) (fun _ h => h)
      exact absurd hs (h _ hv)

/-! ## Minimum number of signers -/

/-- The fewest distinct keys that can satisfy the script, or `none` if no
transaction can ever satisfy it. -/
def minSigners (s : Script) : Option Nat :=
  ((dnf s).map (·.keys.length)).min?

theorem minSigners_none_iff (s : Script) :
    minSigners s = none ↔ ∀ env : Env, env.validity.Valid → ¬ Satisfies env s := by
  rw [minSigners, List.min?_eq_none_iff, List.map_eq_nil_iff, dnf_eq_nil_iff]

/-- The bound is attained. -/
theorem minSigners_sound {s : Script} {n : Nat} (h : minSigners s = some n) :
    ∃ env : Env, env.validity.Valid ∧ env.signers.Nodup ∧ env.signers.length = n ∧
      Satisfies env s := by
  have := List.min?_mem h
  simp only [List.mem_map] at this
  obtain ⟨c, hc, rfl⟩ := this
  obtain ⟨hv, hs⟩ := dnf_witness hc (ks := c.keys) (fun _ h => h)
  exact ⟨⟨c.keys, c.interval⟩, hv, dnf_keys_nodup hc, rfl, hs⟩

/-- No smaller set of signers works. (The `Nodup` hypothesis turns out not to be
needed: the bound holds for any list of signers.) -/
theorem minSigners_optimal {s : Script} {n : Nat} {env : Env} (h : minSigners s = some n)
    (hv : env.validity.Valid) (_hnd : env.signers.Nodup) (hs : Satisfies env s) :
    n ≤ env.signers.length := by
  obtain ⟨c, hc, hh⟩ := dnf_complete hv hs
  have hmin := (List.min?_eq_some_iff.mp h).2 c.keys.length (List.mem_map_of_mem hc)
  have := (dnf_keys_nodup hc).length_le_of_subset (fun k hk => hh.1 k hk)
  omega


/-! ## Minimal signer sets -/

def subsetOf (a b : List KeyHash) : Bool := a.all (b.contains ·)

theorem subsetOf_iff {a b : List KeyHash} : subsetOf a b = true ↔ ∀ k ∈ a, k ∈ b := by
  simp [subsetOf]

theorem subsetOf_refl (a : List KeyHash) : subsetOf a a = true := subsetOf_iff.mpr fun _ h => h

theorem subsetOf_trans {a b c : List KeyHash} (hab : subsetOf a b = true)
    (hbc : subsetOf b c = true) : subsetOf a c = true :=
  subsetOf_iff.mpr fun k hk => subsetOf_iff.mp hbc k (subsetOf_iff.mp hab k hk)

def sortKeys (ks : List KeyHash) : List KeyHash := ks.mergeSort (fun a b => decide (a ≤ b))

def signerStep (acc : List (List KeyHash)) (ks : List KeyHash) : List (List KeyHash) :=
  if acc.any (subsetOf · ks) then acc else ks :: acc.filter (fun d => !subsetOf ks d)

/-- The key sets that can satisfy the script (with a suitable validity
interval) and that have no proper subset that also can, sorted. -/
def signerSets (s : Script) : List (List KeyHash) :=
  (((dnf s).map fun c => sortKeys c.keys).foldl signerStep []).reverse

theorem signerSets_eq (s : Script) :
    signerSets s = (((dnf s).map fun c => sortKeys c.keys).foldl signerStep []).reverse := rfl

theorem signerStep_subset {acc : List (List KeyHash)} {ks d : List KeyHash}
    (h : d ∈ signerStep acc ks) : d ∈ acc ∨ d = ks := by
  unfold signerStep at h
  split at h
  · exact .inl h
  · rcases List.mem_cons.mp h with rfl | h
    · exact .inr rfl
    · exact .inl (List.mem_filter.mp h).1

theorem foldl_signerStep_subset :
    ∀ {l acc : List (List KeyHash)} {d : List KeyHash},
      d ∈ l.foldl signerStep acc → d ∈ acc ∨ d ∈ l
  | [], _, _, h => .inl h
  | ks :: l, acc, d, h => by
    rcases foldl_signerStep_subset (l := l) h with h | h
    · rcases signerStep_subset h with h | rfl
      · exact .inl h
      · exact .inr (by simp)
    · exact .inr (by simp [h])

theorem foldl_signerStep_covers :
    ∀ {l acc : List (List KeyHash)} {b : List KeyHash}, (b ∈ acc ∨ b ∈ l) →
      ∃ d ∈ l.foldl signerStep acc, subsetOf d b = true
  | [], _, _, .inl h => ⟨_, h, subsetOf_refl _⟩
  | [], _, _, .inr h => by simp at h
  | ks :: l, acc, b, h => by
    simp only [List.foldl_cons]
    -- after one step, `b` is covered by something in the new accumulator, or is still to come
    have key : ∃ d ∈ signerStep acc ks, subsetOf d b = true ∨ b ∈ l := by
      unfold signerStep
      split
      · rename_i hany
        rcases h with h | h
        · exact ⟨b, h, .inl (subsetOf_refl b)⟩
        · rcases List.mem_cons.mp h with rfl | h
          · obtain ⟨d, hd, hdb⟩ := List.any_eq_true.mp hany
            exact ⟨d, hd, .inl hdb⟩
          · obtain ⟨d, hd, -⟩ := List.any_eq_true.mp hany
            exact ⟨d, hd, .inr h⟩
      · have hks : ks ∈ ks :: acc.filter (fun d => !subsetOf ks d) := by simp
        rcases h with h | h
        · by_cases hkb : subsetOf ks b = true
          · exact ⟨ks, hks, .inl hkb⟩
          · exact ⟨b, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨h, by simpa using hkb⟩),
              .inl (subsetOf_refl b)⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨b, hks, .inl (subsetOf_refl b)⟩
          · exact ⟨ks, hks, .inr h⟩
    obtain ⟨d, hd, hdb | hbl⟩ := key
    · obtain ⟨e, he, hed⟩ := foldl_signerStep_covers (l := l) (.inl hd)
      exact ⟨e, he, subsetOf_trans hed hdb⟩
    · exact foldl_signerStep_covers (.inr hbl)

/-- No set in the accumulator is a subset of a different one. -/
def Antichain (acc : List (List KeyHash)) : Prop :=
  ∀ a ∈ acc, ∀ b ∈ acc, subsetOf a b = true → a = b

theorem signerStep_antichain {acc : List (List KeyHash)} (ks : List KeyHash)
    (h : Antichain acc) : Antichain (signerStep acc ks) := by
  unfold signerStep
  split
  · exact h
  · rename_i hany
    simp only [Bool.not_eq_true, List.any_eq_false] at hany
    intro a ha b hb hab
    simp only [List.mem_cons, List.mem_filter, Bool.not_eq_true'] at ha hb
    rcases ha with rfl | ⟨ha, hka⟩ <;> rcases hb with rfl | ⟨hb, hkb⟩
    · rfl
    · simp [hab] at hkb
    · exact absurd hab (by simpa using hany a ha)
    · exact h a ha b hb hab

theorem foldl_signerStep_antichain :
    ∀ {l acc : List (List KeyHash)}, Antichain acc → Antichain (l.foldl signerStep acc)
  | [], _, h => h
  | ks :: l, _, h => foldl_signerStep_antichain (l := l) (signerStep_antichain ks h)

theorem mem_signerSets {s : Script} {ks : List KeyHash} (h : ks ∈ signerSets s) :
    ∃ c ∈ dnf s, ks = sortKeys c.keys := by
  rw [signerSets_eq, List.mem_reverse] at h
  rcases foldl_signerStep_subset h with h | h
  · simp at h
  · simpa [eq_comm] using h

theorem signerSets_sound {s : Script} {ks : List KeyHash} (h : ks ∈ signerSets s) :
    ∃ i : Interval, i.Valid ∧ Satisfies ⟨ks, i⟩ s := by
  obtain ⟨c, hc, rfl⟩ := mem_signerSets h
  exact ⟨c.interval, dnf_witness hc (fun k hk => by simpa [sortKeys] using hk)⟩

theorem signerSets_complete {s : Script} {env : Env} (hv : env.validity.Valid)
    (hs : Satisfies env s) : ∃ ks ∈ signerSets s, ∀ k ∈ ks, k ∈ env.signers := by
  obtain ⟨c, hc, hh⟩ := dnf_complete hv hs
  obtain ⟨ks, hks, hsub⟩ := foldl_signerStep_covers (acc := [])
    (l := (dnf s).map fun c => sortKeys c.keys) (b := sortKeys c.keys)
    (.inr (List.mem_map_of_mem hc))
  refine ⟨ks, by rw [signerSets_eq, List.mem_reverse]; exact hks, fun k hk => ?_⟩
  have := subsetOf_iff.mp hsub k hk
  exact hh.1 k (by simpa [sortKeys] using this)

/-- The result is an antichain: no set in it contains another. -/
theorem signerSets_minimal {s : Script} {ks ks' : List KeyHash}
    (h : ks ∈ signerSets s) (h' : ks' ∈ signerSets s) (hsub : ∀ k ∈ ks', k ∈ ks) :
    ks = ks' := by
  rw [signerSets_eq, List.mem_reverse] at h h'
  have := foldl_signerStep_antichain (l := (dnf s).map fun c => sortKeys c.keys)
    (acc := []) (by simp [Antichain])
  exact (this ks' h' ks h (subsetOf_iff.mpr hsub)).symm


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


/-- The one-slot interval `[t, t+1)`. -/
def Interval.at (t : Slot) : Interval := { invalidBefore := some t, invalidHereafter := some (t + 1) }

theorem Interval.at_valid (t : Slot) : (Interval.at t).Valid := by
  simp [Interval.at, Interval.Valid]

theorem Interval.at_contains (t : Slot) : (Interval.at t).Contains t := by
  simp [Interval.at, Interval.Contains]

theorem Clause.window_of_holds {env : Env} {c : Clause} {t : Slot} (h : c.Holds env)
    (ht : env.validity.Contains t) : c.window.Contains t := by
  obtain ⟨-, hlo, hhi⟩ := h
  obtain ⟨k, lo, hi⟩ := c
  obtain ⟨signers, ib, ih⟩ := env
  simp only [Interval.Contains] at ht
  simp only [Clause.window, Window.Contains]
  simp only at hlo hhi
  cases lo <;> cases hi <;> cases ib <;> cases ih <;> simp_all [LoOk, HiOk] <;> grind

theorem Clause.holds_at {c : Clause} {t : Slot} {ks : List KeyHash} (hw : c.window.Contains t)
    (hk : ∀ k ∈ c.keys, k ∈ ks) : c.Holds ⟨ks, Interval.at t⟩ := by
  obtain ⟨k, lo, hi⟩ := c
  simp only [Clause.window, Window.Contains] at hw
  refine ⟨hk, ?_, ?_⟩
  · cases lo <;> simp_all [Interval.at, LoOk]
  · cases hi <;> simp_all [Interval.at, HiOk] <;> grind

theorem windowsFor_spec (keys : List KeyHash) (s : Script) (t : Slot) :
    (∃ i : Interval, i.Valid ∧ i.Contains t ∧ Satisfies ⟨keys, i⟩ s) ↔
      ∃ w ∈ windowsFor keys s, w.Contains t := by
  simp only [windowsFor, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨i, hv, ht, hs⟩
    obtain ⟨c, hc, hh⟩ := dnf_complete hv hs
    exact ⟨c.window, ⟨c, ⟨hc, subsetOf_iff.mpr hh.1⟩, rfl⟩, Clause.window_of_holds hh ht⟩
  · rintro ⟨w, ⟨c, ⟨hc, hk⟩, rfl⟩, hw⟩
    exact ⟨Interval.at t, Interval.at_valid t, Interval.at_contains t,
      dnf_sound hc (Clause.holds_at hw (subsetOf_iff.mp hk))⟩

/-- A transaction applied at slot `t` can satisfy `s` exactly when `t` is in one
of its windows. The `←` direction picks the interval `[t, t+1)`. -/
theorem windows_spec (s : Script) (t : Slot) :
    (∃ env : Env, env.validity.Valid ∧ env.validity.Contains t ∧ Satisfies env s) ↔
      ∃ w ∈ windows s, w.Contains t := by
  simp only [windows, List.mem_map]
  constructor
  · rintro ⟨env, hv, ht, hs⟩
    obtain ⟨c, hc, hh⟩ := dnf_complete hv hs
    exact ⟨c.window, ⟨c, hc, rfl⟩, Clause.window_of_holds hh ht⟩
  · rintro ⟨w, ⟨c, hc, rfl⟩, hw⟩
    exact ⟨⟨c.keys, Interval.at t⟩, Interval.at_valid t, Interval.at_contains t,
      dnf_sound hc (Clause.holds_at hw fun _ h => h)⟩

/-- One step of `mergeWindows`: add `w` (whose start is at least that of every
window so far) to the merged windows, newest first. -/
def mergeStep (acc : List Window) (w : Window) : List Window :=
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
      else w :: p :: rest

/-- Sort by start slot, then merge windows that overlap or touch. -/
def mergeWindows (ws : List Window) : List Window :=
  ((ws.mergeSort (fun a b => decide (a.start ≤ b.start))).foldl mergeStep []).reverse

/-! ### Merging windows -/

theorem mergeStep_starts {acc : List Window} {w : Window}
    (hacc : ∀ p ∈ acc, p.start ≤ w.start) : ∀ x ∈ mergeStep acc w, x.start ≤ w.start := by
  unfold mergeStep
  split
  · simp
  · rename_i p rest
    split
    · exact hacc
    · split
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hacc p (by simp)
        · exact hacc x (by simp [hx])
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact hacc x hx

theorem mergeStep_spec {acc : List Window} {w : Window} (t : Slot)
    (hacc : ∀ p ∈ acc, p.start ≤ w.start) :
    (∃ x ∈ mergeStep acc w, x.Contains t) ↔ (∃ x ∈ acc, x.Contains t) ∨ w.Contains t := by
  cases acc with
  | nil => simp [mergeStep]
  | cons p rest =>
    have hp := hacc p (by simp)
    obtain ⟨ps, pstop⟩ := p
    obtain ⟨ws, wstop⟩ := w
    simp only at hp
    cases pstop with
    | none =>
      simp only [mergeStep, List.mem_cons, or_and_right, exists_or, exists_eq_left]
      have : Window.Contains ⟨ws, wstop⟩ t → Window.Contains ⟨ps, none⟩ t := by
        cases wstop <;> simp [Window.Contains] <;> grind
      constructor
      · exact .inl
      · rintro (h | h)
        · exact h
        · exact .inl (this h)
    | some e =>
      by_cases hle : ws ≤ e
      · simp only [mergeStep, hle, ite_true, List.mem_cons, or_and_right, exists_or, exists_eq_left]
        cases wstop <;> simp [Window.Contains] <;> grind
      · simp only [mergeStep, hle, ite_false, List.mem_cons, or_and_right, exists_or, exists_eq_left]
        constructor
        · rintro (h | h)
          · exact .inr h
          · exact .inl h
        · rintro (h | h)
          · exact .inr h
          · exact .inl h

theorem foldl_mergeStep_spec (t : Slot) :
    ∀ {l acc : List Window}, (∀ p ∈ acc, ∀ w ∈ l, p.start ≤ w.start) →
      l.Pairwise (fun a b => a.start ≤ b.start) →
      ((∃ x ∈ l.foldl mergeStep acc, x.Contains t) ↔
        (∃ x ∈ acc, x.Contains t) ∨ ∃ x ∈ l, x.Contains t)
  | [], _, _, _ => by simp
  | w :: l, acc, hacc, hsorted => by
    simp only [List.pairwise_cons] at hsorted
    obtain ⟨hw, hl⟩ := hsorted
    have hacc_w : ∀ p ∈ acc, p.start ≤ w.start := fun p hp => hacc p hp w (by simp)
    have hacc' : ∀ p ∈ mergeStep acc w, ∀ w' ∈ l, p.start ≤ w'.start :=
      fun p hp w' hw' => Nat.le_trans (mergeStep_starts hacc_w p hp) (hw w' hw')
    rw [List.foldl_cons, foldl_mergeStep_spec t hacc' hl, mergeStep_spec t hacc_w]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h

theorem mergeWindows_spec (ws : List Window) (t : Slot) :
    (∃ w ∈ mergeWindows ws, w.Contains t) ↔ ∃ w ∈ ws, w.Contains t := by
  have hsorted := List.pairwise_mergeSort (le := fun a b : Window => decide (a.start ≤ b.start))
    (by intro a b c; simp only [decide_eq_true_eq]; exact Nat.le_trans)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) ws
  simp only [mergeWindows, List.mem_reverse]
  rw [foldl_mergeStep_spec t (by simp) (hsorted.imp (by simp))]
  simp

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
