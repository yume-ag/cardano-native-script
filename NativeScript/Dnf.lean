import NativeScript.Lemmas

/-!
# Disjunctive normal form

Every native script is equivalent, on valid intervals, to a disjunction of
*clauses*. A clause is a set of required keys plus at most one lower and one
upper time bound. Each analysis reads off this normal form:

* the minimum number of signers is the smallest clause;
* the minimal signer sets are the clauses' key sets, minimised under `⊆`;
* the slots at which the script can be satisfied are the union of the clauses'
  windows.

The DNF can be exponential in the size of the script (`atLeast k` of `n`
produces `n choose k` clauses). That's fine for real multisigs, but it's the
reason this isn't a decision procedure you'd put inside the ledger.
-/

namespace NativeScript

/-- One way of satisfying a script. -/
structure Clause where
  keys : List KeyHash := []
  /-- The interval must have `invalidBefore = some b` with `lo ≤ b`. -/
  lo : Option Slot := none
  /-- The interval must have `invalidHereafter = some h` with `h ≤ hi`. -/
  hi : Option Slot := none
  deriving Repr, DecidableEq, Inhabited

def LoOk : Option Slot → Option Slot → Prop
  | none, _ => True
  | some l, some b => l ≤ b
  | some _, none => False

def HiOk : Option Slot → Option Slot → Prop
  | none, _ => True
  | some h, some a => a ≤ h
  | some _, none => False

instance (r a : Option Slot) : Decidable (LoOk r a) := by
  unfold LoOk; split <;> infer_instance

instance (r a : Option Slot) : Decidable (HiOk r a) := by
  unfold HiOk; split <;> infer_instance

/-- A transaction meets a clause. -/
def Clause.Holds (env : Env) (c : Clause) : Prop :=
  (∀ k ∈ c.keys, k ∈ env.signers) ∧
  LoOk c.lo env.validity.invalidBefore ∧
  HiOk c.hi env.validity.invalidHereafter

instance (env : Env) (c : Clause) : Decidable (c.Holds env) := by
  unfold Clause.Holds; infer_instance

/-- Some valid interval meets the clause's time bounds. -/
def Clause.feasible (c : Clause) : Bool :=
  match c.hi with
  | none => true
  | some h => decide (c.lo.getD 0 < h)

def maxLo : Option Slot → Option Slot → Option Slot
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

def minHi : Option Slot → Option Slot → Option Slot
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

def Clause.top : Clause := {}

def Clause.conj (a b : Clause) : Clause where
  keys := a.keys ++ b.keys.filter (fun k => !a.keys.contains k)
  lo := maxLo a.lo b.lo
  hi := minHi a.hi b.hi

/-- `d.covers c`: every transaction that meets `c` also meets `d`. -/
def Clause.covers (d c : Clause) : Bool :=
  d.keys.all (c.keys.contains ·) &&
  (match d.lo, c.lo with
    | none, _ => true
    | some a, some b => decide (a ≤ b)
    | some _, none => false) &&
  (match d.hi, c.hi with
    | none, _ => true
    | some a, some b => decide (b ≤ a)
    | some _, none => false)

/-- Drop every clause that another clause covers. -/
def minimize (cs : List Clause) : List Clause :=
  (cs.foldl (fun acc c =>
    if acc.any (·.covers c) then acc
    else c :: acc.filter (fun d => !c.covers d)) []).reverse

/-- Conjunction of a list of disjunctions; infeasible clauses are dropped. -/
def conjAll : List (List Clause) → List Clause
  | [] => [Clause.top]
  | d :: ds =>
    let rest := conjAll ds
    (d.flatMap fun c => rest.map c.conj).filter Clause.feasible

/-- All sublists of length exactly `n`, chosen by position. -/
def choose {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | n + 1, x :: xs => (choose n xs).map (x :: ·) ++ choose (n + 1) xs

mutual
def dnf : Script → List Clause
  | .sig k => [{ keys := [k] }]
  | .after t => [{ lo := some t }]
  | .before t => [{ hi := some t }].filter Clause.feasible
  | .all ss => minimize (conjAll (dnfList ss))
  | .any ss => minimize (dnfList ss).flatten
  | .atLeast n ss => minimize ((choose n (dnfList ss)).flatMap conjAll)

def dnfList : List Script → List (List Clause)
  | [] => []
  | s :: ss => dnf s :: dnfList ss
end

/-! ## Correctness of the normal form

The proofs reason about `eval` rather than `Satisfies`, which `eval_iff`
makes equivalent, and use `Script.induct` for induction over scripts.

Note for `omega`: it does not see through `abbrev Slot := Nat`, so goals over
`Slot` go to `grind` instead.
-/

theorem choose_spec {α : Type} (n : Nat) (l sub : List α) :
    sub ∈ choose n l ↔ sub.Sublist l ∧ sub.length = n := by
  induction l generalizing n sub with
  | nil =>
    cases n with
    | zero => simp [choose]
    | succ n => simp [choose]; intro h; simp_all
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [choose, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨-, h⟩; exact List.length_eq_zero_iff.mp h
    | succ n =>
      simp only [choose, List.mem_append, List.mem_map, ih, List.sublist_cons_iff]
      constructor
      · rintro (⟨r, ⟨hr, hlen⟩, rfl⟩ | ⟨hs, hlen⟩)
        · exact ⟨Or.inr ⟨r, rfl, hr⟩, by simp [hlen]⟩
        · exact ⟨Or.inl hs, hlen⟩
      · rintro ⟨hs | ⟨r, rfl, hr⟩, hlen⟩
        · exact Or.inr ⟨hs, hlen⟩
        · exact Or.inl ⟨r, ⟨hr, by simpa using hlen⟩, rfl⟩

theorem choose_map {α β : Type} (f : α → β) (n : Nat) (l : List α) :
    choose n (l.map f) = (choose n l).map (·.map f) := by
  induction l generalizing n with
  | nil => cases n <;> simp [choose]
  | cons x xs ih => cases n <;> simp [choose, ih, Function.comp_def]

theorem dnfList_eq_map (ss : List Script) : dnfList ss = ss.map dnf := by
  induction ss with
  | nil => simp [dnfList]
  | cons s ss ih => simp [dnfList, ih]

theorem loOk_maxLo (x y z : Option Slot) : LoOk (maxLo x y) z ↔ LoOk x z ∧ LoOk y z := by
  cases x <;> cases y <;> cases z <;> simp [maxLo, LoOk] <;> grind

theorem hiOk_minHi (x y z : Option Slot) : HiOk (minHi x y) z ↔ HiOk x z ∧ HiOk y z := by
  cases x <;> cases y <;> cases z <;> simp [minHi, HiOk] <;> grind

theorem Clause.holds_conj {env : Env} {a b : Clause} :
    (a.conj b).Holds env ↔ a.Holds env ∧ b.Holds env := by
  simp only [Clause.Holds, Clause.conj, loOk_maxLo, hiOk_minHi, List.mem_append, List.mem_filter]
  constructor
  · rintro ⟨hk, ⟨hl1, hl2⟩, ⟨hh1, hh2⟩⟩
    refine ⟨⟨fun k hk' => hk k (.inl hk'), hl1, hh1⟩, fun k hk' => ?_, hl2, hh2⟩
    by_cases hka : k ∈ a.keys
    · exact hk k (.inl hka)
    · exact hk k (.inr ⟨hk', by simpa using hka⟩)
  · rintro ⟨⟨hka, hl1, hh1⟩, ⟨hkb, hl2, hh2⟩⟩
    refine ⟨fun k hk => ?_, ⟨hl1, hl2⟩, ⟨hh1, hh2⟩⟩
    rcases hk with hk | ⟨hk, -⟩
    · exact hka k hk
    · exact hkb k hk

theorem Clause.nodup_conj {a b : Clause} (ha : a.keys.Nodup) (hb : b.keys.Nodup) :
    (a.conj b).keys.Nodup := by
  simp only [Clause.conj, List.nodup_append]
  refine ⟨ha, hb.sublist List.filter_sublist, ?_⟩
  intro x hx y hy hxy
  subst hxy
  simp_all

theorem Clause.holds_feasible {env : Env} {c : Clause} (hv : env.validity.Valid)
    (h : c.Holds env) : c.feasible = true := by
  obtain ⟨-, hlo, hhi⟩ := h
  obtain ⟨keys, lo, hi⟩ := c
  obtain ⟨signers, ⟨ib, ih⟩⟩ := env
  simp only [Interval.Valid] at hv
  simp only [Clause.feasible]
  simp only at hlo hhi
  cases lo <;> cases hi <;> cases ib <;> cases ih <;> simp_all [LoOk, HiOk]
  all_goals grind


/-! ### `conjAll` -/

theorem conjAll_sound {env : Env} :
    ∀ {ds : List (List Clause)} {c : Clause}, c ∈ conjAll ds → c.Holds env →
      ∀ d ∈ ds, ∃ c' ∈ d, c'.Holds env
  | [], _, _, _ => by simp
  | d :: ds, c, hc, h => by
    simp only [conjAll, List.mem_filter, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨⟨a, ha, b, hb, rfl⟩, -⟩ := hc
    obtain ⟨h1, h2⟩ := Clause.holds_conj.mp h
    intro d' hd'
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact ⟨a, ha, h1⟩
    · exact conjAll_sound hb h2 d' hd'

theorem conjAll_complete {env : Env} (hv : env.validity.Valid) :
    ∀ {ds : List (List Clause)}, (∀ d ∈ ds, ∃ c' ∈ d, c'.Holds env) →
      ∃ c ∈ conjAll ds, c.Holds env
  | [], _ => ⟨Clause.top, by simp [conjAll], by simp [Clause.top, Clause.Holds, LoOk, HiOk]⟩
  | d :: ds, h => by
    obtain ⟨a, ha, hha⟩ := h d (by simp)
    obtain ⟨b, hb, hhb⟩ := conjAll_complete hv (ds := ds) (fun d' hd' => h d' (by simp [hd']))
    have hab := Clause.holds_conj.mpr ⟨hha, hhb⟩
    refine ⟨a.conj b, ?_, hab⟩
    simp only [conjAll, List.mem_filter, List.mem_flatMap, List.mem_map]
    exact ⟨⟨a, ha, b, hb, rfl⟩, Clause.holds_feasible hv hab⟩

theorem conjAll_good :
    ∀ {ds : List (List Clause)}, (∀ d ∈ ds, ∀ c ∈ d, c.keys.Nodup) →
      ∀ c ∈ conjAll ds, c.feasible = true ∧ c.keys.Nodup
  | [], _ => by simp [conjAll, Clause.top, Clause.feasible]
  | d :: ds, h => by
    intro c hc
    simp only [conjAll, List.mem_filter, List.mem_flatMap, List.mem_map] at hc
    obtain ⟨⟨a, ha, b, hb, rfl⟩, hf⟩ := hc
    refine ⟨hf, Clause.nodup_conj (h d (by simp) a ha) ?_⟩
    exact (conjAll_good (ds := ds) (fun d' hd' => h d' (by simp [hd'])) b hb).2

/-! ### `covers` and `minimize` -/

theorem Clause.covers_refl (c : Clause) : c.covers c = true := by
  obtain ⟨keys, lo, hi⟩ := c
  cases lo <;> cases hi <;> simp [Clause.covers]

theorem Clause.covers_trans {a b c : Clause} (hab : a.covers b = true) (hbc : b.covers c = true) :
    a.covers c = true := by
  obtain ⟨ak, al, ah⟩ := a
  obtain ⟨bk, bl, bh⟩ := b
  obtain ⟨ck, cl, ch⟩ := c
  simp only [Clause.covers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at *
  obtain ⟨⟨hk1, hl1⟩, hh1⟩ := hab
  obtain ⟨⟨hk2, hl2⟩, hh2⟩ := hbc
  refine ⟨⟨fun k hk => hk2 k (hk1 k hk), ?_⟩, ?_⟩
  · revert hl1 hl2; cases al <;> cases bl <;> cases cl <;> simp <;> grind
  · revert hh1 hh2; cases ah <;> cases bh <;> cases ch <;> simp <;> grind

theorem Clause.covers_holds {env : Env} {d c : Clause} (hdc : d.covers c = true)
    (h : c.Holds env) : d.Holds env := by
  obtain ⟨dk, dl, dh⟩ := d
  obtain ⟨ck, cl, ch⟩ := c
  obtain ⟨hk, hl, hh⟩ := h
  simp only [Clause.covers, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hdc
  obtain ⟨⟨hk', hl'⟩, hh'⟩ := hdc
  refine ⟨fun k hk'' => hk k (hk' k hk''), ?_, ?_⟩
  · revert hl hl'; simp only
    cases dl <;> cases cl <;> cases env.validity.invalidBefore <;> simp [LoOk] <;> grind
  · revert hh hh'; simp only
    cases dh <;> cases ch <;> cases env.validity.invalidHereafter <;> simp [HiOk] <;> grind

/-- One step of `minimize`. -/
def minimizeStep (acc : List Clause) (c : Clause) : List Clause :=
  if acc.any (·.covers c) then acc else c :: acc.filter (fun d => !c.covers d)

theorem minimize_eq (cs : List Clause) : minimize cs = (cs.foldl minimizeStep []).reverse := rfl

theorem minimizeStep_subset {acc : List Clause} {c d : Clause} (h : d ∈ minimizeStep acc c) :
    d ∈ acc ∨ d = c := by
  unfold minimizeStep at h
  split at h
  · exact .inl h
  · rcases List.mem_cons.mp h with rfl | h
    · exact .inr rfl
    · exact .inl (List.mem_filter.mp h).1

theorem minimizeStep_covers_new (acc : List Clause) (c : Clause) :
    ∃ d ∈ minimizeStep acc c, d.covers c = true := by
  unfold minimizeStep
  split
  · rename_i h; simpa using h
  · exact ⟨c, by simp, Clause.covers_refl c⟩

theorem minimizeStep_covers_old {acc : List Clause} (c : Clause) {b : Clause} (hb : b ∈ acc) :
    ∃ d ∈ minimizeStep acc c, d.covers b = true := by
  unfold minimizeStep
  split
  · exact ⟨b, hb, Clause.covers_refl b⟩
  · by_cases hcb : c.covers b = true
    · exact ⟨c, by simp, hcb⟩
    · exact ⟨b, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hb, by simpa using hcb⟩),
        Clause.covers_refl b⟩

theorem foldl_minimizeStep_subset :
    ∀ {cs acc : List Clause} {d : Clause}, d ∈ cs.foldl minimizeStep acc → d ∈ acc ∨ d ∈ cs
  | [], _, _, h => .inl h
  | c :: cs, acc, d, h => by
    rcases foldl_minimizeStep_subset (cs := cs) h with h | h
    · rcases minimizeStep_subset h with h | rfl
      · exact .inl h
      · exact .inr (by simp)
    · exact .inr (by simp [h])

theorem foldl_minimizeStep_covers :
    ∀ {cs acc : List Clause} {b : Clause}, (b ∈ acc ∨ b ∈ cs) →
      ∃ d ∈ cs.foldl minimizeStep acc, d.covers b = true
  | [], _, _, .inl h => ⟨_, h, Clause.covers_refl _⟩
  | [], _, _, .inr h => by simp at h
  | c :: cs, acc, b, h => by
    simp only [List.foldl_cons]
    have key : ∃ d ∈ minimizeStep acc c, d.covers b = true ∨ b ∈ cs := by
      rcases h with h | h
      · obtain ⟨d, hd, hdb⟩ := minimizeStep_covers_old c h
        exact ⟨d, hd, .inl hdb⟩
      · rcases List.mem_cons.mp h with rfl | h
        · obtain ⟨d, hd, hdb⟩ := minimizeStep_covers_new acc b
          exact ⟨d, hd, .inl hdb⟩
        · obtain ⟨d, hd, -⟩ := minimizeStep_covers_new acc c
          exact ⟨d, hd, .inr h⟩
    obtain ⟨d, hd, hdb | hbcs⟩ := key
    · obtain ⟨e, he, hed⟩ := foldl_minimizeStep_covers (cs := cs) (.inl hd)
      exact ⟨e, he, Clause.covers_trans hed hdb⟩
    · exact foldl_minimizeStep_covers (.inr hbcs)

theorem minimize_subset {cs : List Clause} {d : Clause} (h : d ∈ minimize cs) : d ∈ cs := by
  rw [minimize_eq, List.mem_reverse] at h
  rcases foldl_minimizeStep_subset h with h | h
  · simp at h
  · exact h

theorem minimize_covers {cs : List Clause} {b : Clause} (h : b ∈ cs) :
    ∃ d ∈ minimize cs, d.covers b = true := by
  obtain ⟨d, hd, hdb⟩ := foldl_minimizeStep_covers (acc := []) (.inr h)
  exact ⟨d, by rw [minimize_eq, List.mem_reverse]; exact hd, hdb⟩


/-! ### The normal form -/

theorem mem_dnf_atLeast {n : Nat} {ss : List Script} {c : Clause} :
    c ∈ (choose n (dnfList ss)).flatMap conjAll ↔
      ∃ sub : List Script, sub.Sublist ss ∧ sub.length = n ∧ c ∈ conjAll (sub.map dnf) := by
  simp only [dnfList_eq_map, choose_map, List.flatMap_map, List.mem_flatMap, choose_spec]
  constructor
  · rintro ⟨sub, ⟨h1, h2⟩, h3⟩; exact ⟨sub, h1, h2, h3⟩
  · rintro ⟨sub, h1, h2, h3⟩; exact ⟨sub, ⟨h1, h2⟩, h3⟩

theorem dnf_good (s : Script) : ∀ c ∈ dnf s, c.feasible = true ∧ c.keys.Nodup := by
  induction s using Script.induct with
  | sig k => simp [dnf, Clause.feasible]
  | after t => simp [dnf, Clause.feasible]
  | before t => simp [dnf, Clause.feasible]
  | all ss ih =>
    intro c hc
    simp only [dnf] at hc
    refine conjAll_good ?_ c (minimize_subset hc)
    simp only [dnfList_eq_map, List.mem_map]
    rintro d ⟨s, hs, rfl⟩ c' hc'
    exact (ih s hs c' hc').2
  | any ss ih =>
    intro c hc
    simp only [dnf] at hc
    have hc := minimize_subset hc
    simp only [dnfList_eq_map, List.mem_flatten, List.mem_map] at hc
    obtain ⟨d, ⟨s, hs, rfl⟩, hcd⟩ := hc
    exact ih s hs c hcd
  | atLeast n ss ih =>
    intro c hc
    simp only [dnf] at hc
    obtain ⟨sub, hsub, -, hc⟩ := mem_dnf_atLeast.mp (minimize_subset hc)
    refine conjAll_good ?_ c hc
    simp only [List.mem_map]
    rintro d ⟨s, hs, rfl⟩ c' hc'
    exact (ih s (hsub.subset hs) c' hc').2

theorem dnf_sound_eval {env : Env} (s : Script) :
    ∀ c ∈ dnf s, c.Holds env → eval env s = true := by
  induction s using Script.induct with
  | sig k =>
    intro c hc h
    simp only [dnf, List.mem_singleton] at hc; subst hc
    simpa using h.1 k (by simp)
  | after t =>
    intro c hc h
    simp only [dnf, List.mem_singleton] at hc; subst hc
    obtain ⟨-, hlo, -⟩ := h
    revert hlo; simp only [eval_after]
    cases env.validity.invalidBefore <;> simp [LoOk]
  | before t =>
    intro c hc h
    simp only [dnf, List.mem_filter, List.mem_singleton] at hc; obtain ⟨rfl, -⟩ := hc
    obtain ⟨-, -, hhi⟩ := h
    revert hhi; simp only [eval_before]
    cases env.validity.invalidHereafter <;> simp [HiOk]
  | all ss ih =>
    intro c hc h
    simp only [dnf] at hc
    have hall := conjAll_sound (minimize_subset hc) h
    simp only [dnfList_eq_map, List.mem_map] at hall
    simp only [eval_all]
    intro s hs
    obtain ⟨c', hc', hh⟩ := hall _ ⟨s, hs, rfl⟩
    exact ih s hs c' hc' hh
  | any ss ih =>
    intro c hc h
    simp only [dnf] at hc
    have hc := minimize_subset hc
    simp only [dnfList_eq_map, List.mem_flatten, List.mem_map] at hc
    obtain ⟨d, ⟨s, hs, rfl⟩, hcd⟩ := hc
    exact (eval_any env ss).mpr ⟨s, hs, ih s hs c hcd h⟩
  | atLeast n ss ih =>
    intro c hc h
    simp only [dnf] at hc
    obtain ⟨sub, hsub, hlen, hc⟩ := mem_dnf_atLeast.mp (minimize_subset hc)
    have hall := conjAll_sound hc h
    simp only [List.mem_map] at hall
    rw [eval_atLeast, count_sublist]
    refine ⟨sub, hsub, by omega, fun s hs => ?_⟩
    obtain ⟨c', hc', hh⟩ := hall _ ⟨s, hs, rfl⟩
    exact ih s (hsub.subset hs) c' hc' hh

theorem dnf_complete_eval {env : Env} (hv : env.validity.Valid) (s : Script) :
    eval env s = true → ∃ c ∈ dnf s, c.Holds env := by
  induction s using Script.induct with
  | sig k =>
    intro h
    refine ⟨{ keys := [k] }, by simp [dnf], ?_, by simp [LoOk], by simp [HiOk]⟩
    simpa using h
  | after t =>
    intro h
    obtain ⟨lo, hlo, hle⟩ := (eval_after env t).mp h
    refine ⟨{ lo := some t }, by simp [dnf], by simp, ?_, by simp [HiOk]⟩
    simp [hlo, LoOk, hle]
  | before t =>
    intro h
    obtain ⟨hi, hhi, hle⟩ := (eval_before env t).mp h
    have : 0 < hi := by
      unfold Interval.Valid at hv; rw [hhi] at hv; simp at hv; grind
    refine ⟨{ hi := some t }, ?_, by simp, by simp [LoOk], ?_⟩
    · simp [dnf, Clause.feasible]; grind
    · simp [hhi, HiOk, hle]
  | all ss ih =>
    intro h
    have hall := (eval_all env ss).mp h
    obtain ⟨c, hc, hh⟩ := conjAll_complete hv (ds := dnfList ss) (by
      simp only [dnfList_eq_map, List.mem_map]
      rintro d ⟨s, hs, rfl⟩
      exact ih s hs (hall s hs))
    obtain ⟨d, hd, hdc⟩ := minimize_covers hc
    exact ⟨d, by simpa [dnf] using hd, Clause.covers_holds hdc hh⟩
  | any ss ih =>
    intro h
    obtain ⟨s, hs, he⟩ := (eval_any env ss).mp h
    obtain ⟨c, hc, hh⟩ := ih s hs he
    have hc' : c ∈ (dnfList ss).flatten := by
      simp only [dnfList_eq_map, List.mem_flatten, List.mem_map]
      exact ⟨dnf s, ⟨s, hs, rfl⟩, hc⟩
    obtain ⟨d, hd, hdc⟩ := minimize_covers hc'
    exact ⟨d, by simpa [dnf] using hd, Clause.covers_holds hdc hh⟩
  | atLeast n ss ih =>
    intro h
    rw [eval_atLeast, count_sublist] at h
    obtain ⟨sub, hsub, hlen, hall⟩ := h
    -- shrink the witness to exactly `n` elements
    let sub' := sub.take n
    have hsub' : sub'.Sublist ss := (List.take_sublist n sub).trans hsub
    have hlen' : sub'.length = n := by simp [sub']; omega
    obtain ⟨c, hc, hh⟩ := conjAll_complete hv (ds := sub'.map dnf) (by
      simp only [List.mem_map]
      rintro d ⟨s, hs, rfl⟩
      have hs' : s ∈ sub := (List.take_sublist n sub).subset hs
      exact ih s (hsub.subset hs') (hall s hs'))
    have hc' := mem_dnf_atLeast.mpr ⟨sub', hsub', hlen', hc⟩
    obtain ⟨d, hd, hdc⟩ := minimize_covers hc'
    exact ⟨d, by simpa [dnf] using hd, Clause.covers_holds hdc hh⟩


/-! ### The headline theorems -/

theorem dnf_feasible {s : Script} {c : Clause} (h : c ∈ dnf s) : c.feasible = true :=
  (dnf_good s c h).1

theorem dnf_keys_nodup {s : Script} {c : Clause} (h : c ∈ dnf s) : c.keys.Nodup :=
  (dnf_good s c h).2

/-- Every clause is a way of satisfying the script. -/
theorem dnf_sound {env : Env} {s : Script} {c : Clause}
    (hc : c ∈ dnf s) (h : c.Holds env) : Satisfies env s :=
  (satisfies_iff_eval env s).mpr (dnf_sound_eval s c hc h)

/-- Every way of satisfying the script with a valid interval is captured by
some clause. Without `Valid` this is false: `before 0` has no clauses, but
`invalidHereafter = some 0` satisfies it. -/
theorem dnf_complete {env : Env} {s : Script}
    (hv : env.validity.Valid) (h : Satisfies env s) : ∃ c ∈ dnf s, c.Holds env :=
  dnf_complete_eval hv s ((satisfies_iff_eval env s).mp h)

end NativeScript
