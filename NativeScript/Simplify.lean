import NativeScript.Lemmas

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
/-! ## Correctness

Each smart constructor is proved correct against `eval` (`eval_mkAll`,
`eval_mkAny`, `eval_mkAtLeast`), and `eval_simplify` puts them together by
induction. `eval_iff` turns the result into a statement about `Satisfies`.
-/


variable {env : Env}

@[simp] theorem eval_trueS : eval env trueS = true := by simp [trueS]
@[simp] theorem eval_falseS : eval env falseS = false := by
  have : ¬ (eval env falseS = true) := by simp [falseS]
  simpa using this

theorem Script.eq_of_isTrue {s : Script} (h : s.isTrue = true) : s = trueS := by
  unfold Script.isTrue at h; split at h <;> simp_all [trueS]

theorem Script.eq_of_isFalse {s : Script} (h : s.isFalse = true) : s = falseS := by
  unfold Script.isFalse at h; split at h <;> simp_all [falseS]

theorem all_flattenAll (l : List Script) :
    (∀ x ∈ flattenAll l, eval env x = true) ↔ ∀ x ∈ l, eval env x = true := by
  induction l with
  | nil => simp [flattenAll]
  | cons s ss ih =>
    cases s <;> simp_all [flattenAll, or_imp, forall_and]

theorem any_flattenAny (l : List Script) :
    (∃ x ∈ flattenAny l, eval env x = true) ↔ ∃ x ∈ l, eval env x = true := by
  induction l with
  | nil => simp [flattenAny]
  | cons s ss ih =>
    cases s <;> simp_all [flattenAny, or_and_right, exists_or]

theorem mem_afterSlots {l : List Script} {t : Slot} : t ∈ afterSlots l ↔ .after t ∈ l := by
  simp only [afterSlots, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩; cases a <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

theorem mem_beforeSlots {l : List Script} {t : Slot} : t ∈ beforeSlots l ↔ .before t ∈ l := by
  simp only [beforeSlots, List.mem_filterMap]
  constructor
  · rintro ⟨a, ha, h⟩; cases a <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

/-- Every element of a list is a non-time-lock, an `after` or a `before`. -/
theorem forall_split (l : List Script) (P : Script → Prop) :
    (∀ x ∈ l, P x) ↔ (∀ x ∈ nonTime l, P x) ∧ (∀ t ∈ afterSlots l, P (.after t)) ∧
      (∀ t ∈ beforeSlots l, P (.before t)) := by
  simp only [mem_afterSlots, mem_beforeSlots, nonTime, List.mem_filter]
  constructor
  · intro h; exact ⟨fun x hx => h x hx.1, fun t ht => h _ ht, fun t ht => h _ ht⟩
  · rintro ⟨h1, h2, h3⟩ x hx
    cases x <;> first | exact h2 _ hx | exact h3 _ hx | exact h1 _ ⟨hx, rfl⟩

theorem exists_split (l : List Script) (P : Script → Prop) :
    (∃ x ∈ l, P x) ↔ (∃ x ∈ nonTime l, P x) ∨ (∃ t ∈ afterSlots l, P (.after t)) ∨
      (∃ t ∈ beforeSlots l, P (.before t)) := by
  simp only [mem_afterSlots, mem_beforeSlots, nonTime, List.mem_filter]
  constructor
  · rintro ⟨x, hx, hp⟩
    cases x with
    | after t => exact .inr (.inl ⟨t, hx, hp⟩)
    | before t => exact .inr (.inr ⟨t, hx, hp⟩)
    | _ => exact .inl ⟨_, ⟨hx, rfl⟩, hp⟩
  · rintro (⟨x, ⟨hx, -⟩, hp⟩ | ⟨t, ht, hp⟩ | ⟨t, ht, hp⟩)
    · exact ⟨x, hx, hp⟩
    · exact ⟨_, ht, hp⟩
    · exact ⟨_, ht, hp⟩


/-! ### Combining time locks -/

theorem all_after_max (L : List Slot) :
    (∀ x ∈ (L.max?.map Script.after).toList, eval env x = true) ↔
      ∀ t ∈ L, eval env (.after t) = true := by
  cases h : L.max? with
  | none => simp [List.max?_eq_none_iff.mp h]
  | some m =>
    obtain ⟨hm, hle⟩ := List.max?_eq_some_iff.mp h
    simp only [Option.map_some, Option.toList_some, List.mem_singleton, forall_eq, eval_after]
    constructor
    · rintro ⟨lo, hlo, hmlo⟩ t ht; exact ⟨lo, hlo, Nat.le_trans (hle t ht) hmlo⟩
    · intro h; exact h m hm

theorem all_before_min (L : List Slot) :
    (∀ x ∈ (L.min?.map Script.before).toList, eval env x = true) ↔
      ∀ t ∈ L, eval env (.before t) = true := by
  cases h : L.min? with
  | none => simp [List.min?_eq_none_iff.mp h]
  | some m =>
    obtain ⟨hm, hle⟩ := List.min?_eq_some_iff.mp h
    simp only [Option.map_some, Option.toList_some, List.mem_singleton, forall_eq, eval_before]
    constructor
    · rintro ⟨hi, hhi, hhim⟩ t ht; exact ⟨hi, hhi, Nat.le_trans hhim (hle t ht)⟩
    · intro h; exact h m hm

theorem any_after_min (L : List Slot) :
    (∃ x ∈ (L.min?.map Script.after).toList, eval env x = true) ↔
      ∃ t ∈ L, eval env (.after t) = true := by
  cases h : L.min? with
  | none => simp [List.min?_eq_none_iff.mp h]
  | some m =>
    obtain ⟨hm, hle⟩ := List.min?_eq_some_iff.mp h
    simp only [Option.map_some, Option.toList_some, List.mem_singleton, exists_eq_left, eval_after]
    constructor
    · intro h; exact ⟨m, hm, h⟩
    · rintro ⟨t, ht, lo, hlo, htlo⟩; exact ⟨lo, hlo, Nat.le_trans (hle t ht) htlo⟩

theorem any_before_max (L : List Slot) :
    (∃ x ∈ (L.max?.map Script.before).toList, eval env x = true) ↔
      ∃ t ∈ L, eval env (.before t) = true := by
  cases h : L.max? with
  | none => simp [List.max?_eq_none_iff.mp h]
  | some m =>
    obtain ⟨hm, hle⟩ := List.max?_eq_some_iff.mp h
    simp only [Option.map_some, Option.toList_some, List.mem_singleton, exists_eq_left, eval_before]
    constructor
    · intro h; exact ⟨m, hm, h⟩
    · rintro ⟨t, ht, hi, hhi, hit⟩; exact ⟨hi, hhi, Nat.le_trans hit (hle t ht)⟩

/-- On a valid interval, `after lo` and `before hi` with `hi ≤ lo` can't both hold. -/
theorem not_after_before (hv : env.validity.Valid) {lo : Option Slot} {h : Slot}
    (hle : h ≤ lo.getD 0) (hlo : ∀ l, lo = some l → eval env (.after l) = true)
    (hhi : eval env (.before h) = true) : False := by
  obtain ⟨a, ha, hah⟩ := (eval_before env h).mp hhi
  unfold Interval.Valid at hv
  rw [ha] at hv
  cases lo with
  | none => simp at hle hv; grind
  | some l =>
    obtain ⟨b, hb, hlb⟩ := (eval_after env l).mp (hlo l rfl)
    rw [hb] at hv
    simp at hle hv; grind


/-- The final `match` in `mkAll`/`mkAny`. -/
theorem eval_node_all (R : List Script) :
    eval env (match R with | [] => trueS | [s] => s | ss => .all ss) = true ↔
      ∀ x ∈ R, eval env x = true := by
  split <;> simp_all

theorem eval_node_any (R : List Script) :
    eval env (match R with | [] => falseS | [s] => s | ss => .any ss) = true ↔
      ∃ x ∈ R, eval env x = true := by
  split <;> simp_all

theorem eval_mkAll (hv : env.validity.Valid) (l : List Script) :
    eval env (mkAll l) = true ↔ ∀ x ∈ l, eval env x = true := by
  rw [← all_flattenAll]
  unfold mkAll
  generalize flattenAll l = m
  dsimp only
  have key : (∀ x ∈ (nonTime m).eraseDups ++ ((afterSlots m).max?.map Script.after).toList ++
      ((beforeSlots m).min?.map Script.before).toList, eval env x = true) ↔
      ∀ x ∈ m, eval env x = true := by
    simp only [List.mem_append, or_imp, forall_and, List.mem_eraseDups]
    rw [all_after_max, all_before_min, forall_split m (fun x => eval env x = true)]
    exact and_assoc
  -- if the time locks contradict each other, nothing satisfies `m`
  have contra : ∀ h, (beforeSlots m).min? = some h → h ≤ (afterSlots m).max?.getD 0 →
      ¬ ∀ x ∈ m, eval env x = true := by
    intro h hmin hle hall
    refine not_after_before hv hle (fun l hl => hall _ ?_) (hall _ ?_)
    · exact mem_afterSlots.mp (List.max?_mem hl)
    · exact mem_beforeSlots.mp (List.min?_mem hmin)
  generalize (nonTime m).eraseDups ++ ((afterSlots m).max?.map Script.after).toList ++
    ((beforeSlots m).min?.map Script.before).toList = r at key ⊢
  split
  · -- some child is `any []`
    rename_i hf
    obtain ⟨x, hx, hxf⟩ := List.any_eq_true.mp hf
    have hx' : falseS ∈ m := Script.eq_of_isFalse hxf ▸ hx
    simp only [eval_falseS, Bool.false_eq_true, false_iff]
    intro h
    simpa using h _ hx'
  split
  · rename_i h hmin
    split
    · rename_i hle
      simp only [eval_falseS, Bool.false_eq_true, false_iff]
      exact contra h hmin (by simpa using hle)
    · rw [← key]; clear key; split <;> simp_all
  · simp only [Bool.false_eq_true, ite_false]
    rw [← key]; clear key; split <;> simp_all

theorem eval_mkAny (l : List Script) :
    eval env (mkAny l) = true ↔ ∃ x ∈ l, eval env x = true := by
  rw [← any_flattenAny]
  unfold mkAny
  generalize flattenAny l = m
  dsimp only
  have key : (∃ x ∈ (nonTime m).eraseDups ++ ((afterSlots m).min?.map Script.after).toList ++
      ((beforeSlots m).max?.map Script.before).toList, eval env x = true) ↔
      ∃ x ∈ m, eval env x = true := by
    simp only [List.mem_append, or_and_right, exists_or, List.mem_eraseDups]
    rw [any_after_min, any_before_max, exists_split m (fun x => eval env x = true)]
    exact or_assoc
  generalize (nonTime m).eraseDups ++ ((afterSlots m).min?.map Script.after).toList ++
    ((beforeSlots m).max?.map Script.before).toList = r at key ⊢
  split
  · rename_i ht
    obtain ⟨x, hx, hxt⟩ := List.any_eq_true.mp ht
    simp only [eval_trueS, true_iff]
    exact ⟨x, hx, by rw [Script.eq_of_isTrue hxt]; simp⟩
  · rw [← key]; clear key; split <;> simp_all


/-! ### `atLeast` -/

/-- Splitting the count: `all []` children always count, `any []` never do. -/
theorem count_split (l : List Script) :
    (l.map (eval env)).count true =
      l.countP Script.isTrue +
        ((l.filter fun s => !s.isTrue && !s.isFalse).map (eval env)).count true := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hT : x.isTrue = true
    · have hx := Script.eq_of_isTrue hT
      subst hx
      have h1 : trueS.isTrue = true := rfl
      simp only [List.map_cons, List.count_cons, List.countP_cons, List.filter_cons, h1, ih,
        eval_trueS]
      simp; omega
    · by_cases hF : x.isFalse = true
      · have hx := Script.eq_of_isFalse hF
        subst hx
        have h1 : falseS.isTrue = false := rfl
        have h2 : falseS.isFalse = true := rfl
        simp only [List.map_cons, List.count_cons, List.countP_cons, List.filter_cons, h1, h2, ih,
          eval_falseS]
        simp
      · simp only [Bool.not_eq_true] at hT hF
        simp [ih, hT, hF, List.count_cons]
        omega

theorem one_le_count_iff (f : Script → Bool) (l : List Script) :
    1 ≤ (l.map f).count true ↔ ∃ x ∈ l, f x = true := by
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, List.count_pos_iff]
  simp

theorem count_eq_length_iff (f : Script → Bool) (l : List Script) :
    (l.map f).count true = l.length ↔ ∀ x ∈ l, f x = true := by
  have := List.count_eq_length (a := true) (l := l.map f)
  simp only [List.length_map, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at this
  rw [this]
  exact forall₂_congr fun _ _ => eq_comm

theorem eval_mkAtLeast (hv : env.validity.Valid) (n : Nat) (l : List Script) :
    eval env (mkAtLeast n l) = true ↔ n ≤ (l.map (eval env)).count true := by
  rw [count_split l]
  unfold mkAtLeast
  dsimp only
  generalize l.filter (fun s => !s.isTrue && !s.isFalse) = l'
  generalize l.countP Script.isTrue = T
  have hc : (l'.map (eval env)).count true ≤ l'.length := by
    simpa using List.count_le_length (a := true) (l := l'.map (eval env))
  split
  · simp only [eval_trueS, true_iff]; omega
  split
  · simp only [eval_falseS, Bool.false_eq_true, false_iff]; omega
  split
  · rename_i h1
    rw [eval_mkAny, ← one_le_count_iff]; omega
  split
  · rename_i h2
    rw [eval_mkAll hv, ← count_eq_length_iff]; omega
  · rw [eval_atLeast]; omega

/-! ### `simplify` -/

theorem simplifyList_eq_map (ss : List Script) : simplifyList ss = ss.map simplify := by
  induction ss with
  | nil => simp [simplifyList]
  | cons s ss ih => simp [simplifyList, ih]

theorem eval_before_zero (hv : env.validity.Valid) : eval env (.before 0) = false := by
  have : ¬ eval env (.before 0) = true := by
    rw [eval_before]
    rintro ⟨hi, hhi, hle⟩
    unfold Interval.Valid at hv
    rw [hhi] at hv
    grind
  exact Bool.eq_false_iff.mpr this

theorem eval_simplify (hv : env.validity.Valid) (s : Script) :
    eval env (simplify s) = eval env s := by
  induction s using Script.induct with
  | sig k => simp [simplify]
  | after t => simp [simplify]
  | before t =>
    cases t with
    | zero => simp [simplify, eval_before_zero hv]
    | succ t => simp [simplify]
  | all ss ih =>
    rw [Bool.eq_iff_iff, simplify, simplifyList_eq_map, eval_mkAll hv, eval_all]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun s hs => by rw [ih s hs]
  | any ss ih =>
    rw [Bool.eq_iff_iff, simplify, simplifyList_eq_map, eval_mkAny, eval_any]
    constructor
    · rintro ⟨x, hx, he⟩
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      exact ⟨s, hs, ih s hs ▸ he⟩
    · rintro ⟨s, hs, he⟩
      exact ⟨simplify s, List.mem_map_of_mem hs, (ih s hs).symm ▸ he⟩
  | atLeast n ss ih =>
    rw [Bool.eq_iff_iff, simplify, simplifyList_eq_map, eval_mkAtLeast hv, eval_atLeast,
      List.map_map]
    have : ss.map (eval env ∘ simplify) = ss.map (eval env) :=
      List.map_congr_left (fun s hs => ih s hs)
    rw [this]

/-- **Simplification preserves meaning** for every transaction that could
actually be applied. -/
theorem simplify_sound {env : Env} (hv : env.validity.Valid) (s : Script) :
    Satisfies env (simplify s) ↔ Satisfies env s := by
  rw [satisfies_iff_eval, satisfies_iff_eval, eval_simplify hv]

end NativeScript
