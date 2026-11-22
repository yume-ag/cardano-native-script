import NativeScript.Semantics

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

/-! ## Correctness of the normal form -/

theorem choose_spec {α : Type} (n : Nat) (l sub : List α) :
    sub ∈ choose n l ↔ sub.Sublist l ∧ sub.length = n := by
  sorry

theorem dnf_feasible {s : Script} {c : Clause} (h : c ∈ dnf s) : c.feasible = true := by
  sorry

theorem dnf_keys_nodup {s : Script} {c : Clause} (h : c ∈ dnf s) : c.keys.Nodup := by
  sorry

/-- Every clause is a way of satisfying the script. -/
theorem dnf_sound {env : Env} {s : Script} {c : Clause}
    (hc : c ∈ dnf s) (h : c.Holds env) : Satisfies env s := by
  sorry

/-- Every way of satisfying the script with a valid interval is captured by
some clause. Without `Valid` this is false: `before 0` has no clauses, but
`invalidHereafter = some 0` satisfies it. -/
theorem dnf_complete {env : Env} {s : Script}
    (hv : env.validity.Valid) (h : Satisfies env s) : ∃ c ∈ dnf s, c.Holds env := by
  sorry

end NativeScript
