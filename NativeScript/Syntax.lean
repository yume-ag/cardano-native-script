/-!
# Syntax of Cardano native scripts

The Allegra-era `Timelock` language (still the native-script language in
Conway). Constructor names follow the `cardano-cli` JSON format; the ledger
names are given in the docstrings.
-/

namespace NativeScript

/-- A key hash: 28 bytes, written as 56 lowercase hex characters. -/
abbrev KeyHash := String

abbrev Slot := Nat

inductive Script where
  /-- `RequireSignature`: the transaction is signed by this key. -/
  | sig (keyHash : KeyHash)
  /-- `RequireAllOf`. `all []` is always true. -/
  | all (scripts : List Script)
  /-- `RequireAnyOf`. `any []` is always false. -/
  | any (scripts : List Script)
  /-- `RequireMOf`: at least `required` of the sub-scripts hold. The
  sub-scripts are counted by position, so a repeated sub-script counts twice. -/
  | atLeast (required : Nat) (scripts : List Script)
  /-- `RequireTimeStart` (`invalid_before` in CDDL): the transaction's validity
  interval must have a lower bound `≥ slot`. -/
  | after (slot : Slot)
  /-- `RequireTimeExpire` (`invalid_hereafter` in CDDL): the transaction's
  validity interval must have an upper bound `≤ slot`. -/
  | before (slot : Slot)
  deriving Repr, Inhabited

mutual
/-- Hand-written: the deriving handler does not support nested inductives. -/
def Script.decEq : (a b : Script) → Decidable (a = b)
  | .sig a, .sig b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .all as, .all bs =>
    match Script.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .any as, .any bs =>
    match Script.decEqList as bs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .atLeast n as, .atLeast m bs =>
    if hn : n = m then
      match Script.decEqList as bs with
      | isTrue h => isTrue (hn ▸ h ▸ rfl)
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
    else isFalse (by intro e; cases e; exact hn rfl)
  | .after a, .after b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .before a, .before b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro e; cases e; exact h rfl)
  | .sig _, .all _ | .sig _, .any _ | .sig _, .atLeast _ _ | .sig _, .after _ | .sig _, .before _
  | .all _, .sig _ | .all _, .any _ | .all _, .atLeast _ _ | .all _, .after _ | .all _, .before _
  | .any _, .sig _ | .any _, .all _ | .any _, .atLeast _ _ | .any _, .after _ | .any _, .before _
  | .atLeast _ _, .sig _ | .atLeast _ _, .all _ | .atLeast _ _, .any _ | .atLeast _ _, .after _
  | .atLeast _ _, .before _
  | .after _, .sig _ | .after _, .all _ | .after _, .any _ | .after _, .atLeast _ _ | .after _, .before _
  | .before _, .sig _ | .before _, .all _ | .before _, .any _ | .before _, .atLeast _ _
  | .before _, .after _ => isFalse (by intro e; cases e)

def Script.decEqList : (a b : List Script) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro e; cases e)
  | a :: as, b :: bs =>
    match Script.decEq a b, Script.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h => isFalse (by intro e; cases e; exact h rfl)
end

instance : DecidableEq Script := Script.decEq

/-- The validity interval of a transaction, `[invalidBefore, invalidHereafter)`.
A missing bound is unbounded. Native scripts only ever see this interval, never
the actual slot at which the transaction is applied. -/
structure Interval where
  invalidBefore : Option Slot := none
  invalidHereafter : Option Slot := none
  deriving Repr, DecidableEq, Inhabited

/-- An interval that some slot actually lies in. The ledger only applies a
transaction at a slot inside its interval, so any transaction that can land on
chain has a valid interval. -/
def Interval.Valid (i : Interval) : Prop :=
  match i.invalidHereafter with
  | none => True
  | some h => i.invalidBefore.getD 0 < h

instance (i : Interval) : Decidable i.Valid := by
  unfold Interval.Valid; split <;> infer_instance

/-- The interval contains slot `t`. -/
def Interval.Contains (i : Interval) (t : Slot) : Prop :=
  i.invalidBefore.getD 0 ≤ t ∧
    match i.invalidHereafter with
    | none => True
    | some h => t < h

instance (i : Interval) (t : Slot) : Decidable (i.Contains t) := by
  unfold Interval.Contains; split <;> infer_instance

/-- What a native script sees of a transaction: who signed it and its validity
interval. -/
structure Env where
  signers : List KeyHash
  validity : Interval := {}
  deriving Repr

end NativeScript
