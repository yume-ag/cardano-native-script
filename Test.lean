import NativeScript

/-!
# Tests

Before you sink an afternoon into proving the `sorry`s, check that the
statements are actually true. This runs thousands of random scripts and
transactions through the executable versions of the theorems, and checks the
hash function against reference vectors.
-/

open NativeScript

/-! ## A tiny PRNG -/

abbrev Gen := StateM Nat

def rand (bound : Nat) : Gen Nat := do
  let s ← get
  let s' := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set s'
  return (s' >>> 33) % bound

def keys : List KeyHash := ['a', 'b', 'c', 'd'].map fun c => String.ofList (List.replicate 56 c)

partial def genScript (depth : Nat) : Gen Script := do
  let leaf : Gen Script := do
    match ← rand 4 with
    | 0 => return .after (← rand 12)
    | 1 => return .before (← rand 13)
    | _ => return .sig keys[← rand 4]!
  if depth == 0 then leaf else
  match ← rand 5 with
  | 0 | 1 => leaf
  | k => do
    let n ← rand 4
    let mut ss := []
    for _ in [0:n] do ss := (← genScript (depth - 1)) :: ss
    -- occasionally duplicate a child, to exercise `atLeast` counting
    if (← rand 4) == 0 then if let some s := ss.head? then ss := s :: ss
    match k with
    | 2 => return .all ss
    | 3 => return .any ss
    | _ => return .atLeast (← rand (ss.length + 2)) ss

def genOptSlot (bound : Nat) : Gen (Option Slot) := do
  if (← rand 3) == 0 then return none else return some (← rand bound)

def genEnv : Gen Env := do
  let mut signers := []
  for k in keys do if (← rand 2) == 0 then signers := k :: signers
  return { signers, validity := { invalidBefore := ← genOptSlot 14, invalidHereafter := ← genOptSlot 15 } }

/-! ## Properties -/

def powerset {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => let p := powerset xs; p ++ p.map (x :: ·)

structure Failure where
  property : String
  script : Script
  env : Option Env := none

def checkScript (s : Script) (envs : List Env) : List Failure := Id.run do
  let mut fails := []
  let d := dnf s
  let simp := simplify s
  for c in d do
    if !c.feasible then fails := ⟨"dnf_feasible", s, none⟩ :: fails
    if !c.keys.Nodup then fails := ⟨"dnf_keys_nodup", s, none⟩ :: fails
  for env in envs do
    let sat := decide (Satisfies env s)
    -- dnf_sound
    if d.any (fun c => decide (c.Holds env)) && !sat then
      fails := ⟨"dnf_sound", s, some env⟩ :: fails
    if env.validity.Valid then
      -- dnf_complete
      if sat && !d.any (fun c => decide (c.Holds env)) then
        fails := ⟨"dnf_complete", s, some env⟩ :: fails
      -- simplify_sound
      if decide (Satisfies env simp) != sat then
        fails := ⟨"simplify_sound", s, some env⟩ :: fails
      -- minSigners_optimal
      if sat then
        match minSigners s with
        | some n => if n > env.signers.eraseDups.length then
            fails := ⟨"minSigners_optimal", s, some env⟩ :: fails
        | none => fails := ⟨"minSigners_none_iff", s, some env⟩ :: fails
      -- signerSets_complete
      if sat && !(signerSets s).any (subsetOf · env.signers) then
        fails := ⟨"signerSets_complete", s, some env⟩ :: fails
  -- signerSets_sound: each set, at the start of its window, satisfies
  for ks in signerSets s do
    let ok := (dnf s).any fun c => subsetOf c.keys ks &&
      decide (Satisfies ⟨ks, { invalidBefore := some (c.lo.getD 0),
                               invalidHereafter := c.hi }⟩ s)
    if !ok then fails := ⟨"signerSets_sound", s, none⟩ :: fails
  -- windows_spec / mergeWindows_spec on slots 0..16, with interval [t, t+1)
  let ws := windows s
  let merged := mergeWindows ws
  for t in List.range 17 do
    let inW := ws.any fun w => decide (w.Contains t)
    let sat := powerset keys |>.any fun ks =>
      decide (Satisfies ⟨ks, { invalidBefore := some t, invalidHereafter := some (t + 1) }⟩ s)
    if inW != sat then fails := ⟨s!"windows_spec (t = {t})", s, none⟩ :: fails
    if inW != merged.any (fun w => decide (w.Contains t)) then
      fails := ⟨s!"mergeWindows_spec (t = {t})", s, none⟩ :: fails
  -- JSON round trip
  if (match Script.parse s.toJson.compress with | .ok s' => s' != s | .error _ => true) then
    fails := ⟨"json round trip", s, none⟩ :: fails
  return fails

/-! ## Hash vectors (from Python's `hashlib.blake2b(digest_size=28)`) -/

def hashVectors : List (ByteArray × String) := [
  (.empty, "836cc68931c2e4e3e838602eca1902591d216837bafddfe6f0c8cb07"),
  ("abc".toUTF8, "9bd237b02a29e43bdd6738afa5b53ff0eee178d6210b618e4511aec8"),
  (⟨((List.range 256).map Nat.toUInt8 |> fun l => l ++ l ++ l).toArray⟩,
    "43a8472a7f1699e287ad66cbdc8fc5ede6aa5146e8a435f76b94330a")]

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 3000
  let mut failures : Array Failure := #[]
  let mut seed := 42
  for _ in [0:n] do
    let ((s, envs), seed') := (do
      let s ← genScript 3
      let mut envs := []
      for _ in [0:25] do envs := (← genEnv) :: envs
      return (s, envs) : Gen _).run seed
    seed := seed'
    failures := failures ++ (checkScript s envs).toArray
  let mut bad := 0
  for (msg, expected) in hashVectors do
    let got := toHex (Blake2b.hash 28 msg)
    if got != expected then
      bad := bad + 1
      IO.println s!"blake2b-224 mismatch: got {got}, expected {expected}"
  -- report the first failure of each property
  let props := (failures.map (·.property)).toList.eraseDups
  for p in props do
    let some f := failures.find? (·.property == p) | continue
    let count := (failures.filter (·.property == p)).size
    IO.println s!"FAIL {p} ({count}×)\n  script: {f.script.toJson.compress}\n  env: {repr f.env}"
  if props.isEmpty && bad == 0 then
    IO.println s!"OK: {n} random scripts × 25 transactions, {hashVectors.length} hash vectors"
    return 0
  return 1
