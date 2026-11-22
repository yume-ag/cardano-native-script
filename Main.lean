import NativeScript

open NativeScript

/-! # `nsa`: the command-line interface -/

def usage : String := "nsa: a formally verified Cardano native-script analyser

USAGE:
  nsa info     <script.json> [--mainnet] [--full-keys]
      Script hash, structure, minimum signers, minimal signer sets,
      the slots at which it can be satisfied, and warnings.

  nsa check    <script.json> [--signer <keyhash>]... [--invalid-before <slot>]
               [--invalid-hereafter <slot>] [--mainnet]
      Can these keys satisfy the script? With an interval, decides it for
      that transaction. Without one, reports when these keys could.

  nsa simplify <script.json>
      Print an equivalent, simplified script as cardano-cli JSON.

  nsa hash     <script.json>
      Print the script hash (= policy ID) and its CBOR.

--mainnet     also show mainnet slots as UTC times
--full-keys   print key hashes in full (default: first 8 hex digits)
Use '-' for <script.json> to read from stdin.
Exit codes: 0 = yes/ok, 1 = no, 2 = usage or parse error."

/-! ## Mainnet slot to UTC -/

/-- Days since 1970-01-01 to (year, month, day), using Howard Hinnant's
`civil_from_days` algorithm. -/
def civil (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  (y, m, d)

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else toString n

def mainnetUtc (slot : Slot) : String :=
  -- Byron slots last 20s; Shelley (slot 4492800 onwards) slots last 1s.
  let posix := if slot < 4492800 then 1506203091 + slot * 20 else 1591566291 + slot
  let (y, m, d) := civil (posix / 86400)
  let s := posix % 86400
  s!"{y}-{pad2 m}-{pad2 d} {pad2 (s / 3600)}:{pad2 (s % 3600 / 60)}:{pad2 (s % 60)} UTC"

/-! ## Rendering -/

structure Opts where
  mainnet : Bool := false
  fullKeys : Bool := false
  signers : List KeyHash := []
  invalidBefore : Option Slot := none
  invalidHereafter : Option Slot := none
  file : Option String := none

def showSlot (o : Opts) (t : Slot) : String :=
  if o.mainnet then s!"{t} ({mainnetUtc t})" else toString t

def showWindow (o : Opts) (w : Window) : String :=
  match w.start, w.stop with
  | 0, none => "at any time"
  | 0, some e => s!"before slot {showSlot o e}"
  | a, none => s!"from slot {showSlot o a}"
  | a, some e => s!"from slot {showSlot o a} until (excl.) {showSlot o e}"

def short (o : Opts) (k : KeyHash) : String := if !o.fullKeys && k.length > 12 then (k.take 8).toString ++ "…" else k

partial def tree (o : Opts) (indent : String) : Script → List String
  | .sig k => [s!"{indent}sig {short o k}"]
  | .all ss => s!"{indent}all of" :: ss.flatMap (tree o (indent ++ "  "))
  | .any ss => s!"{indent}any of" :: ss.flatMap (tree o (indent ++ "  "))
  | .atLeast n ss => s!"{indent}at least {n} of" :: ss.flatMap (tree o (indent ++ "  "))
  | .after t => [s!"{indent}after slot {showSlot o t}"]
  | .before t => [s!"{indent}before slot {showSlot o t}"]

def showKeys (o : Opts) (ks : List KeyHash) : String :=
  if ks.isEmpty then "{} (no signatures)" else "{" ++ ", ".intercalate (ks.map (short o)) ++ "}"

/-! ## Commands -/

def readScript (path : String) : IO (Except String Script) := do
  try
    let input ← if path == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile path
    return Script.parse input
  catch e => return .error (toString e)

def cmdInfo (o : Opts) (s : Script) : IO UInt32 := do
  IO.println s!"Script hash: {s.hash}"
  IO.println "\nStructure:"
  for l in tree o "  " s do IO.println l
  IO.println ""
  match minSigners s with
  | none => IO.println "Minimum signers: none; NO transaction can ever satisfy this script."
  | some n => IO.println s!"Minimum signers: {n}"
  let sets := signerSets s
  IO.println s!"\nMinimal signer sets ({sets.length}):"
  for ks in sets do
    let ws := mergeWindows (windowsFor ks s)
    IO.println s!"  {showKeys o ks}"
    IO.println s!"      {", ".intercalate (ws.map (showWindow o))}"
  let ws := mergeWindows (windows s)
  IO.println "\nSatisfiable:"
  if ws.isEmpty then IO.println "  never"
  for w in ws do IO.println s!"  {showWindow o w}"
  let warnings := lint s
  unless warnings.isEmpty do
    IO.println "\nWarnings:"
    for w in warnings do IO.println s!"  ⚠ {w}"
  return 0

def cmdCheck (o : Opts) (s : Script) : IO UInt32 := do
  let signers := o.signers.eraseDups
  if o.invalidBefore.isSome || o.invalidHereafter.isSome then
    let i : Interval := { invalidBefore := o.invalidBefore, invalidHereafter := o.invalidHereafter }
    let env : Env := { signers, validity := i }
    unless i.Valid do
      IO.println "⚠ this validity interval is empty: no slot lies in it, so the ledger can never apply the transaction."
    -- `decide` runs the *specification* `Satisfies`, through `eval_iff`.
    if decide (Satisfies env s) then
      IO.println "✓ satisfied: these signatures and this validity interval satisfy the script"
      return 0
    IO.println "✗ not satisfied by these signatures and this validity interval"
    let ws := mergeWindows (windowsFor signers s)
    if ws.isEmpty then
      if let some extra := missingKeys signers s then
        IO.println s!"  the smallest set of extra signatures needed: {showKeys o extra}"
    else
      IO.println s!"  these signers could satisfy it with a validity interval inside: {", ".intercalate (ws.map (showWindow o))}"
    return 1
  else
    let ws := mergeWindows (windowsFor signers s)
    if ws.isEmpty then
      IO.println "✗ these signers cannot satisfy the script at any time"
      match missingKeys signers s with
      | some extra => IO.println s!"  the smallest set of extra signatures needed: {showKeys o extra}"
      | none => IO.println "  no set of signatures can: the script is unsatisfiable"
      return 1
    IO.println "✓ these signers can satisfy the script with a validity interval inside:"
    for w in ws do IO.println s!"  {showWindow o w}"
    return 0

def cmdSimplify (s : Script) : IO UInt32 := do
  IO.println (simplify s).toJson.pretty
  return 0

def cmdHash (s : Script) : IO UInt32 := do
  IO.println s!"script hash: {s.hash}"
  IO.println s!"cbor:        {toHex s.toCbor}"
  return 0

partial def parseOpts (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--mainnet" :: rest => parseOpts { o with mainnet := true } rest
  | "--full-keys" :: rest => parseOpts { o with fullKeys := true } rest
  | "--signer" :: k :: rest => parseOpts { o with signers := o.signers ++ [k.toLower] } rest
  | "--invalid-before" :: n :: rest =>
    match n.toNat? with
    | some t => parseOpts { o with invalidBefore := some t } rest
    | none => .error s!"--invalid-before: not a slot number: {n}"
  | "--invalid-hereafter" :: n :: rest =>
    match n.toNat? with
    | some t => parseOpts { o with invalidHereafter := some t } rest
    | none => .error s!"--invalid-hereafter: not a slot number: {n}"
  | arg :: rest =>
    if arg.startsWith "--" && arg != "-" then .error s!"unknown option {arg}"
    else if o.file.isSome then .error s!"unexpected argument {arg}"
    else parseOpts { o with file := some arg } rest

def main (args : List String) : IO UInt32 := do
  let fail (msg : String) : IO UInt32 := do
    IO.eprintln msg; return 2
  match args with
  | [] | ["--help"] | ["-h"] | ["help"] => IO.println usage; return 0
  | cmd :: rest =>
    unless ["info", "check", "simplify", "hash"].contains cmd do
      return (← fail s!"unknown command '{cmd}'\n\n{usage}")
    let o ← match parseOpts {} rest with
      | .ok o => pure o
      | .error e => do IO.eprintln e; IO.eprintln "\n(see nsa --help)"; return 2
    let some file := o.file | fail "missing <script.json>"
    let s ← match ← readScript file with
      | .ok s => pure s
      | .error e => do IO.eprintln s!"cannot read native script: {e}"; return 2
    match cmd with
    | "info" => cmdInfo o s
    | "check" => cmdCheck o s
    | "simplify" => cmdSimplify s
    | "hash" => cmdHash s
    | other => fail s!"unknown command '{other}'\n\n{usage}"
