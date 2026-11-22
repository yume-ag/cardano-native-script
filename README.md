# nsa: a formally verified Cardano native-script analyser

`nsa` reads native scripts in the `cardano-cli` JSON format (the multisig and
time-lock language behind treasury wallets and most minting policies) and
answers the questions people get wrong once scripts are nested:

* **Can these keys sign within this validity interval?**
* **What is the minimum number of signers, and which signer sets are minimal?**
* **In what time window can this script be satisfied at all?**
* **What is an equivalent, simpler script?**
* **What is its script hash / policy ID?**

It's written in Lean 4. The specification of native-script semantics and the
analyses live in the same code base, and the analyses are proved correct
against that specification.

```console
$ nsa info examples/treasury-multisig.json --mainnet
Script hash: d1e36521…
Minimum signers: 1
Minimal signer sets (11):
  {7e9a4f27…, abd38d29…, ff4227fc…}
      at any time
  …
  {7df0e683…}
      from slot 150000000 (2025-03-10 00:24:51 UTC)
```

The "3-of-5" treasury in this example can in fact be spent by **one** key once
slot 150,000,000 has passed. That's the kind of thing the tool is for.

## Usage

```
nsa info     <script.json> [--mainnet] [--full-keys]
nsa check    <script.json> [--signer <keyhash>]... [--invalid-before <slot>] [--invalid-hereafter <slot>]
nsa simplify <script.json>
nsa hash     <script.json>
```

`check` exits with 0 if the signers (and interval, if given) can satisfy the
script, 1 if they can't, and 2 on errors, so it can be used in scripts and CI.

## Building

```sh
nix develop          # provides elan; the Lean version is pinned in ./lean-toolchain
lake build           # → .lake/build/bin/nsa
lake test            # randomised checks of every theorem statement + Blake2b vectors
```

Without Nix, install [elan](https://github.com/leanprover/elan) and run the same
`lake` commands. No Mathlib. The only dependency is lean-json, which needs nothing from the
Lean frontend, so `nsa` is a small binary.

### Editors and lean-tui

The dev shell also provides [lean-tui](https://codeberg.org/wvhulle/lean-tui)
and [Lean-Prism](https://codeberg.org/wvhulle/lean-prism) (Linux), which show the
proof graph under your cursor in a terminal. Project-local editor config is
included. Both run `lean-prism serve` instead of `lake serve`:

* **Helix**: `.helix/languages.toml`, `.helix/config.toml`. Start `hx` from
  inside `nix develop`. The graph updates on `space k` (hover).
* **Zed**: `.zed/settings.json`. Needs the *Lean 4* extension. The graph
  updates when you hover with the mouse.

Then run `lean-tui` in a second terminal. `.envrc` loads the dev shell via
[direnv](https://direnv.net) (`direnv allow`), which is how Zed finds
`lean-prism` when launched from a desktop launcher. The first start builds the
Lean-Prism plugin, which takes a while.

Lean-Prism supports exactly one Lean version per branch, so `lean-toolchain`
is pinned to the version its `main` branch targets (currently v4.35.0). Check
its [supported versions](https://codeberg.org/wvhulle/lean-prism#supported-lean-versions)
before bumping Lean.

## Layout

| File | Contents |
|---|---|
| `NativeScript/Syntax.lean` | `Script`, validity `Interval`, `Env` |
| `NativeScript/Semantics.lean` | `Satisfies` (spec, a `Prop`), `eval` (implementation), `eval_iff`, `Decidable` |
| `NativeScript/Lemmas.lean` | `Script.induct` (induction over scripts), `eval` equations used by the later proofs |
| `NativeScript/Simplify.lean` | `simplify` + `simplify_sound` |
| `NativeScript/Dnf.lean` | Normal form (clauses = key sets + time bounds), soundness and completeness |
| `NativeScript/Analysis.lean` | `minSigners`, `signerSets`, `windows`, with their specs |
| `NativeScript/Hash.lean` | CBOR encoding, Blake2b-224 in pure Lean, script hash |
| `NativeScript/Json.lean` | `cardano-cli` JSON in/out |
| `NativeScript/Lint.lean` | Heuristic warnings (not proved) |
| `Main.lean` | CLI |
| `Test.lean` | Property tests for the theorem statements |

## Semantics, and the subtle bits

The spec is the inductive relation `Satisfies env s`, where `env` holds the
transaction's signers and its **validity interval** `[invalidBefore,
invalidHereafter)`. It follows `evalTimelock` from cardano-ledger:

* `after t` (`RequireTimeStart`) holds iff `invalidBefore = some b` with
  `t ≤ b`. `before t` (`RequireTimeExpire`) holds iff `invalidHereafter =
  some h` with `h ≤ t`. **A missing bound never satisfies a time lock**, so
  `after 0` is not trivially true. Your transaction has to set the bound.
* Time locks are judged against the interval, never against "the current
  slot". So "when can this be satisfied?" means: for which slots `t` is there
  a transaction, valid at `t`, that satisfies the script. `windows_spec`
  states exactly this.
* `atLeast n` counts sub-scripts **by position**. `atLeast 2 [sig A, sig A,
  sig B]` is satisfied by A alone. The linter flags this.
* `evalTimelock` will happily accept an empty interval, e.g. `[10, 5)`. Such
  a transaction can never be applied, so some equivalences (such as `all
  [after 10, before 5] ≡ false`) only hold for **valid** intervals. The
  theorems that need this assume `Interval.Valid`.

## What the proofs guarantee, and what they don't

*Status: every theorem below is proved, with no `sorry`. Each depends only on
Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`); check
with `#print axioms`.*

**Guaranteed:**

* `eval_iff`: the executable evaluator agrees with the declarative spec.
  `nsa check` with an interval runs `decide (Satisfies env s)`.
* `simplify_sound`: `simplify s` and `s` are satisfied by exactly the same
  transactions (with valid intervals).
* `dnf_sound` / `dnf_complete`: the normal form is an exact description of
  the script.
* `minSigners_sound` / `minSigners_optimal`: the reported minimum is attained
  and nothing smaller works.
* `signerSets_sound` / `_complete` / `_minimal`: every listed set works (with
  a suitable interval), every working set contains a listed one, and no listed
  set contains another.
* `windows_spec`, `windowsFor_spec`, `mergeWindows_spec`: a transaction valid
  at slot `t` can satisfy the script iff `t` is in a reported window.

**Not guaranteed:**

* **That `Satisfies` is the ledger.** The spec is a hand transcription of
  `evalTimelock`. It's small enough to audit by eye, but it is not extracted
  from the ledger's formal spec. Linking it to the Agda formal ledger spec, or
  testing it against the Haskell implementation, would close that gap.
* **Hashes.** CBOR and Blake2b are tested (Blake2b against reference vectors),
  not proved. The script hash is computed from *our* canonical encoding
  (definite-length lists up to 23 elements, indefinite beyond, as in
  cardano-ledger). A script serialised differently by another tool has a
  different hash on chain. Cross-check with `cardano-cli hash script`.
* **JSON.** Reading and writing the JSON text itself goes through
  [lean-json](https://github.com/paulbutcher/lean-json), which is proved
  correct against the RFC 8259 grammar and refuses duplicate keys. Mapping
  JSON values to `Script`s (`NativeScript/Json.lean`) is tested by a round
  trip, not proved.
* **The CLI and slot-to-UTC conversion.** Not verified.
  `--mainnet` times assume mainnet's fixed era boundaries.
* **Lint warnings.** Heuristics.
* **Phase-1 validity beyond the script.** Fees, collateral, the slot actually
  being inside the interval, etc. are out of scope.
* **Performance.** The normal form is exponential in the worst case
  (`atLeast k` of `n` gives `n choose k` clauses). That's fine for real
  multisigs, but don't feed it adversarial input in a hot path.

## Licence

TODO
