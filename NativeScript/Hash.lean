import NativeScript.Syntax

/-!
# Script hashes

The script hash (which is also the policy ID of a minting policy) is
`blake2b-224 (0x00 ‖ cbor script)`, where `0x00` is the native-script language
tag. Blake2b is implemented here in plain Lean (RFC 7693) and checked against
reference vectors in `Test.lean`.

The CBOR follows cardano-ledger's `Timelock` encoder. Lists of up to 23
elements are definite-length; longer ones are indefinite-length. The ledger
hashes the bytes that actually appear on chain, so a script that some other
tool serialised differently will hash differently. Compare against
`cardano-cli hash script --script-file …`.
-/

namespace NativeScript

/-! ## Hex -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : ByteArray) : String :=
  b.data.foldl (fun s x => s.push (hexDigit (x.toNat / 16)) |>.push (hexDigit (x.toNat % 16))) ""

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55)
  else none

def fromHex (s : String) : Option ByteArray :=
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | a :: b :: rest, acc => do
      let hi ← hexVal a
      let lo ← hexVal b
      go rest (acc.push (hi * 16 + lo).toUInt8)
    | [_], _ => none
  go s.toList ByteArray.empty

/-! ## Blake2b -/

namespace Blake2b

def iv : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

def sigma : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

def mix (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va := v[a]! + v[b]! + x
  let vd := rotr (v[d]! ^^^ va) 32
  let vc := v[c]! + vd
  let vb := rotr (v[b]! ^^^ vc) 24
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 63
  ((v.set! a va).set! b vb |>.set! c vc).set! d vd

def word (b : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for j in [0:8] do
    w := w ||| ((b.get! (off + j)).toUInt64 <<< (8 * j).toUInt64)
  return w

def compress (h : Array UInt64) (msg : ByteArray) (off : Nat) (t : Nat) (last : Bool) :
    Array UInt64 := Id.run do
  let m := (List.range 16).toArray.map fun i => word msg (off + 8 * i)
  let mut v := h ++ iv
  v := v.set! 12 (v[12]! ^^^ t.toUInt64)
  v := v.set! 13 (v[13]! ^^^ (t >>> 64).toUInt64)
  if last then v := v.set! 14 (~~~ v[14]!)
  for r in [0:12] do
    let s := sigma[r % 10]!
    v := mix v 0 4 8 12 m[s[0]!]! m[s[1]!]!
    v := mix v 1 5 9 13 m[s[2]!]! m[s[3]!]!
    v := mix v 2 6 10 14 m[s[4]!]! m[s[5]!]!
    v := mix v 3 7 11 15 m[s[6]!]! m[s[7]!]!
    v := mix v 0 5 10 15 m[s[8]!]! m[s[9]!]!
    v := mix v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mix v 2 7 8 13 m[s[12]!]! m[s[13]!]!
    v := mix v 3 4 9 14 m[s[14]!]! m[s[15]!]!
  return (List.range 8).toArray.map fun i => h[i]! ^^^ v[i]! ^^^ v[i + 8]!

/-- Unkeyed Blake2b with an `outLen`-byte digest (`1 ≤ outLen ≤ 64`). -/
def hash (outLen : Nat) (msg : ByteArray) : ByteArray := Id.run do
  let nBlocks := max 1 ((msg.size + 127) / 128)
  let padded := msg ++ ⟨(List.replicate (nBlocks * 128 - msg.size) (0 : UInt8)).toArray⟩
  let mut h := iv.set! 0 (iv[0]! ^^^ 0x01010000 ^^^ outLen.toUInt64)
  for i in [0:nBlocks] do
    let last := i + 1 == nBlocks
    let t := if last then msg.size else (i + 1) * 128
    h := compress h padded (i * 128) t last
  let mut out := ByteArray.empty
  for i in [0:outLen] do
    out := out.push (h[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8
  return out

end Blake2b

/-! ## CBOR -/

namespace Cbor

def head (major : Nat) (n : Nat) : ByteArray :=
  let m := (major * 32).toUInt8
  let be (k : Nat) : ByteArray :=
    ⟨((List.range k).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray⟩
  if n < 24 then ⟨#[m + n.toUInt8]⟩
  else if n < 0x100 then ⟨#[m + 24]⟩ ++ be 1
  else if n < 0x10000 then ⟨#[m + 25]⟩ ++ be 2
  else if n < 0x100000000 then ⟨#[m + 26]⟩ ++ be 4
  else ⟨#[m + 27]⟩ ++ be 8

def uint (n : Nat) : ByteArray := head 0 n
def bytes (b : ByteArray) : ByteArray := head 2 b.size ++ b

/-- cardano-ledger's `variableListLenEncoding`: definite length up to 23
elements, indefinite length beyond that. -/
def list (items : List ByteArray) : ByteArray :=
  let body := items.foldl (· ++ ·) ByteArray.empty
  if items.length ≤ 23 then head 4 items.length ++ body
  else ⟨#[0x9f]⟩ ++ body ++ ⟨#[0xff]⟩

end Cbor

partial def Script.toCbor : Script → ByteArray
  | .sig k => Cbor.list [Cbor.uint 0, Cbor.bytes ((fromHex k).getD .empty)]
  | .all ss => Cbor.list [Cbor.uint 1, Cbor.list (ss.map toCbor)]
  | .any ss => Cbor.list [Cbor.uint 2, Cbor.list (ss.map toCbor)]
  | .atLeast n ss => Cbor.list [Cbor.uint 3, Cbor.uint n, Cbor.list (ss.map toCbor)]
  | .after t => Cbor.list [Cbor.uint 4, Cbor.uint t]
  | .before t => Cbor.list [Cbor.uint 5, Cbor.uint t]

/-- The script hash, i.e. the policy ID when the script is used for minting. -/
def Script.hash (s : Script) : String :=
  toHex (Blake2b.hash 28 (⟨#[0x00]⟩ ++ s.toCbor))

end NativeScript
