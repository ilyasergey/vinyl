/-!
# CRC-8 and CRC-16

FLAC frame-header CRC-8 (polynomial `x^8 + x^2 + x^1 + x^0`, i.e. `0x07`) and
frame-footer CRC-16 (polynomial `x^16 + x^15 + x^2 + x^0`, i.e. `0x8005`),
both with initial value 0, MSB-first, not reflected (RFC 9639 §9.3).

No theorems are needed here: the encoder writes the CRC of the bytes it just
produced, and the decoder recomputes the same function over the same bytes
and compares — so in the round-trip proof the check is satisfied
definitionally. Correctness against the standard is covered by test
vectors and by differential testing against libFLAC.

The byte updates are table-driven (the classic 256-entry construction);
`crc8UpdateBitwise`/`crc16UpdateBitwise` are the direct shift-register
definitions the tables are built from, kept as the reference the test
suite compares the table path against on every byte value.
-/

namespace Flac.Crc

/-- One byte step of CRC-8, polynomial `0x07`, as a shift register. -/
def crc8UpdateBitwise (crc b : UInt8) : UInt8 :=
  let x := crc ^^^ b
  (List.range 8).foldl
    (fun c _ => if c &&& 0x80 ≠ 0 then (c <<< 1) ^^^ 0x07 else c <<< 1) x

def crc8Table : Array UInt8 :=
  Array.ofFn (n := 256) fun i => crc8UpdateBitwise (UInt8.ofNat i.val) 0

/-- One byte step of CRC-8, via the table. -/
def crc8Update (crc b : UInt8) : UInt8 :=
  crc8Table[(crc ^^^ b).toNat]'(by
    simp only [crc8Table, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

def crc8List (bs : List UInt8) : UInt8 :=
  bs.foldl crc8Update 0

def crc8 (bs : ByteArray) : UInt8 :=
  bs.foldl crc8Update 0

/-- One byte step of CRC-16, polynomial `0x8005`, as a shift register. -/
def crc16UpdateBitwise (crc : UInt16) (b : UInt8) : UInt16 :=
  let x := crc ^^^ (b.toUInt16 <<< 8)
  (List.range 8).foldl
    (fun c _ => if c &&& 0x8000 ≠ 0 then (c <<< 1) ^^^ 0x8005 else c <<< 1) x

def crc16Table : Array UInt16 :=
  Array.ofFn (n := 256) fun i => crc16UpdateBitwise 0 (UInt8.ofNat i.val)

/-- One byte step of CRC-16, via the table. -/
def crc16Update (crc : UInt16) (b : UInt8) : UInt16 :=
  (crc <<< 8) ^^^ crc16Table[((crc >>> 8).toUInt8 ^^^ b).toNat]'(by
    simp only [crc16Table, Array.size_ofFn]; exact UInt8.toNat_lt_size _)

def crc16List (bs : List UInt8) : UInt16 :=
  bs.foldl crc16Update 0

def crc16 (bs : ByteArray) : UInt16 :=
  bs.foldl crc16Update 0

end Flac.Crc
