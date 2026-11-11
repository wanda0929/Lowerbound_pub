import Mathlib.Data.Rat.Defs

/-! Pure, total decoding of generated decimal literals. No IO, native axiom,
or run-time certificate lookup enters the mathematical definitions. The
exporter and AllocationDataAudit check the encoding and all array shapes. -/
namespace LowerBoundCZ.AllocationCodec

def words (s : String) : Array String :=
  if s.isEmpty then #[] else (s.splitOn " ").toArray

def naturals (s : String) : Array Nat := (words s).map String.toNat!

def rational (s : String) : ℚ :=
  let parts := (s.splitOn "/").toArray
  (parts[0]?.getD "0").toInt! / ((parts[1]?.getD "1").toNat! : ℚ)

def rationals (s : String) : Array ℚ := (words s).map rational

def scalars (s : String) : Array (ℚ × ℚ) := (words s).map fun t =>
  let parts := (t.splitOn ",").toArray
  (rational (parts[0]?.getD "0"), rational (parts[1]?.getD "0"))

def row (s : String) : Array (Nat × Int) := (words s).map fun t =>
  let parts := (t.splitOn ":").toArray
  ((parts[0]?.getD "0").toNat!, (parts[1]?.getD "0").toInt!)

def rows (s : String) : Array (Array (Nat × Int)) :=
  (s.splitOn "|").toArray.map row

def allocation (s : String) : Array (Nat × ℚ) := (words s).map fun t =>
  let parts := (t.splitOn ":").toArray
  ((parts[0]?.getD "0").toNat!, rational (parts[1]?.getD "0"))

structure Source where
  size : Nat
  localizer : Nat
  -- Bit zero is the phase (0 = 1, 1 = i); eleven base-16 digits are powers.
  basis : Array Nat
  rows : Array (Array (Nat × Int))
  -- Upper triangular, row major, including the diagonal.
  upper : Array (ℚ × ℚ)
  deriving Inhabited

/-- Keep large literals encoded until a block is actually evaluated. Eager
module initialization must not parse every Gram matrix merely to import a proof. -/
structure EncodedSource where
  size : Nat
  localizer : Nat
  basis : String
  rows : String
  upper : String
  deriving Inhabited

def EncodedSource.decode (s : EncodedSource) : Source :=
  ⟨s.size, s.localizer, naturals s.basis, AllocationCodec.rows s.rows, scalars s.upper⟩

structure Projection where
  originalID : Nat
  block : Nat
  rows : Array Nat
  matrix : Array ℚ
  polynomial : Array ℚ
  population : Array Nat
  deriving Inhabited

structure EncodedProjection where
  originalID : Nat
  block : Nat
  rows : String
  matrix : String
  polynomial : String
  population : String
  deriving Inhabited

def EncodedProjection.decode (p : EncodedProjection) : Projection :=
  ⟨p.originalID, p.block, naturals p.rows, rationals p.matrix,
    rationals p.polynomial, naturals p.population⟩

end LowerBoundCZ.AllocationCodec
