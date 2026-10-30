import Counting.EncodingRationalRows
import Counting.StoredGaussian

namespace Counting
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem

/-- Row operations with explicit binary row indices, independent of the
dimension of a particular matrix. Bounds are checked when interpreting them. -/
inductive RawRowOp where
  | swap (first second : Nat)
  | scale (row : Nat) (factor : Rat)
  | add (target source : Nat) (factor : Rat)
deriving DecidableEq, Repr

namespace RawRowOp

def ofRowOp {q : Nat} : RowOp q → RawRowOp
  | .swap first second => .swap first.val second.val
  | .scale row factor => .scale row.val factor
  | .add target source factor => .add target.val source.val factor

def toRowOp? (q : Nat) : RawRowOp → Option (RowOp q)
  | .swap first second =>
      if hFirst : first<q then
        if hSecond : second<q then some (.swap ⟨first,hFirst⟩ ⟨second,hSecond⟩) else none
      else none
  | .scale row factor =>
      if hRow : row<q then some (.scale ⟨row,hRow⟩ factor) else none
  | .add target source factor =>
      if hTarget : target<q then
        if hSource : source<q then some (.add ⟨target,hTarget⟩ ⟨source,hSource⟩ factor) else none
      else none

@[simp] theorem toRowOp_ofRowOp {q : Nat} (operation : RowOp q) :
    toRowOp? q (ofRowOp operation)=some operation := by
  cases operation <;> simp [ofRowOp,toRowOp?]

theorem ofRowOp_injective (q : Nat) : Function.Injective (@ofRowOp q) := by
  intro first second same
  have interpreted := congrArg (toRowOp? q) same
  simpa only [toRowOp_ofRowOp,Option.some.injEq] using interpreted

abbrev Fields := Nat×Nat×Nat×Rat

/-- Uniform tag/target/source/factor fields. Unused fields are canonical zero. -/
def fields : RawRowOp → Fields
  | .swap first second => (0,first,second,0)
  | .scale row factor => (1,row,0,factor)
  | .add target source factor => (2,target,source,factor)

/-- A total extension for prefix parsing. `decodeExact` checks re-encoding
and therefore rejects unused fields and tags outside the canonical format. -/
def fromFields (value : Fields) : RawRowOp :=
  if value.1=0 then .swap value.2.1 value.2.2.1
  else if value.1=1 then .scale value.2.1 value.2.2.2
  else .add value.2.1 value.2.2.1 value.2.2.2

@[simp] theorem fromFields_fields (operation : RawRowOp) : fromFields operation.fields=operation := by
  cases operation <;> simp [fields,fromFields]

end RawRowOp

namespace Encoding

def rawRowOpFields : Codec RawRowOp.Fields :=
  product natural (product natural (product natural rational))

def rawRowOp : Codec RawRowOp :=
  transport rawRowOpFields RawRowOp.fields RawRowOp.fromFields RawRowOp.fromFields_fields

@[simp] theorem rawRowOp_swap (first second : Nat) :
    rawRowOp.encode (.swap first second)=
      natural.encode 0++natural.encode first++natural.encode second++rational.encode 0 := by
  simp only [rawRowOp,transport,rawRowOpFields,product,RawRowOp.fields,List.append_assoc]

@[simp] theorem rawRowOp_scale (row : Nat) (factor : Rat) :
    rawRowOp.encode (.scale row factor)=
      natural.encode 1++natural.encode row++natural.encode 0++rational.encode factor := by
  simp only [rawRowOp,transport,rawRowOpFields,product,RawRowOp.fields,List.append_assoc]

@[simp] theorem rawRowOp_add (target source : Nat) (factor : Rat) :
    rawRowOp.encode (.add target source factor)=
      natural.encode 2++natural.encode target++natural.encode source++rational.encode factor := by
  simp only [rawRowOp,transport,rawRowOpFields,product,RawRowOp.fields,List.append_assoc]

theorem rawRowOp_roundtrip (operation : RawRowOp) (suffix : List Bool) :
    rawRowOp.decode (rawRowOp.encode operation++suffix)=some (operation,suffix) :=
  rawRowOp.roundtrip operation suffix

def gaussianOpsRev (operations : List RawRowOp) : List Bool :=
  sequence (framed rawRowOp) operations

@[simp] theorem gaussianOpsRev_cons (operation : RawRowOp) (operations : List RawRowOp) :
    gaussianOpsRev (operation::operations)=frame (rawRowOp.encode operation)++gaussianOpsRev operations := rfl

theorem gaussianOpsRev_parse (operations : List RawRowOp) (suffix : List Bool) :
    parseCount (framed rawRowOp) operations.length (gaussianOpsRev operations++suffix)=some (operations,suffix) :=
  parseCount_sequence (framed rawRowOp) operations suffix

theorem rawRowOp_length (operation : RawRowOp) :
    (rawRowOp.encode operation).length=
      2*operation.fields.1.size+1+(2*operation.fields.2.1.size+1)+
      (2*operation.fields.2.2.1.size+1)+(rational.encode operation.fields.2.2.2).length := by
  simp only [rawRowOp,transport,rawRowOpFields,product,List.length_append,natural_length]
  omega

end Encoding
end Counting
