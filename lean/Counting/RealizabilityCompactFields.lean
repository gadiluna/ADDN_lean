import Counting.RealizabilityCompactBitGraph

namespace Counting.RealizabilityVerifier.CompactGraph

/-- Bounded-slot data used to assemble the auxiliary graph. Numeric mass
scans supply the last two masks; graph assembly only combines Boolean fields. -/
structure Fields (size : Nat) where
  isNew : Fin size → Bool
  isOld : Fin size → Bool
  isOutside : Fin size → Bool
  degreePositive : Fin size → Bool
  leavingPositive : Fin size → Bool
  deficitPositive : Fin size → Bool
  parentMatches : Fin size → Fin size → Bool
  incomingPositive : Fin size → Fin size → Bool

def fieldsActive {size : Nat} (fields : Fields size) (x : Fin size) : Bool :=
  fields.isNew x || fields.isOld x || fields.isOutside x

/-- Incoming incidence is read as receiver, sender: the second clause
therefore queries the transposed pair `y,x`. -/
def fieldsArc {size : Nat} (fields : Fields size) (x y : Fin size) : Bool :=
  (fields.isNew x && fields.isOld y && (fields.parentMatches x y && fields.degreePositive x)) ||
  (fields.isOld x && fields.isNew y && fields.incomingPositive y x) ||
  (fields.isOutside x && fields.isOld y && fields.leavingPositive y) ||
  (fields.isOld x && fields.isOutside y && (fields.leavingPositive x || fields.deficitPositive x))

def actualFields (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    Fields (vista.nodes.size+1) where
  isNew:=isNew vista r
  isOld:=isOld vista r
  isOutside:=isOutside N vista weights r
  degreePositive x:=decide (0 < (vista.node x.val).degree)
  leavingPositive x:=decide (0 < leaving vista weights r x.val)
  deficitPositive x:=decide (demand vista weights r x.val < supply vista weights r x.val)
  parentMatches x y:=(vista.node x.val).parent==some y.val
  incomingPositive receiver sender:=decide (0 < Executable.countFrom (vista.node receiver.val) sender.val)

@[simp] theorem fieldsActive_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat)
    (x : Slot vista) : fieldsActive (actualFields N vista weights r) x=active N vista weights r x := rfl

@[simp] theorem fieldsArc_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat)
    (x y : Slot vista) : fieldsArc (actualFields N vista weights r) x y=arc N vista weights r x y := rfl

def vectorBits {size : Nat} (field : Fin size → Bool) : List Bool:=List.ofFn field

def matrixBits {size : Nat} (field : Fin size → Fin size → Bool) : List Bool:=
  List.ofFn (fun index : Fin (size*size)=>
    let pair : Fin size×Fin size:=finProdFinEquiv.symm index
    field pair.1 pair.2)

@[simp] theorem vectorBits_length {size : Nat} (field : Fin size → Bool) :
    (vectorBits field).length=size:=List.length_ofFn

@[simp] theorem matrixBits_length {size : Nat} (field : Fin size → Fin size → Bool) :
    (matrixBits field).length=size*size:=List.length_ofFn

@[simp] theorem bitAt_vectorBits {size : Nat} (field : Fin size → Bool) (x : Fin size) :
    BitGraph.bitAt (vectorBits field) x.val=field x := by
  simp [BitGraph.bitAt,vectorBits,x.isLt]

@[simp] theorem bitAt_matrixBits {size : Nat} (field : Fin size → Fin size → Bool) (x y : Fin size) :
    BitGraph.bitAt (matrixBits field) (x.val*size+y.val)=field x y := by
  have position : (finProdFinEquiv (x,y)).val=x.val*size+y.val:=by simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [←position]
  change BitGraph.bitAt (vectorBits (fun index : Fin (size*size)=>
    field (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2)) (finProdFinEquiv (x,y)).val=_
  rw [bitAt_vectorBits,Equiv.symm_apply_apply]

/-- Convert the six unary masks and two row-major matrices back into the
bounded field interface. Malformed/truncated tables use the standard false
default; exactness is asserted separately by the tabulation theorem. -/
def fieldsFromBits (size : Nat) (newBits oldBits outsideBits degreeBits leavingBits deficitBits
    parentBits incomingBits : List Bool) : Fields size where
  isNew x:=BitGraph.bitAt newBits x.val
  isOld x:=BitGraph.bitAt oldBits x.val
  isOutside x:=BitGraph.bitAt outsideBits x.val
  degreePositive x:=BitGraph.bitAt degreeBits x.val
  leavingPositive x:=BitGraph.bitAt leavingBits x.val
  deficitPositive x:=BitGraph.bitAt deficitBits x.val
  parentMatches x y:=BitGraph.bitAt parentBits (x.val*size+y.val)
  incomingPositive receiver sender:=BitGraph.bitAt incomingBits (receiver.val*size+sender.val)

theorem fieldsFromBits_tabulated {size : Nat} (fields : Fields size) :
    fieldsFromBits size (vectorBits fields.isNew) (vectorBits fields.isOld)
      (vectorBits fields.isOutside) (vectorBits fields.degreePositive) (vectorBits fields.leavingPositive)
      (vectorBits fields.deficitPositive) (matrixBits fields.parentMatches) (matrixBits fields.incomingPositive)=fields := by
  cases fields
  simp only [fieldsFromBits,bitAt_vectorBits,bitAt_matrixBits]

theorem tabulated_check_eq (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    BitGraph.check (vista.nodes.size+1) (matrixBits (fieldsArc (actualFields N vista weights r)))
      (vectorBits (fieldsActive (actualFields N vista weights r)))=
        connectedCheck (roundArc N vista weights r) := by
  apply bitCheck_eq
  · intro x y;rw [bitAt_matrixBits,fieldsArc_actual]
  · intro x;rw [bitAt_vectorBits,fieldsActive_actual]

end Counting.RealizabilityVerifier.CompactGraph
