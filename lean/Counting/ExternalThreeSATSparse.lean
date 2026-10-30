import Counting.ExternalThreeSATReduction
import Counting.ExternalMatchingList

namespace Counting.External.ThreeSAT

abbrev TypedEdge (n m : Nat) := Place n m × (Place n m × Port n m)

def slotList (n m : Nat) : List (Slot n m) :=
  (List.finRange n).flatMap (fun v=>(List.finRange (3*m+1)).map (fun j=>(v,j)))

@[simp] theorem mem_slotList (n m : Nat) (slot : Slot n m) : slot∈slotList n m := by
  simp [slotList]

def portList (n m : Nat) : List (Port n m) :=
  [false,true].flatMap (fun bit=>(slotList n m).map (fun slot=>(bit,slot)))

@[simp] theorem mem_portList (n m : Nat) (port : Port n m) : port∈portList n m := by
  rcases port with ⟨bit,slot⟩
  cases bit <;> simp [portList]

def variableEdges (n m : Nat) : List (TypedEdge n m) :=
  (slotList n m).flatMap (fun slot=>
    [(.inl slot,.inl slot,(false,slot)),(.inl slot,.inl (nextSlot slot),(true,slot))])

def clauseEdges {n m : Nat} (formula : ThreeSAT n m) : List (TypedEdge n m) :=
  (List.finRange m).flatMap (fun c=>(List.finRange 3).map (fun p=>
    (.inr (.inl c),.inr (.inl c),formula.literalPort c p)))

def completionEdges (n m : Nat) : List (TypedEdge n m) :=
  (List.finRange (slotCount n m-m)).flatMap (fun g=>(portList n m).map (fun port=>
    (.inr (.inr g),.inr (.inr g),port)))

/-- Sparse enumeration: two variable-cycle choices per slot, three clause
choices per clause, and every port for each completion position. -/
def typedEdges {n m : Nat} (formula : ThreeSAT n m) : List (TypedEdge n m) :=
  variableEdges n m++formula.clauseEdges++completionEdges n m

theorem mem_typedEdges {n m : Nat} (formula : ThreeSAT n m) (x y : Place n m) (z : Port n m) :
    (x,y,z)∈formula.typedEdges ↔ formula.gadgetArc x y z=true := by
  rcases z with ⟨bit,slot⟩
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      cases bit <;> simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc,Prod.mk.injEq,and_comm]
    | inr e => cases e <;> simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc]
  | inr e =>
    cases e with
    | inl c =>
      cases y with
      | inl w => simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc]
      | inr f =>
        cases f <;> simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc,Prod.mk.injEq]
        intro _
        exact exists_congr (fun _=>eq_comm)
    | inr g =>
      cases y with
      | inl w => simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc]
      | inr f => cases f <;> simp [typedEdges,variableEdges,clauseEdges,completionEdges,gadgetArc,Prod.mk.injEq]

def sparseEdges {n m : Nat} (formula : ThreeSAT n m) : List (MatchingEdge (2*slotCount n m)) :=
  formula.typedEdges.map (fun edge=>(formula.placeEquiv edge.1,formula.placeEquiv edge.2.1,portEquiv n m edge.2.2))

theorem sparseArc_eq {n m : Nat} (formula : ThreeSAT n m) :
    listArc (2*slotCount n m) formula.sparseEdges=formula.indexedArc := by
  funext x y z
  apply Bool.eq_iff_iff.mpr
  simp only [listArc,decide_eq_true_eq,sparseEdges,List.mem_map]
  constructor
  · rintro ⟨edge,member,equal⟩
    cases equal
    simpa only [indexedArc,Equiv.symm_apply_apply] using (formula.mem_typedEdges edge.1 edge.2.1 edge.2.2).mp member
  · intro allowed
    refine ⟨(formula.placeEquiv.symm x,formula.placeEquiv.symm y,(portEquiv n m).symm z),?_,?_⟩
    · exact (formula.mem_typedEdges _ _ _).mpr allowed
    · simp

def toSparseThreeDM {n m : Nat} (formula : ThreeSAT n m) := listToThreeDM (2*slotCount n m) formula.sparseEdges

theorem toSparseThreeDM_yes_iff {n m : Nat} (formula : ThreeSAT n m) :
    formula.toSparseThreeDM.Yes ↔ formula.Yes := by
  rw [toSparseThreeDM,listToThreeDM_iff,sparseArc_eq]
  exact formula.indexed_matching_iff.trans formula.gadget_matching_iff_yes

@[simp] theorem slotList_length (n m : Nat) : (slotList n m).length=slotCount n m := by
  simp [slotList,slotCount,List.length_flatMap]

@[simp] theorem portList_length (n m : Nat) : (portList n m).length=2*slotCount n m := by
  simp [portList,slotList_length];omega

theorem typedEdges_length {n m : Nat} (formula : ThreeSAT n m) :
    formula.typedEdges.length=2*slotCount n m+3*m+(slotCount n m-m)*(2*slotCount n m) := by
  simp [typedEdges,variableEdges,clauseEdges,completionEdges,List.length_flatMap,Nat.mul_comm,Nat.add_assoc]

theorem sparseEdges_length {n m : Nat} (formula : ThreeSAT n m) :
    formula.sparseEdges.length=2*slotCount n m+3*m+(slotCount n m-m)*(2*slotCount n m) := by
  simp only [sparseEdges,List.length_map,typedEdges_length]

end Counting.External.ThreeSAT
