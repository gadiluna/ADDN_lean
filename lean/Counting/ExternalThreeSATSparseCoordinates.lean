import Counting.ExternalThreeSATSparse

namespace Counting.External.ThreeSAT

@[simp] theorem place_slot_val {n m : Nat} (formula : ThreeSAT n m) (v : Slot n m) :
    (formula.placeEquiv (.inl v)).val=v.1.val*(3*m+1)+v.2.val := by
  change v.2.val+(3*m+1)*v.1.val=v.1.val*(3*m+1)+v.2.val
  ring

@[simp] theorem place_clause_val {n m : Nat} (formula : ThreeSAT n m) (c : Fin m) :
    (formula.placeEquiv (.inr (.inl c))).val=slotCount n m+c.val := by
  simp [placeEquiv,Nat.add_comm]

@[simp] theorem place_completion_val {n m : Nat} (formula : ThreeSAT n m) (g : Fin (slotCount n m-m)) :
    (formula.placeEquiv (.inr (.inr g))).val=slotCount n m+m+g.val := by
  simp [placeEquiv]
  omega

@[simp] theorem port_val {n m : Nat} (bit : Bool) (v : Slot n m) :
    (portEquiv n m (bit,v)).val=(if bit then slotCount n m else 0)+v.1.val*(3*m+1)+v.2.val := by
  cases bit
  · change v.2.val+(3*m+1)*v.1.val+slotCount n m*0=0+v.1.val*(3*m+1)+v.2.val
    ring
  · change v.2.val+(3*m+1)*v.1.val+slotCount n m*1=slotCount n m+v.1.val*(3*m+1)+v.2.val
    ring

theorem nextSlot_val {n m : Nat} (v : Slot n m) :
    (nextSlot v).2.val=if v.2.val=3*m then 0 else v.2.val+1 := by
  simp only [nextSlot,coe_finRotate]
  have equal : (v.2=Fin.last (3*m)) ↔ v.2.val=3*m := by simp [Fin.ext_iff]
  simp only [equal]

def sparseRawRows {n m : Nat} (formula : ThreeSAT n m) : List (List Nat) :=
  formula.sparseEdges.map (fun edge=>[edge.1.val,edge.2.1.val,edge.2.2.val])

def variableRawRows (n m : Nat) : List (List Nat) :=
  (List.finRange n).flatMap (fun v=>(List.finRange (3*m+1)).flatMap (fun j=>
    let index := v.val*(3*m+1)+j.val
    [[index,index,index],
     [index,v.val*(3*m+1)+(if j.val=3*m then 0 else j.val+1),slotCount n m+index]]))

def clauseRawRows {n m : Nat} (formula : ThreeSAT n m) : List (List Nat) :=
  (List.finRange m).flatMap (fun c=>(List.finRange 3).map (fun p=>
    let literal := formula.literal c p
    [slotCount n m+c.val,slotCount n m+c.val,
      (if literal.positive then slotCount n m else 0)+literal.var.val*(3*m+1)+3*c.val+p.val]))

def completionRawRows (n m : Nat) : List (List Nat) :=
  (List.finRange (slotCount n m-m)).flatMap (fun g=>
    [false,true].flatMap (fun bit=>(List.finRange n).flatMap (fun v=>(List.finRange (3*m+1)).map (fun j=>
      [slotCount n m+m+g.val,slotCount n m+m+g.val,
        (if bit then slotCount n m else 0)+v.val*(3*m+1)+j.val]))))

/-- Coordinates used by the executable sparse generator. Every number is
built by bounded counter arithmetic; no inverse finite equivalence is needed. -/
theorem sparseRawRows_blocks {n m : Nat} (formula : ThreeSAT n m) :
    formula.sparseRawRows=variableRawRows n m++formula.clauseRawRows++completionRawRows n m := by
  simp [sparseRawRows,sparseEdges,typedEdges,variableEdges,clauseEdges,completionEdges,
    variableRawRows,clauseRawRows,completionRawRows,slotList,portList,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,
    List.map_map,Function.comp_def,literalPort,literalSlot,occurrence,nextSlot_val,Nat.add_assoc]
  simp [nextSlot]

end Counting.External.ThreeSAT
