import Counting.ExternalMatchingVariableOuter
import Counting.ExternalThreeSATSparseCoordinates
import Counting.ExternalMatchingClauseLoop

namespace Counting.External.MatchingMachine

theorem finRange_map_values {α : Type} (n : Nat) (f : Nat → α) :
    (List.finRange n).map (fun i => f i.val)=(List.range n).map f := by
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun values : List Nat => values.map f) (List.map_coe_finRange_eq_range (n:=n))

theorem finRange_flatMap_values {α : Type} (n : Nat) (f : Nat → List α) :
    (List.finRange n).flatMap (fun i => f i.val)=(List.range n).flatMap f := by
  simpa only [List.flatMap_map,Function.comp_def] using
    congrArg (fun values : List Nat => values.flatMap f) (List.map_coe_finRange_eq_range (n:=n))

theorem portRows_range (first second start count : Nat) :
    portRows first second start count=(List.range' start count).map (fun i => [first,second,i]) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [portRows,List.range'_succ,List.map_cons,ih]

theorem blocks_range (start count width : Nat) :
    (List.range count).flatMap (fun i => (List.range width).map (fun j => start+i*width+j))=
      List.range' start (count*width) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.range_succ,List.flatMap_append,ih]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [←List.range'_eq_map_range]
    rw [List.range'_append_1,Nat.succ_mul]

theorem slots_range (start n m : Nat) :
    (List.finRange n).flatMap (fun v => (List.finRange (3*m+1)).map
      (fun j => start+v.val*(3*m+1)+j.val))=List.range' start (ThreeSAT.slotCount n m) := by
  simp_rw [finRange_map_values]
  rw [finRange_flatMap_values n (fun v => (List.range (3*m+1)).map (fun j => start+v*(3*m+1)+j))]
  exact blocks_range start n (3*m+1)

theorem ports_range (n m : Nat) :
    [false,true].flatMap (fun bit => (List.finRange n).flatMap
      (fun v => (List.finRange (3*m+1)).map
        (fun j => (if bit then ThreeSAT.slotCount n m else 0)+v.val*(3*m+1)+j.val)))=
      List.range (2*ThreeSAT.slotCount n m) := by
  simp only [List.flatMap_cons,List.flatMap_nil,Bool.false_eq_true,if_false,if_true,
    slots_range,List.append_nil]
  calc
    _ = List.range' 0 (ThreeSAT.slotCount n m+ThreeSAT.slotCount n m) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=ThreeSAT.slotCount n m) (n:=ThreeSAT.slotCount n m))
    _ = _ := by rw [←List.range_eq_range'];congr 1;omega

/-- Port order is exactly false/true, then variable, then slot. -/
theorem portRows_coordinates (first second n m : Nat) :
    portRows first second 0 (2*ThreeSAT.slotCount n m)=
      [false,true].flatMap (fun bit => (List.finRange n).flatMap
        (fun v => (List.finRange (3*m+1)).map (fun j =>
          [first,second,(if bit then ThreeSAT.slotCount n m else 0)+v.val*(3*m+1)+j.val]))) := by
  rw [portRows_range,←List.range_eq_range',←ports_range]
  simp only [List.map_flatMap,List.map_map,Function.comp_def]

theorem completionRows_range (first second ports count : Nat) :
    completionRows first second ports count=(List.range count).flatMap
      (fun g => portRows (first+g) (second+g) 0 ports) := by
  induction count generalizing first second with
  | zero => rfl
  | succ count ih =>
    rw [completionRows,ih,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f => (List.range count).flatMap f)
    funext g
    congr 1 <;> omega

theorem completionRows_coordinates (n m : Nat) :
    completionRows (ThreeSAT.slotCount n m+m) (ThreeSAT.slotCount n m+m)
      (2*ThreeSAT.slotCount n m) (ThreeSAT.slotCount n m-m)=ThreeSAT.completionRawRows n m := by
  rw [completionRows_range,←List.map_coe_finRange_eq_range (n:=ThreeSAT.slotCount n m-m),List.flatMap_map]
  unfold ThreeSAT.completionRawRows
  apply congrArg (fun f => (List.finRange (ThreeSAT.slotCount n m-m)).flatMap f)
  funext g
  exact portRows_coordinates _ _ n m

theorem variableRows_range (first second third count : Nat) :
    variableRows first second third count=(List.range count).flatMap
      (fun j => pairRows (first+j) (second+j) (third+j)) := by
  induction count generalizing first second third with
  | zero => rfl
  | succ count ih =>
    rw [variableRows,ih,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f => (List.range count).flatMap f)
    funext j
    congr 1 <;> omega

theorem variableBlockRows_range (first third normal : Nat) :
    variableBlockRows first third normal=(List.range (normal+1)).flatMap
      (fun j => pairRows (first+j) (if j=normal then first else first+j+1) (third+j)) := by
  rw [variableBlockRows,variableRows_range,List.range_succ,List.flatMap_append]
  simp only [List.flatMap_cons,List.flatMap_nil,if_true,List.append_nil]
  congr 1
  apply List.flatMap_congr
  intro j member
  have less := List.mem_range.mp member
  simp [show j≠normal by omega,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem variableBlocksRows_range (first third normal count : Nat) :
    variableBlocksRows first third normal count=(List.range count).flatMap
      (fun v => variableBlockRows (first+v*(normal+1)) (third+v*(normal+1)) normal) := by
  induction count generalizing first third with
  | zero => rfl
  | succ count ih =>
    rw [variableBlocksRows,ih,List.range_succ_eq_map]
    simp only [List.flatMap_cons,List.flatMap_map,Nat.zero_mul,Nat.add_zero]
    congr 1
    apply congrArg (fun f => (List.range count).flatMap f)
    funext v
    congr 1 <;> simp only [Nat.succ_eq_add_one] <;> ring

theorem variableBlocksRows_coordinates (n m : Nat) :
    variableBlocksRows 0 (ThreeSAT.slotCount n m) (3*m) n=ThreeSAT.variableRawRows n m := by
  rw [variableBlocksRows_range,←List.map_coe_finRange_eq_range (n:=n),List.flatMap_map]
  unfold ThreeSAT.variableRawRows
  apply List.flatMap_congr
  intro v _member
  simp only [Nat.zero_add]
  rw [variableBlockRows_range,←List.map_coe_finRange_eq_range (n:=3*m+1),List.flatMap_map]
  apply List.flatMap_congr
  intro j _member
  by_cases last : j.val=3*m <;> simp [pairRows,last,Nat.add_assoc]

theorem literalRows_ofFn (first width shift occurrence count : Nat) (literals : Fin count → Nat × Bool) :
    literalRows first width shift occurrence (List.ofFn literals) =
      List.ofFn (fun p => literalEdge first (literals p).1 width (occurrence+p.val) shift (literals p).2) := by
  induction count generalizing occurrence with
  | zero => simp [literalRows]
  | succ count ih =>
    rw [List.ofFn_succ,literalRows,ih,List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext p
    simp only [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]

theorem clauseRows_ofFn (first width shift occurrence count : Nat) (clauses : Fin count → List (Nat × Bool)) :
    clauseRows first width shift occurrence (List.ofFn clauses) =
      (List.ofFn (fun c => literalRows (first+c.val) width shift (occurrence+3*c.val) (clauses c))).flatten := by
  induction count generalizing first occurrence with
  | zero => simp [clauseRows]
  | succ count ih =>
    rw [List.ofFn_succ,clauseRows,ih,List.ofFn_succ,List.flatten_cons]
    simp only [Fin.val_zero,Nat.add_zero,Nat.mul_zero]
    congr 1
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext c
    congr 1 <;> simp only [Fin.val_succ] <;> omega

theorem clauseRows_coordinates {n m : Nat} (formula : ThreeSAT n m) :
    clauseRows (ThreeSAT.slotCount n m) (3*m+1) (ThreeSAT.slotCount n m) 0
      (formula.toCNF.map (List.map CNFEncoding.literalRaw)) = formula.clauseRawRows := by
  simp only [ThreeSAT.toCNF,List.finRange,List.map_ofFn,Function.comp_def]
  rw [clauseRows_ofFn]
  simp_rw [literalRows_ofFn]
  simp only [ThreeSAT.clauseRawRows,List.finRange,List.map_ofFn,
    CNFEncoding.literalRaw,literalEdge,portValue,Nat.zero_add]
  congr 1
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext c
  apply congrArg List.ofFn
  funext p
  simp only [Nat.add_assoc]
  rfl

end Counting.External.MatchingMachine
