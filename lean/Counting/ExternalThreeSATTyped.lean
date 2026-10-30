import Counting.ExternalThreeSATEncoding
import Counting.ExternalThreeSATSparseCoordinates
import Counting.ExternalThreeDMEncoding

namespace Counting.External.CNFMachine

/-- Reading a checked exact-three CNF changes only its indexing interface. -/
def asThreeSAT (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) : ThreeSAT input.1 input.2.length where
  literal c p := input.2[c.val][p.val]'(by
    rw [three _ (List.getElem_mem c.isLt)]
    exact p.isLt)

theorem asThreeSAT_toCNF (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    (asThreeSAT input three).toCNF=input.2 := by
  unfold ThreeSAT.toCNF
  apply List.ext_getElem
  · simp
  · intro index left right
    simp only [List.getElem_map]
    apply List.ext_getElem
    · simp [three _ (List.getElem_mem right)]
    · intro p hp hq
      simp [asThreeSAT]

theorem asThreeSAT_yes_iff (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    (asThreeSAT input three).Yes ↔ input.2.Satisfiable := by
  rw [←ThreeSAT.toCNF_satisfiable,asThreeSAT_toCNF]

end Counting.External.CNFMachine

namespace Counting.External.ThreeSAT

def sparseInput {n m : Nat} (formula : ThreeSAT n m) : ThreeDMEncoding.Input :=
  ⟨2*slotCount n m,formula.sparseEdges.length,formula.toSparseThreeDM⟩

theorem sparseInput_yes_iff {n m : Nat} (formula : ThreeSAT n m) : formula.sparseInput.2.2.Yes ↔ formula.Yes :=
  formula.toSparseThreeDM_yes_iff

theorem sparseInput_toRaw {n m : Nat} (formula : ThreeSAT n m) :
    ThreeDMEncoding.toRaw formula.sparseInput=(List.replicate (2*slotCount n m) true,formula.sparseRawRows) := by
  apply Prod.ext
  · rfl
  · change (List.ofFn (fun j=>formula.toSparseThreeDM.edge j)).map ThreeDMEncoding.tripleRaw= formula.sparseRawRows
    rw [List.map_ofFn]
    have row (j : Fin formula.sparseEdges.length) :
        ThreeDMEncoding.tripleRaw (formula.toSparseThreeDM.edge j)=
          [formula.sparseEdges[j.val].1.val,formula.sparseEdges[j.val].2.1.val,formula.sparseEdges[j.val].2.2.val] := by
      simp [ThreeDMEncoding.tripleRaw,toSparseThreeDM,listToThreeDM]
    simp only [Function.comp_def,row]
    simpa only [List.map_ofFn,Function.comp_def,sparseRawRows] using
      congrArg (List.map (fun edge : MatchingEdge (2*slotCount n m)=>[edge.1.val,edge.2.1.val,edge.2.2.val]))
        (List.ofFn_getElem (xs := formula.sparseEdges))

end Counting.External.ThreeSAT
