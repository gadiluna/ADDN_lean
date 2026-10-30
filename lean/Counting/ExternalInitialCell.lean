import Counting.ExternalInitialSelect
import Counting.ExternalInitialCleanup

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Compute the initial-cell flags, emit the selected finite template, and clean the flags. -/
def initialCell (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  sequence (initialPrepare extra w) (sequence (initialSelect extra w program)
    (scaleMany (extra+21) (w 13) (w 20) 0 (initialTargets w)))

def initialCellBound (program : Machine.Program) (place offset headerLength capacity : Nat) :=
  initialCoefficient program*(place+1)^2+37*place+19*offset+24*headerLength+18*capacity+115

theorem selectedKind_initial (place offset capacity : Nat) (header : List Bool) :
    selectedKind (decide (offset≤place)) (header[place-offset]?)
      (decide (header.length+capacity ≤ place-offset))=initialKind place offset header capacity := by
  by_cases after : offset≤place
  · cases found : header[place-offset]? <;> simp [selectedKind,initialKind,after,found]
  · simp [selectedKind,initialKind,after]

theorem initialCell_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (place offset capacity : Nat) (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (capacityValue : store (w 3)=List.replicate capacity true)
    (empty : ∀ i ∈ ([6,7,8,9,10,11,12,13,14,15,17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialCellBound program place offset (store (w 2)).length capacity,
      Executes (initialCell extra w program) store transitions
        (Function.update store (w 5)
          (initialBytes program (decide (place=offset)) (initialKind place offset (store (w 2)) capacity) place++store (w 5))) := by
  let prepared := initialPrepared w store place offset capacity
  let payload := initialBytes program (decide (place=offset))
    (initialKind place offset (store (w 2)) capacity) place++store (w 5)
  let emitted := Function.update prepared (w 5) payload
  obtain ⟨prepareTime,prepareBound,prepareRun⟩ := initialPrepare_executes extra w place offset capacity store
    placeValue offsetValue capacityValue (fun i hi => empty i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  obtain ⟨selectTime,selectBound,selectRun⟩ := initialSelect_executes extra w program
    (decide (place=offset)) (decide (offset≤place)) (decide ((store (w 2)).length+capacity ≤ place-offset))
    ((store (w 2))[place-offset]?) place prepared
    (by simp [prepared,initialPrepared,w.injective.eq_iff,placeValue])
    (by simp [prepared,initialPrepared,w.injective.eq_iff])
    (by simp [prepared,initialPrepared,w.injective.eq_iff])
    (by simp [prepared,initialPrepared,w.injective.eq_iff])
    (by simp [prepared,initialPrepared,w.injective.eq_iff])
    (by simp [prepared,initialPrepared])
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals
        simp [prepared,initialPrepared,w.injective.eq_iff]
        apply empty
        simp)
  have selected : Executes (initialSelect extra w program) prepared selectTime emitted := by
    simpa [emitted,payload,selectedKind_initial,prepared,initialPrepared,w.injective.eq_iff] using selectRun
  have cleanupRun := scaleMany_executes (extra+21) (w 13) (w 20) 0 (initialTargets w)
    (initialTargets_unique w) (by simp [initialTargets,w.injective.eq_iff])
    (by simp [initialTargets,w.injective.eq_iff]) (by simp [w.injective.eq_iff]) emitted
    (by simp [emitted,prepared,initialPrepared,w.injective.eq_iff,empty 13 (by simp)])
    (by simp [emitted,prepared,initialPrepared,w.injective.eq_iff,empty 20 (by simp)])
  have cleaned : scaledStore (initialTargets w) 0 emitted=Function.update store (w 5) payload :=
    initial_cleanup w store place offset capacity payload (fun i hi => empty i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  rw [cleaned] at cleanupRun
  have cleanupBound := scaleManyCost_bound (initialTargets w) 0 emitted
    (place+(store (w 2)).length+capacity+1) (by
      intro r member
      have ne : r ≠ w 5 := by
        intro same
        simp [same,initialTargets,w.injective.eq_iff] at member
      simpa [emitted,ne,prepared] using initialPrepared_length w store place offset capacity r member)
  have combined := prepareRun.sequence (selected.sequence cleanupRun)
  refine ⟨prepareTime+1+(selectTime+1+scaleManyCost (initialTargets w) 0 emitted),?_,combined⟩
  have targetsLength : (initialTargets w).length=7 := rfl
  rw [targetsLength] at cleanupBound
  norm_num only at cleanupBound
  unfold initialCellBound
  omega

end Counting.External.CookLevin.StackGenerator
