import Counting.ExternalMatchingFinalize

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- The output headers are measured by copying the actual unary universe and
retained-row counters, then charging the six new elements and two new rows. -/
def finish (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 48) (w 59)))
    (sequence (prepend (w 48) (List.replicate 6 true))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 41) (w 50) (w 59)))
        (sequence (prepend (w 50) [true,true]) (matchingFinalize extra w))))

def finishCost (u kept streamLength : Nat) :=
  5*u+5*kept+30+matchingFinalizeCost (u+6) (kept+2) streamLength

def finishResult (w : GeneratorWorkspace extra) (store : Fin (extra+64)→List Bool)
    (u kept : Nat) (stream : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store
    (w 48) (List.replicate (u+6) true)) (w 50) (List.replicate (kept+2) true))
    (w 36) []) (w 1)
      ((Encoding.list Encoding.boolean).encode (List.replicate (u+6) true)++
        Encoding.natural.encode (kept+2)++stream)

theorem finish_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64)→List Bool) (u kept : Nat) (stream : List Bool) (flag : Bool)
    (universeValue : store (w 17)=List.replicate u true)
    (countValue : store (w 41)=List.replicate kept true)
    (output : store (w 36)=stream.reverse) (status : store (w 1)=[flag])
    (empty : ∀ i∈([18,19,48,50,59] : List (Fin 64)),store (w i)=[]) :
    ∃ time ≤ finishCost u kept stream.length,
      Executes (finish extra w) store time (finishResult w store u kept stream) := by
  have copyingU := copy_executes (extra+61) (w 17) (w 48) (w 59)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) store (empty 59 (by simp))
  rw [universeValue,empty 48 (by simp),List.append_nil,List.length_replicate] at copyingU
  let copiedU := Function.update store (w 48) (List.replicate u true)
  have addingU := prepend_executes (w 48) (List.replicate 6 true) copiedU
  let paddedU := Function.update store (w 48) (List.replicate (u+6) true)
  have addingUAs : Executes (prepend (w 48) (List.replicate 6 true)) copiedU 12 paddedU := by
    have joined : List.replicate 6 true++List.replicate u true=List.replicate (u+6) true := by
      rw [←List.replicate_add,Nat.add_comm]
    simpa only [copiedU,Function.update_self,joined,Function.update_idem,paddedU,List.length_replicate] using addingU
  have copyingK := copy_executes (extra+61) (w 41) (w 50) (w 59)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) paddedU
    (by simp [paddedU,w.injective.eq_iff,empty])
  let copiedK := Function.update paddedU (w 50) (List.replicate kept true)
  have copyingKAs : Executes (ofProgram (ListPrograms.copyProgram (extra+61) (w 41) (w 50) (w 59)))
      paddedU (5*kept+2) copiedK := by
    simpa [paddedU,copiedK,w.injective.eq_iff,countValue,empty] using copyingK
  let paddedK := Function.update paddedU (w 50) (List.replicate (kept+2) true)
  have addingK := prepend_executes (w 50) [true,true] copiedK
  have addingKAs : Executes (prepend (w 50) [true,true]) copiedK 4 paddedK := by
    have joined : [true,true]++List.replicate kept true=List.replicate (kept+2) true := by
      change List.replicate 2 true++List.replicate kept true=_
      rw [←List.replicate_add,Nat.add_comm]
    simpa only [copiedK,Function.update_self,joined,Function.update_idem,paddedK,List.length_cons,List.length_nil] using addingK
  obtain ⟨lastTime,lastBound,finalizing⟩ := matchingFinalize_executes extra w (u+6) (kept+2) stream flag paddedK
    (by simp [paddedK,paddedU,w.injective.eq_iff])
    (by simp [paddedK])
    (by simp [paddedK,paddedU,w.injective.eq_iff,output])
    (by simp [paddedK,paddedU,w.injective.eq_iff,status])
    (by simp [paddedK,paddedU,w.injective.eq_iff,empty])
    (by simp [paddedK,paddedU,w.injective.eq_iff,empty])
    (by simp [paddedK,paddedU,w.injective.eq_iff,empty])
  have combined := copyingU.sequence (addingUAs.sequence (copyingKAs.sequence (addingKAs.sequence finalizing)))
  refine ⟨_,?_,combined⟩
  dsimp only [finishCost]
  omega

end Counting.External.CoverNormalization
