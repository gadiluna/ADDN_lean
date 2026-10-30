import Counting.ExternalCoverInputRaw
import Counting.StackUnaryDivisibleThree

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def universeGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 17) (w 27) (w 3)))
    (sequence (divisibleThree (w 27) (w 1)) (ofProgram (combineFlagsProgram (extra+30) (w 1))))

theorem universeGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (n : Nat) (accepted : Bool) (tail : List Bool)
    (count : store (w 17)=List.replicate n true) (status : store (w 1)=accepted::tail)
    (scratch : store (w 3)=[]) (empty : store (w 27)=[]) :
    Executes (universeGuard extra w) store (6*n+9)
      (Function.update store (w 1) ((accepted && decide (n%3=0))::tail)) := by
  have copying:=copy_executes (extra+29) (w 17) (w 27) (w 3)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store scratch
  rw [count,empty,List.append_nil,List.length_replicate] at copying
  let copied:=Function.update store (w 27) (List.replicate n true)
  have division:=divisibleThree_executes (w 27) (w 1) (by simp [w.injective.eq_iff]) n copied (by simp [copied])
  have restored : Function.update copied (w 27) []=store := by
    simp only [copied,Function.update_idem];rw [←empty,Function.update_eq_self]
  rw [restored] at division
  have flag : copied (w 1)=accepted::tail:=by simp [copied,w.injective.eq_iff,status]
  rw [flag] at division
  let checked:=Function.update store (w 1) (decide (n%3=0)::accepted::tail)
  have combining:=combineFlags_executes (extra+30) (w 1) checked accepted (decide (n%3=0)) tail (by simp [checked])
  simp only [checked,Function.update_idem] at combining
  have executed:=copying.sequence (division.sequence combining)
  convert executed using 1 <;> first | rfl | omega

theorem baseStatus_mod (raw : MatchingVerification.Raw) :
    (baseStatus raw && decide (raw.1.length%3=0))=rawStatus raw := by
  apply Bool.eq_iff_iff.mpr
  simp only [baseStatus,rowsRange,rowRange,rawStatus,MatchingInputValidation.rawStatus,
    MatchingInputValidation.rowsRange,MatchingInputValidation.rowRange,extraStatus,
    Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨markers,rows⟩,divisible⟩
    exact ⟨⟨markers,fun row member=>(rows row member).1⟩,divisible,
      fun row member=>(rows row member).2⟩
  · rintro ⟨⟨markers,ranges⟩,divisible,orders⟩
    exact ⟨⟨markers,fun row member=>⟨ranges row member,orders row member⟩⟩,divisible⟩

def rawGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (baseGuard extra w) (universeGuard extra w)

theorem rawGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (raw : MatchingVerification.Raw) (suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=MatchingVerification.rawCodec.encode raw++suffix)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈rawScratch,store (w i)=[]) :
    ∃ time ≤ 300010*((store (w 0)).length+1)^5,
      Executes (rawGuard extra w) store time
        (Function.update (Function.update (Function.update (Function.update store
          (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
          (w 0) suffix) (w 1) ((accepted && rawStatus raw)::tail)) := by
  obtain ⟨time,bound,execution⟩:=baseGuard_executes extra w raw suffix tail store accepted source status empty
  let checked:=Function.update (Function.update (Function.update (Function.update store
    (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
    (w 0) suffix) (w 1) ((accepted && baseStatus raw)::tail)
  have division:=universeGuard_executes extra w checked raw.1.length (accepted && baseStatus raw) tail
    (by simp [checked,w.injective.eq_iff]) (by simp [checked])
    (by simp [checked,w.injective.eq_iff,empty,rawScratch,prefixScratch,tripleScratch,MatchingInputValidation.indexScratch])
    (by simp [checked,w.injective.eq_iff,empty,rawScratch,prefixScratch])
  simp only [checked,Function.update_idem,Bool.and_assoc,baseStatus_mod] at division
  have size : raw.1.length ≤ (store (w 0)).length := by
    rw [source]
    change raw.1.length ≤ (((Encoding.list Encoding.boolean).encode raw.1++
      (Encoding.list MatchingVerification.clauseCodec).encode raw.2)++suffix).length
    simp only [List.length_append,Encoding.list_length]
    have table : (raw.1.map (fun bit=>(Encoding.boolean.encode bit).length)).sum=raw.1.length := by
      simp [Encoding.boolean]
    rw [table]
    omega
  have linear : (store (w 0)).length+1 ≤ ((store (w 0)).length+1)^5:=Nat.le_self_pow (by decide) _
  refine ⟨time+1+(6*raw.1.length+9),?_,execution.sequence division⟩
  omega

end Counting.External.CoverInputValidation
