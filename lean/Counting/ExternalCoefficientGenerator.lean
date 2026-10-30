import Counting.ExternalCoefficientInputSemantics
import Counting.ExternalCoefficientFinish
import Counting.ExternalCoverPrepare

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 32768

def coefficientGenerator (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (CoverMachine.coverPrepare extra w)
    (sequence (move (extra+61) (w 23) (w 43) (w 20))
      (sequence (emitCoefficientHeader extra w)
        (sequence (coefficientStream extra w) (finishCoefficients extra w))))

def generatorCost (input q count output : Nat) :=
  4000*(input+3*q+1)^3+1+(6*count+4+1+
    (100*(count+2)^2+1+(streamCost q count input+1+(2*output+4))))

theorem coefficientGenerator_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (input : X3CEncoding.Input)
    (source : store (w 0)=X3CEncoding.codec.encode input) (status : store (w 1)=[true])
    (universeCounter : store (w 17)=List.replicate (3*input.1) true)
    (rowCounter : store (w 25)=List.replicate input.2.1 true)
    (empty : ∀ i∈MatchingMachine.generatorScratch,store (w i)=[]) :
    ∃ time ≤ generatorCost (store (w 0)).length input.1 input.2.1
        ((Encoding.list Encoding.natural).encode (inputCoefficients input)).length,
      ∃ result,Executes (coefficientGenerator extra w) store time result ∧
        result (w 1)=(Encoding.list Encoding.natural).encode (inputCoefficients input) := by
  let q:=input.1
  let count:=input.2.1
  let raw:=X3CEncoding.toRaw input
  have initialEmpty (i : Fin 64) (h0 : i≠0) (h1 : i≠1) (hu : i≠17) (hm : i≠25) (hw : i≠31) (hb : i≠51) :
      store (w i)=[] := empty i (by simp [MatchingMachine.generatorScratch,h0,h1,hu,hm,hw,hb])
  have preparationEmpty (i : Fin 64) (member : i∈CoverMachine.coverPrepareScratch) : store (w i)=[] := by
    fin_cases i <;> simp [CoverMachine.coverPrepareScratch] at member ⊢
    all_goals simp [initialEmpty]
  have rawSource : store (w 0)=ThreeDMEncoding.rawCodec.encode raw := source
  obtain ⟨prepareTime,prepareBound,preparing⟩:=CoverMachine.coverPrepare_executes extra w store raw true [] rawSource status preparationEmpty
  have rawUniverse : raw.1.length=3*q := by simp [raw,X3CEncoding.toRaw,q]
  have rawCount : raw.2.length=count := by simp [raw,X3CEncoding.toRaw,count]
  rw [rawUniverse] at prepareBound
  let prepared:=Function.update (Function.update store (w 0)
    (Encoding.sequence (Encoding.list Encoding.natural) raw.2)) (w 23) (List.replicate count true)
  rw [rawCount] at preparing
  have moving:=move_executes (extra+61) (w 23) (w 43) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) prepared
    (by simp [prepared,w.injective.eq_iff,initialEmpty])
  have moveSource : prepared (w 23)=List.replicate count true := by simp [prepared]
  have moveTarget : prepared (w 43)=[] := by simp [prepared,w.injective.eq_iff,initialEmpty]
  rw [moveSource,moveTarget,List.append_nil,List.length_replicate] at moving
  let counted:=Function.update (Function.update store (w 0)
    (Encoding.sequence (Encoding.list Encoding.natural) raw.2)) (w 43) (List.replicate count true)
  have moved : Function.update (Function.update prepared (w 43) (List.replicate count true)) (w 23) []=counted := by
    funext r
    by_cases e23 : r=w 23
    · subst r;simp [counted,w.injective.eq_iff,initialEmpty]
    · simp [counted,prepared,Function.update_apply,e23]
  rw [moved] at moving
  have headerEmpty (i : Fin 64) (member : i∈headerScratch) : counted (w i)=[] := by
    fin_cases i <;> simp [headerScratch] at member ⊢
    all_goals simp [counted,w.injective.eq_iff,initialEmpty]
  obtain ⟨headerTime,headerBound,headerRun⟩:=emitCoefficientHeader_executes extra w counted headerEmpty
  have countAt : (counted (w 25)).length=count := by simp [counted,w.injective.eq_iff,rowCounter,count]
  have outputAt : counted (w 36)=[] := by simp [counted,w.injective.eq_iff,initialEmpty]
  rw [countAt] at headerBound headerRun
  rw [outputAt,List.append_nil] at headerRun
  let headerStore:=Function.update counted (w 36) (Encoding.natural.encode (count+1)).reverse
  have streamEmpty (i : Fin 64) (member : i∈streamScratch) : headerStore (w i)=[] := by
    have exclude : i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠31 ∧ i≠51 ∧ i≠43 ∧ i≠36 := by
      fin_cases i <;> simp [streamScratch,parameterScratch,baseScratch,highScratch,baselineScratch,
        productScratch,geometricScratch,rowScratch,tripleScratch,atomScratch] at member ⊢
    simp [headerStore,counted,w.injective.eq_iff,exclude.1,exclude.2.2.2.2.2.2.1,exclude.2.2.2.2.2.2.2,
      initialEmpty i exclude.1 exclude.2.1 exclude.2.2.1 exclude.2.2.2.1 exclude.2.2.2.2.1 exclude.2.2.2.2.2.1]
  have streamBound : (headerStore (w 0)).length ≤ (store (w 0)).length := by
    rw [rawSource]
    simp only [headerStore,counted,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 64)≠36)),
      Function.update_of_ne (w.injective.ne (by decide : (0:Fin 64)≠43)),Function.update_self,
      ThreeDMEncoding.rawCodec,Encoding.product,Encoding.list,List.length_append]
    omega
  obtain ⟨streamTime,streamBoundTime,streamRun⟩:=coefficientStream_executes extra w headerStore q (store (w 0)).length raw.2 true [] []
    (by simp [headerStore,counted,w.injective.eq_iff])
    (by simp [headerStore,counted,w.injective.eq_iff,rawCount])
    (by simp [headerStore,counted,w.injective.eq_iff,status])
    (by simp [headerStore,counted,w.injective.eq_iff,universeCounter,q]) streamBound
    (input_rows_three input) (input_rows_fit input) (input_rows_size_all input) streamEmpty
  let streamed:=coefficientStreamResult w headerStore q raw.2 []
  let output:=(Encoding.list Encoding.natural).encode (inputCoefficients input)
  have streamOutput : streamed (w 36)=output.reverse := by
    simp only [streamed,coefficientStreamResult,Function.update_self,headerStore]
    have countValues : (coefficientValues q raw.2).length=count+1 := by simp [coefficientValues,rawCount]
    change (Encoding.sequence Encoding.natural (coefficientValues q raw.2)).reverse++
      (Encoding.natural.encode (count+1)).reverse=
      ((Encoding.list Encoding.natural).encode (coefficientValues q raw.2)).reverse
    simp only [Encoding.list,countValues,List.reverse_append]
  have finishRun:=finishCoefficients_executes extra w streamed output streamOutput
  have finalStatus : streamed (w 1)=[true] := by
    simp [streamed,coefficientStreamResult,headerStore,counted,w.injective.eq_iff,status]
  rw [finalStatus] at finishRun
  simp only [List.length_cons,List.length_nil] at finishRun
  have finishAs : Executes (finishCoefficients extra w) streamed (2*output.length+4)
      (Function.update (Function.update streamed (w 36) []) (w 1) output) := by
    convert finishRun using 1; omega
  refine ⟨prepareTime+1+(6*count+4+1+(headerTime+1+(streamTime+1+(2*output.length+4)))),?_,_,
    preparing.sequence (moving.sequence (headerRun.sequence (streamRun.sequence finishAs))),by simp [output]⟩
  rw [rawCount] at streamBoundTime
  change _ ≤ generatorCost (store (w 0)).length q count output.length
  unfold generatorCost
  omega

end Counting.External.CoefficientMachine
