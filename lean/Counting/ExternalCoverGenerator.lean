import Counting.ExternalCoverCounts
import Counting.ExternalCoverPrepare
import Counting.ExternalCoverRowLoop
import Counting.ExternalMatchingFinalize

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

def coverRowWorkspace (w : GeneratorWorkspace extra) : RowWorkspace (extra+16) := w.literal

def coverGenerator (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (coverCounts extra w) (sequence (coverPrepare extra w)
    (sequence (generateRows (extra+16) (coverRowWorkspace w)) (matchingFinalize extra w)))

def coverGeneratorCost (input q m streamLength : Nat) :=
  15*q+5*m+12+1+(4000*(input+q+1)^3+1+
    (m*(4000*(input+q+1)^3+2)+1+1+matchingFinalizeCost (3*q) m streamLength))

theorem coverGenerator_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (raw : ThreeDMEncoding.Raw)
    (source : store (w 0)=ThreeDMEncoding.rawCodec.encode raw) (status : store (w 1)=[true])
    (qValue : store (w 17)=List.replicate raw.1.length true)
    (mValue : store (w 25)=List.replicate raw.2.length true)
    (three : ∀ row∈raw.2,row.length=3) (fits : ∀ row∈raw.2,∀ index∈row,index≤ raw.1.length)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ coverGeneratorCost (store (w 0)).length raw.1.length raw.2.length
        (Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows raw.1.length raw.2)).length,
      ∃ result,Executes (coverGenerator extra w) store time result ∧
        result (w 1)=(Encoding.list Encoding.boolean).encode (List.replicate (3*raw.1.length) true)++
          Encoding.natural.encode raw.2.length++
            Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows raw.1.length raw.2) := by
  let q := raw.1.length
  let m := raw.2.length
  have initialEmpty (i : Fin 64) (h0 : i≠0) (h1 : i≠1) (hq : i≠17) (hm : i≠25) (hw : i≠31) (hb : i≠51) : store (w i)=[] :=
    empty i (by simp [generatorScratch,h0,h1,hq,hm,hw,hb])
  have counts := coverCounts_executes extra w store q m (by simp [qValue,q]) mValue
    (initialEmpty 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (initialEmpty 50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (initialEmpty 59 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  let sD := Function.update (Function.update store (w 48) (List.replicate (3*q) true)) (w 50) (List.replicate m true)
  have dSource : sD (w 0)=ThreeDMEncoding.rawCodec.encode raw := by simp [sD,w.injective.eq_iff,source]
  have dStatus : sD (w 1)=[true] := by simp [sD,w.injective.eq_iff,status]
  have dEmpty (i : Fin 64) (member : i∈coverPrepareScratch) : sD (w i)=[] := by
    fin_cases i <;> simp [coverPrepareScratch] at member ⊢
    all_goals simp [sD,w.injective.eq_iff,initialEmpty]
  obtain ⟨prepareTime,prepareBound,preparing⟩ := coverPrepare_executes extra w sD raw true [] dSource dStatus dEmpty
  let sP := Function.update (Function.update sD (w 0)
    (Encoding.sequence (Encoding.list Encoding.natural) raw.2)) (w 23) (List.replicate m true)
  have preparedBound : (sP (w 0)).length≤(store (w 0)).length := by
    rw [source]
    simp only [sP,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 64)≠23)),Function.update_self,
      ThreeDMEncoding.rawCodec,Encoding.product,Encoding.list,List.length_append]
    omega
  have rowsEmpty (i : Fin 48) (member : i∈rowScratch) : sP (coverRowWorkspace w i)=[] := by
    fin_cases i <;> simp [rowScratch] at member ⊢
    all_goals simp [coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,sD,w.injective.eq_iff,initialEmpty]
  obtain ⟨rowsTime,rowsBound,rowsRun⟩ := generateRows_executes (extra+16) (coverRowWorkspace w) raw.2 q (store (w 0)).length sP true [] []
    (by simp [coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,w.injective.eq_iff])
    (by simp [coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,m])
    (by simp [coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,w.injective.eq_iff,dStatus])
    (by simp [coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,sD,w.injective.eq_iff,qValue,q])
    preparedBound three fits rowsEmpty
  let sR := rowsResult (coverRowWorkspace w) sP q raw.2 []
  let stream := Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows q raw.2)
  have rowStore (i : Fin 64) (h0 : i≠0) (hc : i≠23) (ho : i≠36) : sR (w i)=sD (w i) := by
    simp [sR,rowsResult,coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,w.injective.eq_iff,h0,hc,ho]
  have rowOutput : sR (w 36)=stream.reverse := by
    simp [sR,rowsResult,coverRowWorkspace,GeneratorWorkspace.literal,literalPositions,sP,sD,w.injective.eq_iff,stream,
      initialEmpty 36 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨finishTime,finishBound,finishing⟩ := matchingFinalize_executes extra w (3*q) m stream true sR
    (by rw [rowStore 48 (by decide) (by decide) (by decide)];simp [sD,w.injective.eq_iff])
    (by rw [rowStore 50 (by decide) (by decide) (by decide)];simp [sD]) rowOutput
    (by rw [rowStore 1 (by decide) (by decide) (by decide)];exact dStatus)
    (by rw [rowStore 18 (by decide) (by decide) (by decide)];simp [sD,w.injective.eq_iff,initialEmpty])
    (by rw [rowStore 19 (by decide) (by decide) (by decide)];simp [sD,w.injective.eq_iff,initialEmpty])
    (by rw [rowStore 59 (by decide) (by decide) (by decide)];simp [sD,w.injective.eq_iff,initialEmpty])
  refine ⟨15*q+5*m+12+1+(prepareTime+1+(rowsTime+1+finishTime)),?_,_,
    counts.sequence (preparing.sequence (rowsRun.sequence finishing)),?_⟩
  · have prepBound : prepareTime≤4000*((store (w 0)).length+q+1)^3 := by
      simpa [sD,w.injective.eq_iff,q] using prepareBound
    change rowsTime≤ m*(4000*((store (w 0)).length+q+1)^3+2)+1 at rowsBound
    dsimp only [coverGeneratorCost]
    change _≤15*q+5*m+12+1+(4000*((store (w 0)).length+q+1)^3+1+
      (m*(4000*((store (w 0)).length+q+1)^3+2)+1+1+matchingFinalizeCost (3*q) m stream.length))
    omega
  · simp only [Function.update_self,List.append_assoc,q,m,stream]

end Counting.External.CoverMachine
