import Counting.ExternalMatchingPrepare
import Counting.ExternalMatchingVariablePart
import Counting.ExternalMatchingClausePart
import Counting.ExternalMatchingCompletionPart
import Counting.ExternalMatchingFinalize

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 65536

def matchingRows (n : Nat) (clauses : List (List (Nat×Bool))) : List (List Nat) :=
  let m := clauses.length
  let s := MatchingDimensions.slots n m
  variableBlocksRows 0 s (3*m) n++clauseRows s (3*m+1) s 0 clauses++
    completionRows (s+m) (s+m) (MatchingDimensions.order n m) (MatchingDimensions.garbage n m)

def matchingGenerator (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (MatchingDimensions.routine (extra+52) w.dimensions)
    (sequence (matchingPrepare extra w) (sequence (variablePart extra w)
      (sequence (clausePart extra w) (sequence (completionPart extra w) (matchingFinalize extra w)))))

def matchingGeneratorCost (input n m streamLength : Nat) :=
  let s := MatchingDimensions.slots n m
  MatchingDimensions.cost n m+1+(4000*(input+n+1)^3+1+(variablePartCost n m s+1+
    (clausePartCost input n m (3*m+1) s+1+(completionPartCost (s+m) (MatchingDimensions.order n m)
      (MatchingDimensions.garbage n m)+1+matchingFinalizeCost (MatchingDimensions.order n m)
        (MatchingDimensions.edges n m) streamLength))))

theorem matchingGenerator_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (raw : CNFEncoding.Raw)
    (source : store (w 0)=CNFEncoding.rawCodec.encode raw) (status : store (w 1)=[true])
    (nValue : store (w 17)=List.replicate raw.1.length true)
    (mValue : store (w 25)=List.replicate raw.2.length true)
    (three : ∀ clause∈raw.2,clause.length=3)
    (fits : ∀ clause∈raw.2,∀ literal∈clause,literal.1≤raw.1.length)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ matchingGeneratorCost (store (w 0)).length raw.1.length raw.2.length
        (Encoding.sequence (Encoding.list Encoding.natural) (matchingRows raw.1.length raw.2)).length,
      ∃ result,Executes (matchingGenerator extra w) store time result ∧
        result (w 1)=(Encoding.list Encoding.boolean).encode (List.replicate (MatchingDimensions.order raw.1.length raw.2.length) true)++
          Encoding.natural.encode (MatchingDimensions.edges raw.1.length raw.2.length)++
            Encoding.sequence (Encoding.list Encoding.natural) (matchingRows raw.1.length raw.2) := by
  let n := raw.1.length
  let m := raw.2.length
  let s := MatchingDimensions.slots n m
  let q := MatchingDimensions.order n m
  let g := MatchingDimensions.garbage n m
  let e := MatchingDimensions.edges n m
  have initialEmpty (i : Fin 64) (h0 : i≠0) (h1 : i≠1) (hn : i≠17) (hm : i≠25) (hw : i≠31) (hb : i≠51) : store (w i)=[] :=
    empty i (by simp [generatorScratch,h0,h1,hn,hm,hw,hb])
  have dimensionEmpty (i : Fin 12) (h0 : i≠0) (h1 : i≠1) : store (w.dimensions i)=[] := by
    fin_cases i <;> simp_all [GeneratorWorkspace.dimensions,generatorDimensionPositions]
  have dimensions := MatchingDimensions.routine_executes (extra+52) w.dimensions n m store nValue mValue dimensionEmpty
  let sD := MatchingDimensions.result w.dimensions n m store
  have dSource : sD (w 0)=CNFEncoding.rawCodec.encode raw := by
    simp [sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,source]
  have dStatus : sD (w 1)=[true] := by
    simp [sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,status]
  have dEmpty (i : Fin 64) (member : i∈matchingPrepareScratch) : sD (w i)=[] := by
    fin_cases i <;> simp [matchingPrepareScratch] at member ⊢
    all_goals simp [sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty]
  obtain ⟨prepareTime,prepareBound,preparing⟩ := matchingPrepare_executes extra w sD raw true [] dSource dStatus dEmpty
  let sP := Function.update (Function.update sD (w 0)
    (Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) raw.2)) (w 23) (List.replicate m true)
  have preparedBound : (sP (w 0)).length≤(store (w 0)).length := by
    rw [source]
    simp only [sP,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 64)≠23)),Function.update_self,
      CNFEncoding.rawCodec,Encoding.product,Encoding.list,List.length_append]
    omega
  have variableEmpty (i : Fin 64) (member : i∈variablePartScratch) : sP (w i)=[] := by
    fin_cases i <;> simp [variablePartScratch] at member ⊢
    all_goals simp [sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty]
  obtain ⟨variableTime,variableBound,variableRun⟩ := variablePart_executes extra w n m s sP
    (by simp [sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,nValue,n])
    (by simp [sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,mValue,m])
    (by simp [sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,s]) variableEmpty
  let variableStream := Encoding.sequence (Encoding.list Encoding.natural) (variableBlocksRows 0 s (3*m) n)
  let sV := Function.update sP (w 36) (variableStream.reverse++sP (w 36))
  have clauseEmpty (i : Fin 64) (member : i∈clausePartScratch) : sV (w i)=[] := by
    fin_cases i <;> simp [clausePartScratch] at member ⊢
    all_goals simp [sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty]
  obtain ⟨clauseTime,clauseBound,clauseRun⟩ := clausePart_executes extra w n (3*m+1) s raw.2 sV
    (by simp [sV,sP,w.injective.eq_iff])
    (by simp [sV,sP,w.injective.eq_iff,dStatus])
    (by simp [sV,sP,w.injective.eq_iff,m])
    (by simp [sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,nValue,n])
    (by simp [sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff])
    (by simp [sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,s])
    three fits clauseEmpty
  let sC := clausePartResult w sV (3*m+1) s raw.2
  have completionEmpty (i : Fin 64) (member : i∈completionPartScratch) : sC (w i)=[] := by
    fin_cases i <;> simp [completionPartScratch] at member ⊢
    all_goals simp [sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty]
  obtain ⟨completionTime,completionBound,completionRun⟩ := completionPart_executes extra w (s+m) q g sC
    (by simp [sC,clausePartResult,m,w.injective.eq_iff])
    (by simp [sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,q])
    (by simp [sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,g]) completionEmpty
  let stream := Encoding.sequence (Encoding.list Encoding.natural) (matchingRows n raw.2)
  let sF := Function.update sC (w 36) ((Encoding.sequence (Encoding.list Encoding.natural)
    (completionRows (s+m) (s+m) q g)).reverse++sC (w 36))
  have output : sF (w 36)=stream.reverse := by
    simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,
      variableStream,stream,matchingRows,s,q,g,m,w.injective.eq_iff,initialEmpty,sequence_append,List.reverse_append,List.append_assoc]
  obtain ⟨finalTime,finalBound,finalRun⟩ := matchingFinalize_executes extra w q e stream true sF
    (by simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,q])
    (by simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,e]) output
    (by simp [sF,sC,clausePartResult,sV,sP,w.injective.eq_iff,dStatus])
    (by simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty])
    (by simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty])
    (by simp [sF,sC,clausePartResult,sV,sP,sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,initialEmpty])
  have combined := dimensions.sequence (preparing.sequence (variableRun.sequence (clauseRun.sequence (completionRun.sequence finalRun))))
  refine ⟨MatchingDimensions.cost n m+1+(prepareTime+1+(variableTime+1+(clauseTime+1+(completionTime+1+finalTime)))),?_,_,combined,?_⟩
  · have prepareBound' : prepareTime≤4000*((store (w 0)).length+n+1)^3 := by
      simpa [sD,MatchingDimensions.result,GeneratorWorkspace.dimensions,generatorDimensionPositions,w.injective.eq_iff,n] using prepareBound
    have clauseBound' : clauseTime≤clausePartCost (store (w 0)).length n m (3*m+1) s := by
      apply clauseBound.trans
      dsimp only [clausePartCost]
      apply Nat.add_le_add_left
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      have same : (sV (w 0)).length=(sP (w 0)).length := by simp [sV,w.injective.eq_iff]
      rw [same]
      omega
    change _ ≤ MatchingDimensions.cost n m+1+(4000*((store (w 0)).length+n+1)^3+1+(variablePartCost n m s+1+
      (clausePartCost (store (w 0)).length n m (3*m+1) s+1+(completionPartCost (s+m) q g+1+matchingFinalizeCost q e stream.length))))
    omega
  · simp only [Function.update_self,q,e,stream,n,m]

end Counting.External.MatchingMachine
