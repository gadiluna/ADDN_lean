import Counting.ExternalCNFFormulaPrepare
import Counting.ExternalCNFGeneratedSize
import Counting.ExternalCNFFinalize

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

def generatorScratch : List (Fin 52) := formulaPrepareScratch++generatorClauseScratch++[19,42]

def formulaGenerator (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (formulaPrepare extra w)
    (sequence (generatorFormulaLoop extra w) (formulaFinalize extra w))

def formulaGeneratorCost (sourceLength n m width streamLength : Nat) :=
  let index := n+m*(width+1)
  4000*(sourceLength+n+1)^3+1+
    (m*(50000*(sourceLength+index+width+formulaCodeLimit sourceLength index width+2)^3+2)+1+1+
      formulaFinalizeCost m width index streamLength)

theorem formulaGenerator_executes (extra : Nat) (w : ClauseWorkspace extra)
    (store : Fin (extra+52) → List Bool) (raw : CNFEncoding.Raw)
    (source : store (w 0)=CNFEncoding.rawCodec.encode raw) (status : store (w 1)=[true])
    (population : store (w 17)=List.replicate raw.1.length true)
    (count : store (w 25)=List.replicate raw.2.length true)
    (widthEq : store (w 47)=List.replicate (rawWidth raw.2) true)
    (empty : ∀ i∈generatorScratch,store (w i)=[]) :
    ∃ time ≤ formulaGeneratorCost (store (w 0)).length raw.1.length raw.2.length (rawWidth raw.2)
        (Encoding.sequence (Encoding.list literalCodec) (formulaRows raw.1.length (rawWidth raw.2) raw.2)).length,
      ∃ result, Executes (formulaGenerator extra w) store time result ∧
        result (w 1)=CNFEncoding.rawCodec.encode
          (List.replicate (raw.1.length+raw.2.length*(rawWidth raw.2+1)) true,
            formulaRows raw.1.length (rawWidth raw.2) raw.2) := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := formulaPrepare_executes extra w store raw true [] source status population
    (fun i member=>empty i (by simp [generatorScratch,member]))
  let prepared := Function.update (Function.update (Function.update store (w 0)
    (Encoding.sequence (Encoding.list literalCodec) raw.2)) (w 23) (List.replicate raw.2.length true))
    (w 34) (List.replicate raw.1.length true)
  have preparedSource : prepared (w 0)=Encoding.sequence (Encoding.list literalCodec) raw.2++[] := by
    simp [prepared,w.injective.eq_iff]
  have preparedBound : (prepared (w 0)).length ≤ (store (w 0)).length := by
    rw [preparedSource,source]
    simp only [List.append_nil,CNFEncoding.rawCodec,Encoding.product,Encoding.list,List.length_append]
    omega
  have preparedEmpty (i : Fin 52) (member : i∈generatorClauseScratch) : prepared (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [generatorClauseScratch] at member
    have b : i≠23 := by intro equal;subst i;simp [generatorClauseScratch] at member
    have c : i≠34 := by intro equal;subst i;simp [generatorClauseScratch] at member
    simp [prepared,w.injective.eq_iff,a,b,c,empty i (by simp [generatorScratch,member])]
  obtain ⟨loopTime,loopBound,looping⟩ := generatorFormulaLoop_executes extra w raw.2 (rawWidth raw.2)
    (store (w 0)).length (raw.1.length+raw.2.length*(rawWidth raw.2+1)) prepared true [] [] preparedSource preparedBound
    (by simp [prepared,w.injective.eq_iff]) (by simp [prepared,w.injective.eq_iff,status])
    (by simp [prepared,w.injective.eq_iff,widthEq]) (by simp [prepared])
    (rawWidth_member raw.2) preparedEmpty
  let looped := formulaResult extra w prepared (rawWidth raw.2) raw.2 []
  let index := raw.1.length+raw.2.length*(rawWidth raw.2+1)
  let stream := Encoding.sequence (Encoding.list literalCodec) (formulaRows raw.1.length (rawWidth raw.2) raw.2)
  have loopedIndex : looped (w 34)=List.replicate index true := by
    simp [looped,formulaResult,prepared,w.injective.eq_iff,index,Nat.add_comm]
  have loopedOutput : looped (w 42)=stream.reverse := by
    simp [looped,formulaResult,prepared,w.injective.eq_iff,stream,empty 42 (by simp [generatorScratch])]
  have loopedEmpty (i : Fin 52) (member : i∈([18,19,45,49,50,51] : List (Fin 52))) : looped (w i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [looped,formulaResult,prepared,w.injective.eq_iff,empty,generatorScratch,formulaPrepareScratch,generatorClauseScratch]
  obtain ⟨finalTime,finalBound,finalizing⟩ := formulaFinalize_executes extra w looped raw.2.length (rawWidth raw.2) index stream true
    (by simp [looped,formulaResult,prepared,w.injective.eq_iff,count])
    (by simp [looped,formulaResult,prepared,w.injective.eq_iff,widthEq]) loopedIndex loopedOutput
    (by simp [looped,formulaResult,prepared,w.injective.eq_iff,status]) loopedEmpty
  have combined := preparing.sequence (looping.sequence finalizing)
  refine ⟨prepareTime+1+(loopTime+1+finalTime),?_,_,combined,?_⟩
  · change _ ≤ 4000*((store (w 0)).length+raw.1.length+1)^3+1+(_+1+formulaFinalizeCost _ _ index stream.length)
    omega
  · simp only [Function.update_self,CNFEncoding.rawCodec,Encoding.product,Encoding.list,formulaRows_length]
    change (_++_++stream)=(_++(_++stream))
    rw [List.append_assoc]

end Counting.External.CNFMachine
