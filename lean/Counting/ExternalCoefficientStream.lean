import Counting.ExternalCoefficientParameters
import Counting.ExternalCoefficientRows

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def streamScratch : List (Fin 64) := parameterScratch++rowScratch
def coefficientStream (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (prepareParameters extra w) (sequence (emitCoefficient extra w) (writeCoefficientRows extra w))
def streamCost (q count sourceLimit : Nat) := parameterCost q+1+
  (9*(X3C.target q).bits.length+8+1+
    (count*(rowCost sourceLimit (3*q) (X3C.base q).bits.length (X3C.high q).bits.length
      ((3*q+1)*(X3C.base q).size)+2)+1))
def coefficientValues (q : Nat) (rows : List (List Nat)) : List Nat :=
  X3C.target q::rows.map (fun row=>X3C.high q+powers (X3C.base q) row)
def coefficientStreamResult (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (q : Nat) (rows : List (List Nat)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 27) (List.replicate q true)) (w 52) (X3C.base q).bits) (w 54) (X3C.high q).bits)
    (w 0) suffix) (w 43) []) (w 36)
    ((Encoding.sequence Encoding.natural (coefficientValues q rows)).reverse++store (w 36))

theorem coefficientStream_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (q sourceLimit : Nat) (rows : List (List Nat))
    (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rows++suffix)
    (counter : store (w 43)=List.replicate rows.length true)
    (status : store (w 1)=accepted::tail) (universeCounter : store (w 17)=List.replicate (3*q) true)
    (sourceBound : (store (w 0)).length ≤ sourceLimit)
    (three : ∀ row∈rows,row.length=3) (fits : ∀ row∈rows,∀ index∈row,index ≤ 3*q)
    (sumSize : ∀ row∈rows,(X3C.high q+powers (X3C.base q) row).bits.length ≤ (3*q+1)*(X3C.base q).size)
    (empty : ∀ i∈streamScratch,store (w i)=[]) :
    ∃ time ≤ streamCost q rows.length sourceLimit,
      Executes (coefficientStream extra w) store time (coefficientStreamResult w store q rows suffix) := by
  obtain ⟨parameterTime,parameterBound,parametersRun⟩:=prepareParameters_executes extra w store q universeCounter
    (fun i member=>empty i (List.mem_append_left _ member))
  let prepared:=parameterResult w store q
  have emitting:=emitCoefficient_executes extra w prepared (X3C.target q)
    (by simp [prepared,parameterResult])
    (by simp [prepared,parameterResult,w.injective.eq_iff,empty,streamScratch,rowScratch])
    (by simp [prepared,parameterResult,w.injective.eq_iff,empty,streamScratch,rowScratch,tripleScratch,atomScratch])
  let based:=Function.update (Function.update (Function.update store (w 27) (List.replicate q true))
    (w 52) (X3C.base q).bits) (w 54) (X3C.high q).bits
  let emitted:=Function.update based (w 36) ((Encoding.natural.encode (X3C.target q)).reverse++store (w 36))
  have emitFinal : Function.update (Function.update prepared (w 55) []) (w 36)
      ((Encoding.natural.encode (X3C.target q)).reverse++prepared (w 36))=emitted := by
    funext r
    by_cases e55 : r=w 55
    · subst r;simp [emitted,based,w.injective.eq_iff,empty,streamScratch,rowScratch,tripleScratch]
    · simp [prepared,parameterResult,emitted,based,Function.update_apply,e55,w.injective.eq_iff]
  rw [emitFinal] at emitting
  have rowEmpty (i : Fin 64) (member : i∈rowScratch) : emitted (w i)=[] := by
    have n27 : i≠27 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
    have n36 : i≠36 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
    have n52 : i≠52 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
    have n54 : i≠54 := by intro same;subst i;simp [rowScratch,tripleScratch,atomScratch] at member
    simpa [emitted,based,w.injective.eq_iff,n27,n36,n52,n54] using
      empty i (List.mem_append_right _ member)
  obtain ⟨rowsTime,rowsBound,rowsRun⟩:=writeCoefficientRows_executes extra w rows
    (X3C.base q) (X3C.high q) (3*q) sourceLimit ((3*q+1)*(X3C.base q).size) emitted accepted suffix tail
    (by simp [emitted,based,w.injective.eq_iff,source])
    (by simp [emitted,based,w.injective.eq_iff,counter])
    (by simp [emitted,based,w.injective.eq_iff,status])
    (by simp [emitted,based,w.injective.eq_iff,universeCounter])
    (by simp [emitted,based,w.injective.eq_iff]) (by simp [emitted,based,w.injective.eq_iff])
    (by simpa [emitted,based,w.injective.eq_iff] using sourceBound) three fits sumSize rowEmpty
  have final : coefficientRowsResult w emitted (X3C.base q) (X3C.high q) rows suffix=
      coefficientStreamResult w store q rows suffix := by
    funext r
    by_cases e36 : r=w 36
    · subst r;simp [coefficientRowsResult,coefficientStreamResult,coefficientValues,emitted,
        Encoding.sequence,List.reverse_append,List.append_assoc]
    · simp [coefficientRowsResult,coefficientStreamResult,emitted,based,Function.update_apply,e36]
  rw [final] at rowsRun
  refine ⟨parameterTime+1+(9*(X3C.target q).bits.length+8+1+rowsTime),?_,
    parametersRun.sequence (emitting.sequence rowsRun)⟩
  unfold streamCost
  omega

end Counting.External.CoefficientMachine
