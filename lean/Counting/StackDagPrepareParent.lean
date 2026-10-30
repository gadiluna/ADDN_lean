import Counting.StackDagParentIndex
import Counting.StackEncodingFrameStore
import Counting.StackEncodingPair

/-! Prepare the parent-reader index from its binary optional-parent field.
The source field is preserved and the unary budget is consumed. This is
actual stack code, including copying, framing, bounded conversion and cleanup. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def prepareCountRoles : CountWorkspace 17:=⟨![20,18,0,2,3,4,1,5,6,7,25],by decide⟩

def prepareParent : Routine 26:=
  sequence (ofProgram (ListPrograms.copyProgram 25 22 26 4))
    (sequence (frameRoutine 25 26 20 4)
      (sequence (parentIndexRoutine 17 prepareCountRoles)
        (sequence (ofProgram (combineFlagsProgram 26 1)) (clear 20))))

def prepareParentStore (store : Store 26) (accepted : Bool) (tail : List Bool) (code : Nat) : Store 26:=
  Function.update (Function.update (Function.update store 18
    (List.replicate (min code (store 25).length-1) true)) 25 []) 1
    ((accepted && decide (code≤(store 25).length))::tail)

theorem prepareParent_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail) (code : Nat) (payload : store 22=code.bits)
    (work : ∀ r : Fin 28,r∈({0,2,3,4,5,6,7,18,20,26}:Finset (Fin 28)) → store r=[]) :
    ∃ time ≤ 100*((store 25).length+2*code.size+2)^3,
      Executes prepareParent store time (prepareParentStore store accepted tail code) := by
  have copied:=copy_executes 25 22 26 4 (by decide) (by decide) (by decide) store (work 4 (by decide))
  rw [work 26 (by decide),List.append_nil,payload] at copied
  let copiedStore:=Function.update store 26 code.bits
  have framed:=frame_executes_updates 25 26 20 4 (by decide) (by decide) (by decide)
    copiedStore (by simp [copiedStore,work 4 (by decide)])
  have copyVal : copiedStore 26=code.bits:=by simp [copiedStore]
  have frameEmpty : copiedStore 20=[]:=by simp [copiedStore,work 20 (by decide)]
  rw [copyVal,frameEmpty,List.append_nil] at framed
  have restored : Function.update copiedStore 26 []=store:=by
    simp only [copiedStore,Function.update_idem,←work 26 (by decide),Function.update_eq_self]
  rw [restored] at framed
  let framedStore:=Function.update store 20 (Encoding.frame code.bits)
  have indexEmpty : framedStore (prepareCountRoles 1)=[]:=by
    simp [framedStore,prepareCountRoles,work 18 (by decide)]
  have indexWork (r : Fin 11) (inside : r∈({2,3,4,5,7,8,9}:Finset (Fin 11))) :
      framedStore (prepareCountRoles r)=[] := by
    fin_cases r <;> simp only [Finset.mem_insert,Finset.mem_singleton] at inside
    all_goals first | contradiction | simp [framedStore,prepareCountRoles,work]
  obtain ⟨indexTime,indexBound,indexRun⟩:=parentIndex_executes 17 prepareCountRoles framedStore code
    (by simp [framedStore,prepareCountRoles,Encoding.natural]) indexEmpty indexWork
  let indexed:=parentIndexStore 17 prepareCountRoles framedStore code
  have indexedFlag : indexed 1=decide (code≤(store 25).length)::accepted::tail:=by
    simp [indexed,parentIndexStore,boundedNaturalResult,framedStore,prepareCountRoles,status]
  have combined:=combineFlags_executes 26 1 indexed accepted (decide (code≤(store 25).length)) tail indexedFlag
  let combinedStore:=Function.update indexed 1 ((accepted && decide (code≤(store 25).length))::tail)
  have frameValue : combinedStore 20=Encoding.frame code.bits:=by
    simp [combinedStore,indexed,parentIndexStore,boundedNaturalResult,framedStore,prepareCountRoles]
  have clearing:=clear_executes 20 combinedStore
  rw [frameValue] at clearing
  have cleaned : Function.update combinedStore 20 []=prepareParentStore store accepted tail code := by
    funext r
    fin_cases r <;> simp [prepareParentStore,combinedStore,indexed,parentIndexStore,boundedNaturalResult,
      framedStore,prepareCountRoles,work 20 (by decide)]
  rw [cleaned] at clearing
  have composed:=copied.sequence (framed.sequence (indexRun.sequence (combined.sequence clearing)))
  have budget : framedStore (prepareCountRoles 10)=store 25:=by simp [framedStore,prepareCountRoles]
  rw [budget,Encoding.natural_length] at indexBound
  have norm : (store 25).length+(2*code.size+1)+1=(store 25).length+2*code.size+2:=by omega
  rw [norm] at indexBound
  refine ⟨_,?_,composed⟩
  rw [Encoding.bits_length,Encoding.frame_length,Encoding.bits_length]
  have growth:=Nat.le_self_pow (by decide : 3≠0) ((store 25).length+2*code.size+2)
  omega

end Counting.StackMachine.DagValidation
