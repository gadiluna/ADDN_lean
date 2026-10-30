import Counting.StackDagDistinctLoop

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def distinctPreviousRoutine : Routine 33:=sequence (ofProgram (ListPrograms.copyProgram 32 29 20 2))
  (sequence (forEach 20 distinctItemRoutine) (clear 18))

theorem distinctPrevious_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[])
    (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (budget : (store 29).length=index.val)
    (currentCode : store 28=Encoding.node.encode values[index]) :
    ∃ time ≤ 180000*((store 17).length+1)^5,
      Executes distinctPreviousRoutine store time
        (Function.update store 1 ((accepted && distinctRange values values[index] 0 index.val)::tail)) := by
  have copying:=copy_executes 32 29 20 2 (by decide) (by decide) (by decide) store (work 2 (by decide) (by decide))
  rw [budget,e20,List.append_nil] at copying
  let ready:=Function.update store 20 (store 29)
  have readyWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : ready r=[]:=by
    have n20 : r≠20:=by intro eq;subst r;norm_num at small
    simp [ready,n20,work r small ne]
  obtain ⟨loopTime,loopBound,loopRun⟩:=distinctLoop_executes ready accepted tail
    (by simp [ready,status]) readyWork (by simp [ready,e19]) values 0 index.val (by have:=index.isLt;omega)
    suffix (by simp [ready,source]) (by simp [ready,e18]) values[index]
    (by simp [ready,currentCode]) (store 29) (by simp [ready]) budget
  let checked:=distinctLoopStore ready accepted tail values values[index] 0 index.val
  have unary : checked 18=List.replicate index.val true:=by simp [checked,distinctLoopStore,ready,e18]
  have clearing:=clear_executes (18:Fin 35) checked
  rw [unary,List.length_replicate] at clearing
  have final : Function.update checked 18 []=
      Function.update store 1 ((accepted && distinctRange values values[index] 0 index.val)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r18 : r=18 <;> by_cases r20 : r=20 <;>
      simp [checked,distinctLoopStore,ready,r1,r18,r20,e18,e20]
  rw [final] at clearing
  have count:=node_sequence_count_le values
  have member:=node_sequence_member_le values values[index] (List.getElem_mem index.isLt)
  have indexBound : index.val≤(store 17).length:=by rw [source,List.length_append];have:=index.isLt;omega
  have selectedLength : (store 28).length≤(store 17).length:=by rw [currentCode,source,List.length_append];omega
  have readSource : ready 17=store 17:=by simp [ready]
  have readCurrent : ready 28=store 28:=by simp [ready]
  rw [readSource,readCurrent] at loopBound
  let S:=(store 17).length+1
  have spos : 1≤S:=by dsimp only [S];omega
  have base : (store 17).length+(store 28).length+1≤2*S:=by dsimp only [S];omega
  have indexS : index.val≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤160000*S^5+2*S+1:=by
    have leading : index.val*(10000*((store 17).length+(store 28).length+1)^4+2)+1≤
        S*(10000*(2*S)^4+2)+1:=by gcongr
    have expanded : S*(10000*(2*S)^4+2)+1=160000*S^5+2*S+1:=by ring
    omega
  have linear : S≤S^5:=Nat.le_self_pow (by decide) _
  have one : 1≤S^5:=Nat.one_le_pow _ _ spos
  exact ⟨5*index.val+2+1+(loopTime+1+(index.val+1)),by change _≤180000*S^5;omega,
    copying.sequence (loopRun.sequence clearing)⟩

end Counting.StackMachine.DagValidation
