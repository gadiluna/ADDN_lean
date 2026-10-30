import Counting.EncodingNetwork
import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def initialCode (leader:Bool) : List Bool := Encoding.vista.encode (Executable.initialVista leader)
theorem initialCode_length (leader:Bool) : (initialCode leader).length=9 := by cases leader <;> decide

/-- The two possible initial local states are finite constants in the
program. Reading an initial bit selects and emits its exact DAG encoding. -/
def initialItem : Routine 1 := branchRoutine 0
  (prepend 1 (initialCode true).reverse) (prepend 1 (initialCode false).reverse)

def initialItemStore (store:Store 1) (leader:Bool) (suffix:List Bool) : Store 1 :=
  Function.update (Function.update store 0 suffix) 1 ((initialCode leader).reverse++store 1)

theorem initialItem_executes (store:Store 1) (leader:Bool) (suffix:List Bool)
    (source:store 0=leader::suffix) :
    Executes initialItem store 19 (initialItemStore store leader suffix) := by
  have emitting:=prepend_executes (1:Fin 3) (initialCode leader).reverse (Function.update store 0 suffix)
  simp only [List.length_reverse,initialCode_length,Function.update_of_ne (by decide : (1:Fin 3)≠0)] at emitting
  cases leader with
  | false => exact branch_executes_false (0:Fin 3) _ _ store _ suffix 18 source emitting
  | true => exact branch_executes_true (0:Fin 3) _ _ store _ suffix 18 source emitting

def initialValuesStore (store:Store 1) (leaders suffix:List Bool) : Store 1 :=
  Function.update (Function.update (Function.update store 0 suffix) 2 [])
    1 ((Encoding.sequence Encoding.vista (leaders.map Executable.initialVista)).reverse++store 1)

theorem initialValues_executes (leaders suffix:List Bool) (store:Store 1)
    (source:store 0=leaders++suffix) (counter:store 2=List.replicate leaders.length true) :
    Executes (forEach 2 initialItem) store (21*leaders.length+1) (initialValuesStore store leaders suffix) := by
  induction leaders generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩:=repeat_empty (2:Fin 3) initialItem store (by simpa using counter)
    have final:initialValuesStore store [] suffix=store:=by
      funext r
      fin_cases r <;> simp_all [initialValuesStore,Encoding.sequence]
    exact ⟨⟨1,store⟩,ran,halted,final.symm⟩
  | cons leader leaders ih =>
    let consumed:=Function.update store 2 (List.replicate leaders.length true)
    obtain ⟨body,bodyRun,bodyHalted,bodyStore⟩:=initialItem_executes consumed leader (leaders++suffix)
      (by simpa [consumed] using source)
    let middle:=initialItemStore consumed leader (leaders++suffix)
    obtain ⟨finish,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,initialItemStore]) (by simp [middle,initialItemStore,consumed])
    have firstRun:=repeat_iteration (2:Fin 3) initialItem store true (List.replicate leaders.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) 19 body bodyRun bodyHalted
    have final:initialValuesStore middle leaders suffix=initialValuesStore store (leader::leaders) suffix:=by
      funext r
      fin_cases r <;> simp [initialValuesStore,middle,initialItemStore,consumed,Encoding.sequence,initialCode,List.append_assoc]
    refine ⟨finish,?_,tailHalted,tailStore.trans final⟩
    rw [show 21*(leader::leaders).length+1=(19+2)+(21*leaders.length+1) by simp;omega,
      Machine.run_add,firstRun,Option.bind_some,bodyStore]
    exact tailRun

end Counting.StackMachine.NetworkVista
