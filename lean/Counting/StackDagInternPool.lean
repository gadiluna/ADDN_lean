import Counting.StackDagInternSearch
import Counting.StackEncodingListAppendBounds
import Counting.EncodingNetwork

namespace Counting.StackMachine.DagUpdate.Intern
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def appendRoles : Fin 10 ↪ Fin 64 := ⟨![0,1,22,2,4,5,6,7,8,9],by decide⟩

def selectPool : Routine 62 := branchRoutine 23
  (ofProgram (ListPrograms.copyProgram 61 0 2 4))
  (mapRegisters appendRoles appendCanonical)

theorem firstIndex_getD_le_length (query : Executable.Node) (nodes : List Executable.Node) :
    (Executable.firstIndex query nodes).getD nodes.length ≤ nodes.length := by
  cases found : Executable.firstIndex query nodes with
  | none => simp
  | some index =>
    have inside := (Executable.firstIndex_some_iff query nodes index).mp found
    simpa using Nat.le_of_lt inside.choose

theorem selectPool_executes (store : Store 62) (nodes : List Executable.Node) (query : Executable.Node)
    (source : store 0=(Encoding.list Encoding.node).encode nodes)
    (queryAt : store 1=Encoding.node.encode query)
    (foundAt : store 23=[(Executable.firstIndex query nodes).isSome])
    (indexAt : store 22=List.replicate ((Executable.firstIndex query nodes).getD nodes.length) true)
    (outputEmpty : store 2=[]) (empty : ∀ r : Fin 64,4 ≤ r.val → r.val ≤ 9 → store r=[]) :
    ∃ time ≤ 1000*((store 0).length+(store 1).length+1)^2,
      Executes selectPool store time
        (Function.update (Function.update store 23 []) 2
          ((Encoding.array Encoding.node).encode (Executable.intern nodes.toArray query).1)) := by
  let ready := Function.update store 23 []
  let K := (store 0).length+(store 1).length+1
  have positive : 1 ≤ K := by omega
  have square : K ≤ K^2 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^2 := one_le_pow₀ positive
  cases found : Executable.firstIndex query nodes with
  | some index =>
    have copying := copy_executes 61 (0:Fin 64) 2 4 (by decide) (by decide) (by decide)
      ready (by simp [ready,empty])
    have value : ready 0=store 0 := by simp [ready]
    have vacant : ready 2=[] := by simp [ready,outputEmpty]
    rw [value,vacant,List.append_nil] at copying
    have ran := branch_executes_true (23:Fin 64) (ofProgram (ListPrograms.copyProgram 61 0 2 4))
      (mapRegisters appendRoles appendCanonical) store (Function.update ready 2 (store 0)) []
      (5*(store 0).length+2) (by simpa [found] using foundAt) copying
    refine ⟨1+(5*(store 0).length+2),?_,?_⟩
    · change _ ≤ 1000*K^2
      have sourceBound : (store 0).length ≤ K := by omega
      omega
    · simpa only [selectPool,Executable.intern_toArray,found,Encoding.array,Encoding.transport,
        List.toList_toArray,source,ready] using ran
  | none =>
    let localStore : Store 8 := ready ∘ appendRoles
    obtain ⟨time,bound,appending⟩ := appendCanonical_executes_polynomial Encoding.node nodes query localStore
      (by simpa [localStore,ready,appendRoles] using source)
      (by simpa [localStore,ready,appendRoles] using queryAt)
      (by simpa [localStore,ready,appendRoles,found] using indexAt) (by
        intro r lower
        fin_cases r <;> simp_all [localStore,ready,appendRoles])
    let result := Function.update ready 2 ((Encoding.list Encoding.node).encode (nodes++[query]))
    have relocated : Executes (mapRegisters appendRoles appendCanonical) ready time result := by
      apply relocate_executes_frame appendCanonical appendRoles ready result localStore
        (Function.update localStore 3 ((Encoding.list Encoding.node).encode (nodes++[query]))) time rfl _ _ appending
      · intro r
        fin_cases r <;> simp [result,localStore,appendRoles]
      · intro r outside
        have different : r≠2 := fun eq=>outside 3 (by simpa [appendRoles] using eq.symm)
        simp [result,different]
    have ran := branch_executes_false (23:Fin 64) (ofProgram (ListPrograms.copyProgram 61 0 2 4))
      (mapRegisters appendRoles appendCanonical) store result [] time
      (by simpa [found] using foundAt) relocated
    refine ⟨1+time,?_,?_⟩
    · have countLength : (localStore 2).length=nodes.length := by
        simp [localStore,ready,appendRoles,indexAt,found]
      have sourceValue : localStore 0=store 0 := by simp [localStore,ready,appendRoles]
      have queryValue : localStore 1=store 1 := by simp [localStore,ready,appendRoles]
      rw [countLength,sourceValue,queryValue] at bound
      have countBound : nodes.length ≤ (store 0).length := by
        have count := DagValidation.node_sequence_count_le nodes
        rw [source]
        simp only [Encoding.list,List.length_append]
        omega
      have base : nodes.length+(store 0).length+(store 1).length+1 ≤ 2*K := by omega
      have powered := Nat.pow_le_pow_left base 2
      change _ ≤ 1000*K^2
      nlinarith only [bound,powered,one]
    · simpa only [selectPool,Executable.intern_toArray,found,Encoding.array,Encoding.transport,
        List.toList_toArray,result,ready] using ran

end Counting.StackMachine.DagUpdate.Intern
