import Counting.StackRealizabilityCountsPrefix
import Counting.StackRoutineRelocate
import Counting.EncodingNetwork

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def sumRoles : Fin 21 ↪ Fin 22 where
  toFun i:=⟨i.val,by have:=i.isLt;omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 22=>r.val) same

/-- Sum an explicitly serialized row using binary arithmetic. Zero arc
multiplicities are permitted; the auxiliary positivity flag of the reused
summation routine is cleared after all entries have been added. -/
def rowTotal : Routine 20 := sequence (ofProgram (ListPrograms.copyProgram 19 21 17 4))
  (sequence (pushBit 1 true)
    (sequence (relocate RealizabilityCheck.countsPrefix sumRoles)
      (sequence (clear 0) (clear 1))))

theorem rowTotal_executes (store:Store 20) (row:Array Nat)
    (source:store 21=(Encoding.array Encoding.natural).encode row)
    (work:∀r:Fin 22,r≠21 → store r=[]) :
    ∃time ≤ 2100*((store 21).length+1)^3,
      Executes rowTotal store time (Function.update store 19 row.toList.sum.bits) := by
  have copying:=copy_executes 19 (21:Fin 22) 17 4 (by decide) (by decide) (by decide) store (work 4 (by decide))
  rw [work 17 (by decide),List.append_nil] at copying
  let copied:=Function.update store 17 (store 21)
  have pushing:=pushBit_executes (1:Fin 22) true copied
  rw [show copied 1=[] by simp [copied,work]] at pushing
  let ready:=Function.update copied 1 [true]
  let localStore:=ready ∘ sumRoles
  have empty (i:Fin 21) (n1:i≠1) (n17:i≠17):localStore i=[]:=by
    have r1:sumRoles i≠1:=by intro same;apply n1;apply Fin.ext;exact congrArg (fun r:Fin 22=>r.val) same
    have r17:sumRoles i≠17:=by intro same;apply n17;apply Fin.ext;exact congrArg (fun r:Fin 22=>r.val) same
    have r21:sumRoles i≠21:=by
      intro same
      have value:=congrArg (fun r:Fin 22=>r.val) same
      change i.val=21 at value
      have:=i.isLt
      omega
    simp [localStore,ready,copied,r1,r17,work _ r21]
  obtain ⟨sumTime,sumBound,sumRun⟩:=RealizabilityCheck.countsPrefix_executes localStore true []
    (by simp [localStore,sumRoles,ready])
    (by intro i small n1;exact empty i n1 (by intro same;subst i;norm_num at small))
    (empty 18 (by decide) (by decide)) (empty 20 (by decide) (by decide))
    0 (by simpa using empty 19 (by decide) (by decide)) row.toList []
    (by simp [localStore,sumRoles,ready,copied,source,Encoding.array,Encoding.transport])
  let summed:=Function.update (Function.update (Function.update (Function.update ready 17 [])
    0 (List.replicate row.size true)) 19 row.toList.sum.bits)
      1 [RealizabilityCheck.positiveCounts row.toList]
  have summing:Executes (relocate RealizabilityCheck.countsPrefix sumRoles) ready sumTime summed:=by
    apply relocate_executes_frame RealizabilityCheck.countsPrefix sumRoles ready summed localStore
      (RealizabilityCheck.countsPrefixStore localStore true [] [] 0 row.toList) sumTime rfl
    · intro i
      fin_cases i <;> simp [summed,RealizabilityCheck.countsPrefixStore,localStore,sumRoles]
    · intro r outside
      have n0:r≠0:=by simpa [sumRoles] using (outside 0).symm
      have n1:r≠1:=by simpa [sumRoles] using (outside 1).symm
      have n17:r≠17:=by simpa [sumRoles] using (outside 17).symm
      have n19:r≠19:=by simpa [sumRoles] using (outside 19).symm
      simp [summed,n0,n1,n17,n19]
    · exact sumRun
  have clearCount:=clear_executes (0:Fin 22) summed
  rw [show summed 0=List.replicate row.size true by simp [summed],List.length_replicate] at clearCount
  have clearFlag:=clear_executes (1:Fin 22) (Function.update summed 0 [])
  rw [show Function.update summed 0 [] 1=[RealizabilityCheck.positiveCounts row.toList] by simp [summed]] at clearFlag
  have final:Function.update (Function.update summed 0 []) 1 []=Function.update store 19 row.toList.sum.bits:=by
    funext r
    fin_cases r <;> simp [summed,ready,copied,work]
  rw [final] at clearFlag
  have sizeBound:row.size≤(store 21).length:=by
    rw [source]
    exact Encoding.array_size_le_length _ _ (by intro value _;rw [Encoding.natural_length];omega)
  have sourceSame:localStore 17=store 21:=by simp [localStore,sumRoles,ready,copied]
  rw [sourceSame,Nat.size_zero,Nat.add_zero] at sumBound
  have linear:(store 21).length+1≤((store 21).length+1)^3:=Nat.le_self_pow (by decide) _
  refine ⟨_,?_,copying.sequence (pushing.sequence (summing.sequence (clearCount.sequence clearFlag)))⟩
  simp only [List.length_cons,List.length_nil] at *
  omega

end Counting.StackMachine.NetworkVista
