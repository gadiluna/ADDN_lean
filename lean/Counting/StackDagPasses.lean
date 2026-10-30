import Counting.StackDagPass

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem scanStore_work (input flags : List Bool) (r : Fin 35) (small : r.val<17) (ne : r≠1) :
    scanStore input flags r=[]:=by
  have n17 : r≠17:=by intro equal;subst r;norm_num at small
  simp [scanStore,n17,ne]

theorem nodesPass_executes (vista : Executable.Vista) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 223000000*((Encoding.vista.encode vista).length+1)^6,
      Executes (validationPass nodesPrefixRoutine) (validatorStore (Encoding.vista.encode vista) (accepted::tail)) time
        (validatorStore (Encoding.vista.encode vista)
          ((accepted && nodeRangeCheck vista.nodes.toList 0 vista.nodes.size)::tail)):=by
  let start:=scanStore (Encoding.vista.encode vista) (accepted::tail)
  have work:=scanStore_work (Encoding.vista.encode vista) (accepted::tail)
  have extra (r : Fin 35) (member : r∈({18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34}:Finset (Fin 35))) : start r=[]:=by
    fin_cases r <;> simp_all [start,scanStore]
  obtain ⟨time,bound,ran⟩:=nodesPrefix_executes start accepted tail (by simp [start,scanStore]) work extra
    vista.nodes.toList (Encoding.natural.encode vista.bottom) (by simp [start,scanStore])
  have final : nodesPrefixStore start accepted tail vista.nodes.toList (Encoding.natural.encode vista.bottom)=
      scanStore (tableSuffix vista) ((accepted && nodeRangeCheck vista.nodes.toList 0 vista.nodes.size)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r17 : r=17 <;>
      simp [nodesPrefixStore,scanStore,start,tableSuffix,r1,r17]
  rw [final] at ran
  have passed:=validationPass_executes nodesPrefixRoutine _ _ _ _ time ran
  have suffix:=tableSuffix_length vista
  change time≤222000000*((Encoding.vista.encode vista).length+1)^6 at bound
  have linear:=Nat.le_self_pow (by decide : 6≠0) ((Encoding.vista.encode vista).length+1)
  exact ⟨_,by omega,passed⟩

theorem distinctPass_executes (vista : Executable.Vista) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 221000*((Encoding.vista.encode vista).length+1)^6,
      Executes (validationPass distinctPrefixRoutine) (validatorStore (Encoding.vista.encode vista) (accepted::tail)) time
        (validatorStore (Encoding.vista.encode vista)
          ((accepted && distinctAllRange vista.nodes.toList 0 vista.nodes.size)::tail)):=by
  let start:=scanStore (Encoding.vista.encode vista) (accepted::tail)
  have work:=scanStore_work (Encoding.vista.encode vista) (accepted::tail)
  have extra (r : Fin 35) (member : r∈({18,19,20,27,28,29}:Finset (Fin 35))) : start r=[]:=by
    fin_cases r <;> simp_all [start,scanStore]
  obtain ⟨time,bound,ran⟩:=distinctPrefix_executes start accepted tail (by simp [start,scanStore]) work extra
    vista.nodes.toList (Encoding.natural.encode vista.bottom) (by simp [start,scanStore])
  have final : distinctPrefixStore start accepted tail vista.nodes.toList (Encoding.natural.encode vista.bottom)=
      scanStore (tableSuffix vista) ((accepted && distinctAllRange vista.nodes.toList 0 vista.nodes.size)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r17 : r=17 <;>
      simp [distinctPrefixStore,scanStore,start,tableSuffix,r1,r17]
  rw [final] at ran
  have passed:=validationPass_executes distinctPrefixRoutine _ _ _ _ time ran
  have suffix:=tableSuffix_length vista
  change time≤220000*((Encoding.vista.encode vista).length+1)^6 at bound
  have linear:=Nat.le_self_pow (by decide : 6≠0) ((Encoding.vista.encode vista).length+1)
  exact ⟨_,by omega,passed⟩

theorem coverPass_executes (vista : Executable.Vista) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 104000*((Encoding.vista.encode vista).length+1)^5,
      Executes (validationPass coverPrefix) (validatorStore (Encoding.vista.encode vista) (accepted::tail)) time
        (validatorStore (Encoding.vista.encode vista) ((accepted && coverCheck vista.nodes.toList vista.bottom)::tail)):=by
  let start:=scanStore (Encoding.vista.encode vista) (accepted::tail)
  have work:=scanStore_work (Encoding.vista.encode vista) (accepted::tail)
  have extra (r : Fin 35) (member : r∈({21,22,23,24,25,26,27,28,30,31,34}:Finset (Fin 35))) : start r=[]:=by
    fin_cases r <;> simp_all [start,scanStore]
  obtain ⟨time,bound,ran⟩:=coverPrefix_executes start accepted tail (by simp [start,scanStore]) work extra
    vista.nodes.toList vista.bottom (by simp [start,scanStore])
  have final : coverPrefixStore start accepted tail vista.nodes.toList vista.bottom=
      scanStore (tableSuffix vista) ((accepted && coverCheck vista.nodes.toList vista.bottom)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r17 : r=17 <;>
      simp [coverPrefixStore,scanStore,start,tableSuffix,r1,r17]
  rw [final] at ran
  have passed:=validationPass_executes coverPrefix _ _ _ _ time ran
  have suffix:=tableSuffix_length vista
  change time≤103000*((Encoding.vista.encode vista).length+1)^5 at bound
  have linear:=Nat.le_self_pow (by decide : 5≠0) ((Encoding.vista.encode vista).length+1)
  exact ⟨_,by omega,passed⟩

def semanticRoutine : Routine 35:=sequence (validationPass nodesPrefixRoutine)
  (sequence (validationPass distinctPrefixRoutine) (validationPass coverPrefix))

theorem semanticRoutine_executes (vista : Executable.Vista) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 224000000*((Encoding.vista.encode vista).length+1)^6,
      Executes semanticRoutine (validatorStore (Encoding.vista.encode vista) (accepted::tail)) time
        (validatorStore (Encoding.vista.encode vista) ((accepted && vista.valid)::tail)):=by
  obtain ⟨nodeTime,nodeBound,nodeRun⟩:=nodesPass_executes vista accepted tail
  obtain ⟨distinctTime,distinctBound,distinctRun⟩:=distinctPass_executes vista
    (accepted && nodeRangeCheck vista.nodes.toList 0 vista.nodes.size) tail
  obtain ⟨coverTime,coverBound,coverRun⟩:=coverPass_executes vista
    ((accepted && nodeRangeCheck vista.nodes.toList 0 vista.nodes.size) &&
      distinctAllRange vista.nodes.toList 0 vista.nodes.size) tail
  have flags : (((accepted && nodeRangeCheck vista.nodes.toList 0 vista.nodes.size) &&
      distinctAllRange vista.nodes.toList 0 vista.nodes.size) && coverCheck vista.nodes.toList vista.bottom)=
      (accepted && vista.valid):=by
    rw [←semanticCheck_eq_valid]
    simp only [semanticCheck,Bool.and_assoc]
  rw [flags] at coverRun
  have fifth : ((Encoding.vista.encode vista).length+1)^5≤((Encoding.vista.encode vista).length+1)^6:=
    Nat.pow_le_pow_right (by omega) (by decide)
  have one : 1≤((Encoding.vista.encode vista).length+1)^6:=Nat.one_le_pow _ _ (by omega)
  exact ⟨nodeTime+1+(distinctTime+1+coverTime),by omega,nodeRun.sequence (distinctRun.sequence coverRun)⟩

end Counting.StackMachine.DagValidation
