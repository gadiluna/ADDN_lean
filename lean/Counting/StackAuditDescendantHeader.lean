import Counting.StackAuditDescendantAll
import Counting.StackEncodingListReadHeader
import Counting.EncodingVerifier
import Counting.EncodingNetwork

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def tableRoles : FullListWorkspace 23 :=
  ⟨![17,1,2,3,30,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

def readTable : Routine 38 := sequence (pushBit 1 true)
  (sequence (readListHeader 23 tableRoles) (clear 1))

def tableReady (store : Store 38) (nodes : Array Executable.Node) : Store 38 :=
  Function.update (Function.update store 17 (Encoding.sequence Encoding.node nodes.toList)) 30
    (List.replicate nodes.size true)

/-- The scan budget comes from the actual canonical array header. The
reader's internal unary expansion is bounded by its serialized input. -/
theorem readTable_executes (store : Store 38) (nodes : Array Executable.Node)
    (source : store 17=(Encoding.array Encoding.node).encode nodes)
    (e30 : store 30=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 2000*((store 17).length+1)^3,
      Executes readTable store time (tableReady store nodes) := by
  have a:=pushBit_executes (1:Fin 40) true store
  rw [empty 1 (by decide) (by decide)] at a
  let ready:=Function.update store 1 [true]
  obtain ⟨headerTime,headerBound,b⟩:=readListHeader_canonical 23 tableRoles ready true []
    (by simp [tableRoles,ready]) (by
      intro r member
      fin_cases r <;> simp_all [tableRoles,ready]) Encoding.node Encoding.node_positive_length
    nodes.toList [] (by simp [tableRoles,ready,source];rfl)
  let read:=Function.update (Function.update ready 17 (Encoding.sequence Encoding.node nodes.toList)) 30
    (List.replicate nodes.size true)
  have output : Function.update (Function.update ready (tableRoles 0)
      (Encoding.sequence Encoding.node nodes.toList++[])) (tableRoles 4) (List.replicate nodes.toList.length true)=read := by
    simp [tableRoles,read]
  rw [output] at b
  have c:=clear_executes (1:Fin 40) read
  have status : read 1=[true] := by simp [read,ready]
  rw [status,List.length_singleton] at c
  have final : Function.update read 1 []=tableReady store nodes := by
    funext r
    by_cases r1:r=1 <;> by_cases r17:r=17 <;> by_cases r30:r=30 <;>
      simp [read,ready,tableReady,r1,r17,r30,empty]
  rw [final] at c
  have sourceSame : (ready (tableRoles 0)).length=(store 17).length := by simp [ready,tableRoles]
  rw [sourceSame] at headerBound
  have one : 1 ≤ ((store 17).length+1)^3:=Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

def countTable : Routine 38 := sequence readTable countAll

/-- The complete descendant count reads its own node-count budget from
the encoded table, checks every actual node, and clears all scan scratch. -/
theorem countTable_executes (store : Store 38) (vista : Executable.Vista)
    (last ancestor : Nat) (steps : List Bool)
    (source : store 17=(Encoding.array Encoding.node).encode vista.nodes)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps)
    (e30 : store 30=[]) (e35 : store 35=[]) (e36 : store 36=[]) (e37 : store 37=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 17000000000*((store 17).length+steps.length+(ancestor+1).size+last.size+1)^6,
      Executes countTable store time
        (Function.update (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 39
          (List.replicate (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size) true++store 39)) := by
  obtain ⟨headerTime,headerBound,a⟩:=readTable_executes store vista.nodes source e30 empty
  let ready:=tableReady store vista.nodes
  obtain ⟨countTime,countBound,b⟩:=countAll_executes ready vista last ancestor steps
    (List.replicate vista.nodes.size true) (by simp)
    (by simp [ready,tableReady]) (by simp [ready,tableReady,lastAt]) (by simp [ready,tableReady,target])
    (by simp [ready,tableReady,stepBudget]) (by simp [ready,tableReady])
    (by simp [ready,tableReady,e35]) (by simp [ready,tableReady,e36]) (by simp [ready,tableReady,e37]) (by
      intro r small different
      have n30 : r≠30 := by intro same;subst r;norm_num at small
      simp [ready,tableReady,different,n30,empty r small different])
  have final : Function.update (Function.update ready 30 []) 39
      (List.replicate (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size) true++ready 39)=
      Function.update (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 39
        (List.replicate (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size) true++store 39) := by
    funext r
    by_cases r17:r=17 <;> by_cases r30:r=30 <;> by_cases r39:r=39 <;>
      simp [ready,tableReady,r17,r30,r39,e30]
  rw [final] at b
  refine ⟨_,?_,a.sequence b⟩
  have shorter : (ready 17).length ≤ (store 17).length := by
    rw [source]
    change (Encoding.sequence Encoding.node vista.nodes.toList).length ≤
      (Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [List.length_append]
    omega
  let K:=(store 17).length+steps.length+(ancestor+1).size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have countLimit : countTime ≤ 16000000000*K^6 := countBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 6))
  have headerLimit : headerTime ≤ 2000*K^6 := headerBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [K];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  change headerTime+1+countTime ≤ 17000000000*K^6
  omega

end Counting.StackMachine.AuditDescendant
