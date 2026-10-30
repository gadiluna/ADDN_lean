import Counting.StackAuditDescendantSelection
import Counting.StackRoutineLists

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false

def prepareSelection : Routine 38 :=
  sequence (ofProgram (ListPrograms.copyProgram 37 36 18 0))
    (sequence (ofProgram (ListPrograms.copyProgram 37 37 24 0))
      (ofProgram (ListPrograms.copyProgram 37 38 25 0)))

def selectionReady (store : Store 38) : Store 38 :=
  Function.update (Function.update (Function.update store 18 (store 36)) 24 (store 37)) 25 (store 38)

/-- Copy the actual persistent index, reference and step budget. Their
lengths, including the unary counters, are charged to the execution. -/
theorem prepareSelection_executes (store : Store 38)
    (e0 : store 0=[]) (e18 : store 18=[]) (e24 : store 24=[]) (e25 : store 25=[]) :
    Executes prepareSelection store (5*((store 36).length+(store 37).length+(store 38).length)+8)
      (selectionReady store) := by
  have a:=copy_executes 37 (36:Fin 40) 18 0 (by decide) (by decide) (by decide) store e0
  rw [e18,List.append_nil] at a
  let first:=Function.update store 18 (store 36)
  have b:=copy_executes 37 (37:Fin 40) 24 0 (by decide) (by decide) (by decide) first (by simp [first,e0])
  have bSource : first 37=store 37 := by simp [first]
  have bTarget : first 24=[] := by simp [first,e24]
  rw [bSource,bTarget,List.append_nil] at b
  let second:=Function.update first 24 (store 37)
  have c:=copy_executes 37 (38:Fin 40) 25 0 (by decide) (by decide) (by decide) second (by simp [second,first,e0])
  have cSource : second 38=store 38 := by simp [second,first]
  have cTarget : second 25=[] := by simp [second,first,e25]
  rw [cSource,cTarget,List.append_nil] at c
  convert a.sequence (b.sequence c) using 1 <;> first | rfl | omega

def selectCurrent : Routine 38 := sequence prepareSelection selected

/-- Selection within a table scan preserves its persistent counters and
all accumulated results, with a uniform bound in the compact table size. -/
theorem selectCurrent_executes (store : Store 38) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (last ancestor : Nat) (bits : List Bool)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (indexAt : (store 36).length=index.val) (current : store 37=(index.val+1).bits)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (counter : store 38=bits) (flag : store 35=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 14000000000*((store 17).length+bits.length+(ancestor+1).size+last.size+1)^5,
      Executes selectCurrent store time
        (Function.update store 35 [Executable.descendantSelected vista bits.length last ancestor index.val]) := by
  have a:=prepareSelection_executes store (empty 0 (by decide) (by decide))
    (empty 18 (by decide) (by decide)) (empty 24 (by decide) (by decide)) (empty 25 (by decide) (by decide))
  obtain ⟨bodyTime,bodyBound,b⟩:=selected_executes (selectionReady store) vista index last ancestor bits
    (by simp [selectionReady,source]) (by simpa [selectionReady] using indexAt)
    (by simp [selectionReady,lastAt]) (by simp [selectionReady,current])
    (by simp [selectionReady,target]) (by simp [selectionReady,counter]) (by
      intro r small n17 n18 n24 n25
      simp [selectionReady,n18,n24,n25,empty r small n17])
  have final : Function.update (Function.update (Function.update (Function.update (selectionReady store) 18 []) 25 []) 24 []) 35
      (Executable.descendantSelected vista bits.length last ancestor index.val::selectionReady store 35)=
      Function.update store 35 [Executable.descendantSelected vista bits.length last ancestor index.val] := by
    funext r
    by_cases a:r=18 <;> by_cases b:r=24 <;> by_cases c:r=25 <;> by_cases d:r=35 <;>
      simp [selectionReady,a,b,c,d,empty,flag]
  rw [final] at b
  refine ⟨_,?_,a.sequence b⟩
  have nodeCount:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList,←source] at nodeCount
  have width : (index.val+1).size ≤ (store 17).length :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans
      ((show index.val+1 ≤ vista.nodes.size by have:=index.isLt;omega).trans nodeCount)
  let K:=(store 17).length+bits.length+(ancestor+1).size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have one : 1 ≤ K^5:=Nat.one_le_pow _ _ positive
  have linear : K ≤ K^5:=Nat.le_self_pow (by decide) _
  have bodyLimit : bodyTime ≤ (400000000*2^5)*K^5 := by
    have base : (selectionReady store 17).length+(index.val+1).size+bits.length+
        (ancestor+1).size+last.size+1 ≤ 2*K := by simp only [selectionReady,Function.update_of_ne (by decide : (17:Fin 40)≠25),Function.update_of_ne (by decide : (17:Fin 40)≠24),Function.update_of_ne (by decide : (17:Fin 40)≠18)];dsimp only [K];omega
    calc
      _ ≤ 400000000*(2*K)^5:=bodyBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 5))
      _ = _ := by ring
  have prepLimit : (store 36).length+(store 37).length+(store 38).length ≤ 3*K := by
    rw [indexAt,current,counter,Encoding.bits_length]
    have:=index.isLt
    dsimp only [K];omega
  change 5*((store 36).length+(store 37).length+(store 38).length)+8+1+bodyTime ≤ 14000000000*K^5
  norm_num at bodyLimit
  omega

end Counting.StackMachine.AuditDescendant
