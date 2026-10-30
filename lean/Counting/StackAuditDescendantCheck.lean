import Counting.StackAuditDescendantHeader
import Counting.StackAuditDescendantCompare
import Counting.StackAuditDescendantWeight

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def checkAncestor : Routine 38 := sequence readTable
  (sequence readWeight (sequence countCompare (clear 31)))

/-- Read the real node-count header and selected binary weight, count its
matching descendants, and return exactly the paper's inequality test.
Missing weights use zero, without an array-shape assumption. -/
theorem checkAncestor_executes (store : Store 38) (vista : Executable.Vista)
    (weights : Array Nat) (last ancestor : Nat) (steps : List Bool)
    (source : store 17=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (query : store 33=Encoding.natural.encode ancestor)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps)
    (e30 : store 30=[]) (e31 : store 31=[]) (e35 : store 35=[])
    (e36 : store 36=[]) (e37 : store 37=[]) (e39 : store 39=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 18000000000*((store 17).length+(store 32).length+(store 33).length+
        steps.length+(ancestor+1).size+last.size+1)^6,
      Executes checkAncestor store time
        (Function.update (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 35
          [decide (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size ≤
            weights[ancestor]?.getD 0)]) := by
  obtain ⟨headerTime,headerBound,a⟩:=readTable_executes store vista.nodes source e30 empty
  let ready:=tableReady store vista.nodes
  obtain ⟨weightTime,weightBound,b⟩:=readWeight_executes ready weights ancestor
    (by simp [ready,tableReady,weightsAt]) (by simp [ready,tableReady,query]) (by simp [ready,tableReady,e31]) (by
      intro r small
      have n17 : r≠17 := by intro same;subst r;norm_num at small
      have n30 : r≠30 := by intro same;subst r;norm_num at small
      simp [ready,tableReady,n17,n30,empty r (by omega) n17])
  let weight:=weights[ancestor]?.getD 0
  let weighted:=Function.update ready 31 weight.bits
  obtain ⟨countTime,countBound,c⟩:=countCompare_executes weighted vista last ancestor weight steps
    (List.replicate vista.nodes.size true) (by simp)
    (by simp [weighted,ready,tableReady]) (by simp [weighted,ready,tableReady,lastAt])
    (by simp [weighted,ready,tableReady,target]) (by simp [weighted])
    (by simp [weighted,ready,tableReady,stepBudget]) (by simp [weighted,ready,tableReady])
    (by simp [weighted,ready,tableReady,e35]) (by simp [weighted,ready,tableReady,e36])
    (by simp [weighted,ready,tableReady,e37]) (by simp [weighted,ready,tableReady,e39]) (by
      intro r small n17
      have n30 : r≠30 := by intro same;subst r;norm_num at small
      have n31 : r≠31 := by intro same;subst r;norm_num at small
      simp [weighted,ready,tableReady,n17,n30,n31,empty r small n17])
  let answer:=decide (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size ≤ weight)
  let checked:=Function.update (Function.update weighted 30 []) 35 [answer]
  have d:=clear_executes (31:Fin 40) checked
  have weightWord : checked 31=weight.bits := by simp [checked,weighted]
  rw [weightWord,Encoding.bits_length] at d
  have final : Function.update checked 31 []=
      Function.update (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 35 [answer] := by
    funext r
    by_cases r17:r=17 <;> by_cases r30:r=30 <;> by_cases r31:r=31 <;> by_cases r35:r=35 <;>
      simp [checked,weighted,ready,tableReady,r17,r30,r31,r35,e30,e31]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  have shorter : (weighted 17).length ≤ (store 17).length := by
    rw [source]
    change (Encoding.sequence Encoding.node vista.nodes.toList).length ≤
      (Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList).length
    simp only [List.length_append]
    omega
  have weightSize : weight.size ≤ (store 32).length := by
    rw [weightsAt]
    exact weight_size_le_encoded weights ancestor
  have sameWeights : (ready 32).length=(store 32).length := by simp [ready,tableReady]
  have sameQuery : (ready 33).length=(store 33).length := by simp [ready,tableReady]
  rw [sameWeights,sameQuery] at weightBound
  let K:=(store 17).length+(store 32).length+(store 33).length+steps.length+(ancestor+1).size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have countLimit : countTime ≤ 17000000000*K^6 := countBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 6))
  have headerLimit : headerTime ≤ 2000*K^6 := headerBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [K];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have weightLimit : weightTime ≤ 200*K^6 := weightBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [K];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  have width : weight.size ≤ K := by dsimp only [K];omega
  change headerTime+1+(weightTime+1+(countTime+1+(weight.size+1))) ≤ 18000000000*K^6
  omega

theorem checkAncestor_auditDescendantAt (store : Store 38) (vista : Executable.Vista)
    (weights : Array Nat) (anchor last ancestor : Nat) (steps : List Bool)
    (stepCount : steps.length=last-anchor)
    (source : store 17=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (query : store 33=Encoding.natural.encode ancestor)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps)
    (e30 : store 30=[]) (e31 : store 31=[]) (e35 : store 35=[])
    (e36 : store 36=[]) (e37 : store 37=[]) (e39 : store 39=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 18000000000*((store 17).length+(store 32).length+(store 33).length+
        steps.length+(ancestor+1).size+last.size+1)^6,
      Executes checkAncestor store time
        (Function.update (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 35
          [Executable.auditDescendantAt vista weights anchor last ancestor]) := by
  obtain ⟨time,bound,run⟩:=checkAncestor_executes store vista weights last ancestor steps source weightsAt query
    lastAt target stepBudget e30 e31 e35 e36 e37 e39 empty
  exact ⟨time,bound,by simpa only [Executable.auditDescendantAt,stepCount] using run⟩

end Counting.StackMachine.AuditDescendant
