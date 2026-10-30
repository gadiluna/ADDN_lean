import Counting.StackAnchorRowSelect
import Counting.StackAnchorLeaderCoefficient

namespace Counting.StackMachine.AnchorLeaderRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev file := AnchorRow.file
abbrev select := AnchorRow.select
abbrev calculate : Routine 38 := relocate AnchorLeader.calculate AnchorRow.coefficientRoles
abbrev item : Routine 38 := sequence calculate (sequence select (clear 23))
abbrev word (node : Executable.Node) (_query : Nat) :=
  Encoding.rational.encode (AnchorLeader.value node)

theorem word_length (node : Executable.Node) (query : Nat) : (word node query).length ≤ 7 := by
  unfold word AnchorLeader.value
  split <;> decide

theorem calculate_executes (node : Executable.Node) (query : Nat)
    (suffix anchor reversed width counter : List Bool) :
    ∃ time ≤ 10000*((Encoding.node.encode node++suffix).length+query.size+1)^3,
      Executes calculate
        (file (Encoding.node.encode node++suffix) query.bits anchor [] [] reversed width counter []) time
        (file suffix query.bits anchor (word node query) node.level.bits reversed width counter []) := by
  obtain ⟨time,bounded,ran⟩ := AnchorLeader.calculate_executes node query suffix
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AnchorLeader.calculate AnchorRow.coefficientRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,AnchorRow.file,AnchorCoefficient.file,AnchorRow.coefficientRoles]
  · intro r;fin_cases r <;> simp [file,AnchorRow.file,AnchorCoefficient.file,AnchorRow.coefficientRoles]
  · intro r outside
    have n0 : r≠0 := by intro h;subst r;exact outside 0 rfl
    have n22 : r≠22 := by intro h;subst r;exact outside 22 rfl
    have n23 : r≠23 := by intro h;subst r;exact outside 23 rfl
    fin_cases r <;> simp_all [file,AnchorRow.file]

def nextReversed (node : Executable.Node) (query anchor : Nat) (reversed : List Bool) : List Bool :=
  if node.level=anchor then (Encoding.frame (word node query)).reverse++reversed else reversed

def nextWidth (node : Executable.Node) (anchor : Nat) (width : List Bool) : List Bool :=
  if node.level=anchor then true::width else width

theorem select_file (node : Executable.Node) (query anchor : Nat)
    (input reversed width counter : List Bool) :
    ∃ time ≤ 6*(node.level.size+anchor.size)+9*(word node query).length+30,
      Executes select (file input query.bits anchor.bits (word node query) node.level.bits reversed width counter [])
        time (file input query.bits anchor.bits [] node.level.bits
          (nextReversed node query anchor reversed) (nextWidth node anchor width) counter []) := by
  let store := file input query.bits anchor.bits (word node query) node.level.bits reversed width counter []
  obtain ⟨time,bounded,ran⟩ := AnchorRow.select_executes store rfl rfl rfl rfl rfl rfl
  change time ≤ 6*(node.level.bits.length+anchor.bits.length)+9*(word node query).length+30 at bounded
  simp only [Encoding.bits_length] at bounded
  refine ⟨time,bounded,?_⟩
  have result : (if store 23=store 34 then
      Function.update (Function.update (Function.update store 22 []) 35
        ((Encoding.frame (store 22)).reverse++store 35)) 36 (true::store 36)
      else Function.update store 22 [])=
      file input query.bits anchor.bits [] node.level.bits
        (nextReversed node query anchor reversed) (nextWidth node anchor width) counter [] := by
    change (if node.level.bits=anchor.bits then _ else _)=_
    simp only [Encoding.bits_injective.eq_iff]
    by_cases eq : node.level=anchor <;>
      simp only [eq,if_pos,if_neg,not_false_eq_true] <;>
      funext r <;> fin_cases r <;> simp [store,file,AnchorRow.file,nextReversed,nextWidth,eq]
  rw [result] at ran
  exact ran

theorem item_executes (node : Executable.Node) (query anchor : Nat)
    (suffix reversed width counter : List Bool) :
    ∃ time ≤ 200000*((Encoding.node.encode node++suffix).length+query.size+anchor.size+1)^3,
      Executes item (file (Encoding.node.encode node++suffix) query.bits anchor.bits [] [] reversed width counter [])
        time (file suffix query.bits anchor.bits [] []
          (nextReversed node query anchor reversed) (nextWidth node anchor width) counter []) := by
  obtain ⟨firstTime,firstBound,firstRun⟩ := calculate_executes node query suffix anchor.bits reversed width counter
  obtain ⟨secondTime,secondBound,secondRun⟩ := select_file node query anchor suffix reversed width counter
  have cleanup := clear_executes (23:Fin 40)
    (file suffix query.bits anchor.bits [] node.level.bits
      (nextReversed node query anchor reversed) (nextWidth node anchor width) counter [])
  have cleanupStore : Function.update
      (file suffix query.bits anchor.bits [] node.level.bits
        (nextReversed node query anchor reversed) (nextWidth node anchor width) counter []) 23 []=
      file suffix query.bits anchor.bits [] []
        (nextReversed node query anchor reversed) (nextWidth node anchor width) counter [] := by
    funext r;fin_cases r <;> simp [file,AnchorRow.file]
  rw [cleanupStore] at cleanup
  change Executes _ _ (node.level.bits.length+1) _ at cleanup
  simp only [Encoding.bits_length] at cleanup
  have composed := firstRun.sequence (secondRun.sequence cleanup)
  refine ⟨firstTime+1+(secondTime+1+(node.level.size+1)),?_,?_⟩
  · have label : node.level.size ≤ (Encoding.node.encode node).length := by
      rw [Encoding.node_length];unfold Encoding.nodeBits;omega
    have length := word_length node query
    let size := (Encoding.node.encode node++suffix).length+query.size+anchor.size+1
    have first : firstTime ≤ 10000*size^3 := firstBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [size];omega) 3))
    have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
    change _ ≤ 200000*size^3
    dsimp only [size] at first linear positive ⊢
    simp only [List.length_append] at *
    omega
  · exact composed

end Counting.StackMachine.AnchorLeaderRow
