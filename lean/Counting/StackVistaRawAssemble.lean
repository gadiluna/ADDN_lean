import Counting.StackDagNodeAssemble
import Counting.StackDagIncrement
import Counting.StackDagMapInternBank

namespace Counting.StackMachine.DagUpdate.Raw
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def assembleRoles : Fin 64 ↪ Fin 96 := ⟨![0,3,75,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,80,41,82,83,44,81,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],by decide⟩

def assembleNode : Routine 94 := mapRegisters assembleRoles NodeMap.assemble

def assembledStore (store : Store 94) (node : Executable.Node) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update store 75 []) 80 []) 81 []) 82 []) 83 []) 1 (Encoding.node.encode node)

theorem assembleNode_executes (store : Store 94) (node : Executable.Node)
    (levelAt : store 80=node.level.bits) (parentAt : store 81=(NodeMap.parentNumber node).bits)
    (leaderAt : store 82=[node.leader]) (degreeAt : store 83=node.degree.bits)
    (incomingAt : store 75=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming)
    (empty : ∀ r:Fin 96,r=1 ∨ r=41 ∨ r=46 ∨ r=47 ∨ r=48 → store r=[]) :
    Executes assembleNode store
      (9*(node.level.bits.length+(NodeMap.parentNumber node).bits.length+node.degree.bits.length)+
        2*((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).length+
        2*(Encoding.node.encode node).length+35)
      (assembledStore store node) := by
  let localStore : Store 62 := store ∘ assembleRoles
  have run := NodeMap.assemble_executes localStore node levelAt parentAt leaderAt degreeAt incomingAt
    (empty 1 (by simp)) (empty 46 (by simp)) (empty 47 (by simp)) (empty 48 (by simp))
  have e41 : localStore 41=[] := empty 41 (by simp)
  rw [e41,List.length_nil,Nat.add_zero] at run
  apply relocate_executes_frame NodeMap.assemble assembleRoles store (assembledStore store node)
    localStore (NodeMap.assembledResult localStore node) _ rfl _ _ run
  · intro r
    fin_cases r <;> simp [assembledStore,NodeMap.assembledResult,localStore,assembleRoles,empty]
  · intro r outside
    have n1 : r≠1 := fun eq=>outside 3 (by simpa [assembleRoles] using eq.symm)
    have n75 : r≠75 := fun eq=>outside 2 (by simpa [assembleRoles] using eq.symm)
    have n80 : r≠80 := fun eq=>outside 40 (by simpa [assembleRoles] using eq.symm)
    have n81 : r≠81 := fun eq=>outside 45 (by simpa [assembleRoles] using eq.symm)
    have n82 : r≠82 := fun eq=>outside 42 (by simpa [assembleRoles] using eq.symm)
    have n83 : r≠83 := fun eq=>outside 43 (by simpa [assembleRoles] using eq.symm)
    simp [assembledStore,n1,n75,n80,n81,n82,n83]

def incrementAndAssemble : Routine 94 := sequence (DagValidation.incrementRoutine 93 79 80 69)
  (sequence (DagValidation.incrementRoutine 93 79 81 69) assembleNode)

def newNode (round bottom : Nat) (leader : Bool) (degree : Nat) (edges : List (Nat×Nat)) : Executable.Node :=
  ⟨round+1,some bottom,leader,degree,edges⟩

def assembleBudget (round bottom : Nat) (leader : Bool) (degree : Nat) (edges : List (Nat×Nat)) : Nat :=
  let node := newNode round bottom leader degree edges
  4*round.size+4*bottom.size+
    9*(node.level.bits.length+(NodeMap.parentNumber node).bits.length+node.degree.bits.length)+
    2*((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges).length+
    2*(Encoding.node.encode node).length+51

theorem incrementAndAssemble_executes (store : Store 94) (round bottom : Nat)
    (leader : Bool) (degree : Nat) (edges : List (Nat×Nat))
    (roundAt : store 80=round.bits) (bottomAt : store 81=bottom.bits)
    (leaderAt : store 82=[leader]) (degreeAt : store 83=degree.bits)
    (edgesAt : store 75=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges)
    (empty : ∀ r:Fin 96,r=1 ∨ r=41 ∨ r=46 ∨ r=47 ∨ r=48 ∨ r=69 ∨ r=79 → store r=[]) :
    ∃ time ≤ assembleBudget round bottom leader degree edges,
      Executes incrementAndAssemble store time (assembledStore store (newNode round bottom leader degree edges)) := by
  obtain ⟨t0,b0,r0⟩ := DagValidation.increment_natural 93 (79:Fin 96) 80 69
    (by decide) (by decide) (by decide) store
    (empty 79 (by simp)) (empty 69 (by simp)) round roundAt
  let a := Function.update store 80 (round+1).bits
  obtain ⟨t1,b1,r1⟩ := DagValidation.increment_natural 93 (79:Fin 96) 81 69
    (by decide) (by decide) (by decide) a
    (by simp [a,empty]) (by simp [a,empty]) bottom (by simp [a,bottomAt])
  let b := Function.update a 81 (bottom+1).bits
  let node := newNode round bottom leader degree edges
  have assembled := assembleNode_executes b node
    (by simp [b,a,node,newNode]) (by simp [b,node,newNode,NodeMap.parentNumber])
    (by simp [b,a,node,newNode,leaderAt]) (by simp [b,a,node,newNode,degreeAt])
    (by simp [b,a,node,newNode,edgesAt]) (by
      intro r eligible
      rcases eligible with rfl|rfl|rfl|rfl|rfl <;> simp [b,a,empty])
  have result : assembledStore b node=assembledStore store node := by
    funext r
    fin_cases r <;> simp [assembledStore,b,a]
  rw [result] at assembled
  refine ⟨_,?_,r0.sequence (r1.sequence assembled)⟩
  dsimp only [assembleBudget,node,newNode] at *
  omega

end Counting.StackMachine.DagUpdate.Raw
