import Counting.StackDagMapInternBank
import Counting.StackComparePreserving

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def collectLevelRoles : Fin 6 ↪ Fin 96 := ⟨![66,82,67,68,69,70],by decide⟩

/-- Inspect the level of a remapped node while retaining the complete node
word for the selected indexed record. Equality is an executed bit scan. -/
def collectLevel : Routine 94 := sequence (ofProgram (ListPrograms.copyProgram 93 3 65 4))
  (sequence (ofProgram (unframeProgram 93 65 66 4))
    (sequence (clear 65) (sequence (Compare.preservingEquality 90 collectLevelRoles) (clear 66))))

theorem collectLevel_executes (store : Store 94) (node : Executable.Node) (level : Nat)
    (source : store 3=Encoding.node.encode node) (levelAt : store 82=level.bits)
    (empty : ∀ r:Fin 96,r=4 ∨ (65≤r.val ∧ r.val≤70) → store r=[]) :
    ∃ time ≤ 30*((store 3).length+(store 82).length+1),
      Executes collectLevel store time (Function.update store 67 [decide (node.level=level)]) := by
  let rest := (Encoding.product Encoding.optionalNatural (Encoding.product Encoding.boolean
    (Encoding.product Encoding.natural (Encoding.list (Encoding.product Encoding.natural Encoding.natural))))).encode
    (node.parent,node.leader,node.degree,node.incoming)
  have encoded : Encoding.node.encode node=Encoding.frame node.level.bits++rest := rfl
  have copy := copy_executes 93 (3:Fin 96) 65 4 (by decide) (by decide) (by decide) store (empty 4 (by simp))
  rw [empty 65 (by simp),List.append_nil,source] at copy
  let a := Function.update store 65 (Encoding.node.encode node)
  have read := unframe_canonical_executes 93 (65:Fin 96) 66 4 (by decide) (by decide) (by decide)
    a node.level.bits rest (by simp [a,encoded]) (by simp [a,empty])
  rw [show a 66=[] by simp [a,empty],List.append_nil] at read
  let b := Function.update (Function.update a 65 rest) 66 node.level.bits
  have clearRest := clear_executes (65:Fin 96) b
  rw [show b 65=rest by simp [b]] at clearRest
  let c := Function.update b 65 []
  have compare := Compare.preservingEquality_executes 90 collectLevelRoles c
    (by simp [collectLevelRoles,c,b,a,empty]) (by simp [collectLevelRoles,c,b,a,empty])
    (by simp [collectLevelRoles,c,b,a,empty])
  have left : c (collectLevelRoles 0)=node.level.bits := by simp [collectLevelRoles,c,b]
  have right : c (collectLevelRoles 1)=level.bits := by simp [collectLevelRoles,c,b,a,levelAt]
  have out : c (collectLevelRoles 2)=[] := by simp [collectLevelRoles,c,b,a,empty]
  rw [left,right,out] at compare
  simp only [Encoding.bits_injective.eq_iff] at compare
  let d := Function.update c 67 [decide (node.level=level)]
  have clearLevel := clear_executes (66:Fin 96) d
  rw [show d 66=node.level.bits by simp [d,c,b]] at clearLevel
  have final : Function.update d 66 []=Function.update store 67 [decide (node.level=level)] := by
    funext r
    by_cases r65:r=65 <;> by_cases r66:r=66 <;> by_cases r67:r=67 <;>
      simp [d,c,b,a,r65,r66,r67,empty]
  rw [final] at clearLevel
  refine ⟨_,?_,copy.sequence (read.sequence (clearRest.sequence (compare.sequence clearLevel)))⟩
  have length : (Encoding.node.encode node).length=2*node.level.bits.length+1+rest.length := by
    rw [encoded,List.length_append,Encoding.frame_length]
  have bound := Compare.preservingCost_le node.level.bits level.bits
  rw [source,levelAt]
  omega

end Counting.StackMachine.DagUpdate.Canonical
