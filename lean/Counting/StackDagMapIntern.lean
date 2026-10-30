import Counting.StackDagMapInternBank
import Counting.StackRoutineMove

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def mapIntern : Routine 94 := sequence mapNode
  (sequence (move 93 0 67 4) (sequence (move 93 1 68 4) (sequence (move 93 3 1 4)
    (sequence (ofProgram (ListPrograms.copyProgram 93 64 0 4))
      (sequence internNode (sequence (clear 0) (sequence (clear 1)
        (sequence (move 93 2 65 4) (sequence (move 93 3 66 4)
          (sequence (move 93 67 0 4) (move 93 68 1 4)))))))))))

def mapInternBudget (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) (suffix : List Bool) : Nat :=
  let mapped := Executable.referenceMap mapping node
  let result := Executable.intern pool mapped
  let M := ((Encoding.array Encoding.natural).encode mapping).length
  let P := ((Encoding.array Encoding.node).encode pool).length
  let Q := (Encoding.node.encode mapped).length
  30000000000*((Encoding.node.encode node).length+suffix.length+M+1)^7+
  8000*(P+Q+1)^4+12*suffix.length+12*M+7*Q+6*P+
  6*((Encoding.array Encoding.node).encode result.1).length+6*result.2.bits.length+43

/-- The actual import transaction: remap one compact signature and intern
it in the saved pool, preserving the mapping and original pool for the
caller's subsequent update. -/
theorem mapIntern_executes (store : Store 94) (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) (suffix : List Bool)
    (source : store 0=Encoding.node.encode node++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 68 → r≠64 → store r=[]) :
    ∃ time ≤ mapInternBudget mapping pool node suffix,
      Executes mapIntern store time
        (Function.update (Function.update (Function.update store 0 suffix) 65
          ((Encoding.array Encoding.node).encode (Executable.intern pool (Executable.referenceMap mapping node)).1))
          66 (Executable.intern pool (Executable.referenceMap mapping node)).2.bits) := by
  let target := Executable.referenceMap mapping node
  let result := Executable.intern pool target
  let mappingCode := (Encoding.array Encoding.natural).encode mapping
  let poolCode := (Encoding.array Encoding.node).encode pool
  let nodeCode := Encoding.node.encode target
  let resultCode := (Encoding.array Encoding.node).encode result.1
  obtain ⟨mapTime,mapBound,mapRun⟩ := mapNode_executes store mapping node suffix source mappingAt (by
    intro r lower upper
    exact empty r lower (by omega) (by intro eq;subst r;norm_num at upper))
  let mapped := Function.update (Function.update store 0 suffix) 3 nodeCode
  have saveSuffix := move_executes 93 (0:Fin 96) 67 4 (by decide) (by decide) (by decide)
    mapped (by simp [mapped,empty])
  have suffixValue : mapped 0=suffix := by simp [mapped]
  have suffixEmpty : mapped 67=[] := by simp [mapped,empty]
  rw [suffixValue,suffixEmpty,List.append_nil] at saveSuffix
  let suffixSaved := Function.update (Function.update mapped 67 suffix) 0 []
  have saveMapping := move_executes 93 (1:Fin 96) 68 4 (by decide) (by decide) (by decide)
    suffixSaved (by simp [suffixSaved,mapped,empty])
  have mappingValue : suffixSaved 1=mappingCode := by simp [suffixSaved,mapped,mappingAt,mappingCode]
  have mappingEmpty : suffixSaved 68=[] := by simp [suffixSaved,mapped,empty]
  rw [mappingValue,mappingEmpty,List.append_nil] at saveMapping
  let mappingSaved := Function.update (Function.update suffixSaved 68 mappingCode) 1 []
  have moveNode := move_executes 93 (3:Fin 96) 1 4 (by decide) (by decide) (by decide)
    mappingSaved (by simp [mappingSaved,suffixSaved,mapped,empty])
  have nodeValue : mappingSaved 3=nodeCode := by simp [mappingSaved,suffixSaved,mapped]
  have queryEmpty : mappingSaved 1=[] := by simp [mappingSaved]
  rw [nodeValue,queryEmpty,List.append_nil] at moveNode
  let nodeReady := Function.update (Function.update mappingSaved 1 nodeCode) 3 []
  have copyPool := copy_executes 93 (64:Fin 96) 0 4 (by decide) (by decide) (by decide)
    nodeReady (by simp [nodeReady,mappingSaved,suffixSaved,mapped,empty])
  have poolValue : nodeReady 64=poolCode := by simp [nodeReady,mappingSaved,suffixSaved,mapped,poolAt,poolCode]
  have sourceEmpty : nodeReady 0=[] := by simp [nodeReady,mappingSaved,suffixSaved]
  rw [poolValue,sourceEmpty,List.append_nil] at copyPool
  let ready := Function.update nodeReady 0 poolCode
  obtain ⟨internTime,internBound,internRun⟩ := internNode_executes ready pool target
    (by rfl) (by simp [ready,nodeReady,nodeCode]) (by
      intro r lower upper
      fin_cases r <;> simp_all [ready,nodeReady,mappingSaved,suffixSaved,mapped])
  let interned := Function.update (Function.update ready 2 resultCode) 3 result.2.bits
  have erasePool := clear_executes (0:Fin 96) interned
  have oldPool : interned 0=poolCode := by simp [interned,ready]
  rw [oldPool] at erasePool
  let noPool := Function.update interned 0 []
  have eraseNode := clear_executes (1:Fin 96) noPool
  have oldNode : noPool 1=nodeCode := by simp [noPool,interned,ready,nodeReady]
  rw [oldNode] at eraseNode
  let cleared := Function.update noPool 1 []
  have outputPool := move_executes 93 (2:Fin 96) 65 4 (by decide) (by decide) (by decide)
    cleared (by simp [cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty])
  have nextPool : cleared 2=resultCode := by simp [cleared,noPool,interned]
  have outputPoolEmpty : cleared 65=[] := by
    simp [cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty]
  rw [nextPool,outputPoolEmpty,List.append_nil] at outputPool
  let poolOutput := Function.update (Function.update cleared 65 resultCode) 2 []
  have outputIndex := move_executes 93 (3:Fin 96) 66 4 (by decide) (by decide) (by decide)
    poolOutput (by simp [poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty])
  have nextIndex : poolOutput 3=result.2.bits := by simp [poolOutput,cleared,noPool,interned]
  have outputIndexEmpty : poolOutput 66=[] := by
    simp [poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty]
  rw [nextIndex,outputIndexEmpty,List.append_nil] at outputIndex
  let indexOutput := Function.update (Function.update poolOutput 66 result.2.bits) 3 []
  have restoreSuffix := move_executes 93 (67:Fin 96) 0 4 (by decide) (by decide) (by decide)
    indexOutput (by simp [indexOutput,poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty])
  have savedSuffix : indexOutput 67=suffix := by
    simp [indexOutput,poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved]
  have suffixTarget : indexOutput 0=[] := by simp [indexOutput,poolOutput,cleared,noPool]
  rw [savedSuffix,suffixTarget,List.append_nil] at restoreSuffix
  let suffixRestored := Function.update (Function.update indexOutput 0 suffix) 67 []
  have restoreMapping := move_executes 93 (68:Fin 96) 1 4 (by decide) (by decide) (by decide)
    suffixRestored (by simp [suffixRestored,indexOutput,poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved,suffixSaved,mapped,empty])
  have savedMapping : suffixRestored 68=mappingCode := by
    simp [suffixRestored,indexOutput,poolOutput,cleared,noPool,interned,ready,nodeReady,mappingSaved]
  have mappingTarget : suffixRestored 1=[] := by simp [suffixRestored,indexOutput,poolOutput,cleared]
  rw [savedMapping,mappingTarget,List.append_nil] at restoreMapping
  have final : Function.update (Function.update suffixRestored 1 mappingCode) 68 []=
      Function.update (Function.update (Function.update store 0 suffix) 65 resultCode) 66 result.2.bits := by
    funext r
    fin_cases r <;> simp [suffixRestored,indexOutput,poolOutput,cleared,noPool,interned,ready,nodeReady,
      mappingSaved,suffixSaved,mapped,empty,mappingCode,mappingAt]
  rw [final] at restoreMapping
  refine ⟨_,?_,mapRun.sequence (saveSuffix.sequence (saveMapping.sequence (moveNode.sequence
    (copyPool.sequence (internRun.sequence (erasePool.sequence (eraseNode.sequence
      (outputPool.sequence (outputIndex.sequence (restoreSuffix.sequence restoreMapping))))))))))⟩
  have readyPool : ready 0=poolCode := by simp [ready]
  have readyNode : ready 1=nodeCode := by simp [ready,nodeReady]
  rw [readyPool,readyNode] at internBound
  rw [source,mappingAt,List.length_append] at mapBound
  dsimp only [mapInternBudget]
  dsimp only [poolCode,nodeCode,mappingCode,resultCode,result,target] at internBound ⊢
  omega

end Counting.StackMachine.DagUpdate.Import
