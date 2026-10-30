import Counting.StackDagInternScan
import Counting.StackRoutineCopyReverse
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.DagUpdate.Intern
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def scanRoles : Fin 32 ↪ Fin 64 := ⟨fun r=>⟨r.val+4,by have:=r.isLt;omega⟩,by
  intro a b equal
  apply Fin.ext
  have value := congrArg (fun r : Fin 64=>r.val) equal
  dsimp at value
  omega⟩

def searchQueryRoles : Fin 4 ↪ Fin 64 := ⟨![1,21,36,37],by decide⟩

def searchTable : Routine 62 :=
  sequence (ofProgram (ListPrograms.copyProgram 61 0 4 36))
    (sequence (copyReverse 60 searchQueryRoles)
      (sequence (pushBit 5 true) (sequence (pushBit 23 false)
        (sequence (mapRegisters scanRoles scan) (sequence (clear 5) (clear 21))))))

def searched (store : Store 62) (query : Executable.Node) (nodes : List Executable.Node) : Store 62 :=
  Function.update (Function.update store 23 [(Executable.firstIndex query nodes).isSome]) 22
    (List.replicate ((Executable.firstIndex query nodes).getD nodes.length) true)

/-- Search preserves both the original table and the queried signature.
The only outputs are a unary first index and a found flag. -/
theorem searchTable_executes (store : Store 62) (nodes : List Executable.Node) (query : Executable.Node)
    (source : store 0=(Encoding.list Encoding.node).encode nodes)
    (queryAt : store 1=Encoding.node.encode query)
    (empty : ∀ r : Fin 64,4 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 6000*((store 0).length+(store 1).length+1)^4,
      Executes searchTable store time (searched store query nodes) := by
  have sourceCopy := copy_executes 61 (0:Fin 64) 4 36 (by decide) (by decide) (by decide)
    store (empty 36 (by decide) (by decide))
  rw [empty 4 (by decide) (by decide),List.append_nil] at sourceCopy
  let copied := Function.update store 4 (store 0)
  have queryCopy := copyReverse_executes 60 searchQueryRoles copied
    (by simp [copied,searchQueryRoles,empty]) (by simp [copied,searchQueryRoles,empty])
  have sourceQuery : copied (searchQueryRoles 0)=store 1 := by simp [copied,searchQueryRoles]
  have targetQuery : copied (searchQueryRoles 1)=[] := by simp [copied,searchQueryRoles,empty]
  rw [sourceQuery,targetQuery,List.append_nil] at queryCopy
  let queryCopied := Function.update copied 21 (store 1).reverse
  have statusPush := pushBit_executes (5:Fin 64) true queryCopied
  have statusEmpty : queryCopied 5=[] := by simp [queryCopied,copied,empty]
  rw [statusEmpty] at statusPush
  let initialized := Function.update queryCopied 5 [true]
  have foundPush := pushBit_executes (23:Fin 64) false initialized
  have foundEmpty : initialized 23=[] := by simp [initialized,queryCopied,copied,empty]
  rw [foundEmpty] at foundPush
  let ready := Function.update initialized 23 [false]
  let localStore : Store 30 := ready ∘ scanRoles
  obtain ⟨scanTime,scanBound,scanRun⟩ := scan_executes localStore query nodes []
    (by simpa [localStore,scanRoles,ready,initialized,queryCopied,copied] using source)
    (by simp [localStore,scanRoles,ready,initialized,queryCopied,queryAt])
    (by simp [localStore,scanRoles,ready,initialized])
    (by simp [localStore,scanRoles,ready])
    (by simp [localStore,scanRoles,ready,initialized,queryCopied,copied,empty]) (by
      intro r member
      fin_cases r <;> simp_all [localStore,scanRoles,ready,initialized,queryCopied,copied])
  let checked := Function.update (Function.update (Function.update ready 4 [])
    23 [(Executable.firstIndex query nodes).isSome]) 22
    (List.replicate ((Executable.firstIndex query nodes).getD nodes.length) true)
  have relocated : Executes (mapRegisters scanRoles scan) ready scanTime checked := by
    apply relocate_executes_frame scan scanRoles ready checked localStore
      (searchResult localStore query nodes []) scanTime rfl _ _ scanRun
    · intro r
      fin_cases r <;> simp [checked,searchResult,localStore,scanRoles]
    · intro r outside
      have n4 : r≠4 := fun eq=>outside 0 (by simpa [scanRoles] using eq.symm)
      have n22 : r≠22 := fun eq=>outside 18 (by simpa [scanRoles] using eq.symm)
      have n23 : r≠23 := fun eq=>outside 19 (by simpa [scanRoles] using eq.symm)
      simp [checked,n4,n22,n23]
  have clearStatus := clear_executes (5:Fin 64) checked
  have statusAt : checked 5=[true] := by simp [checked,ready,initialized]
  rw [statusAt] at clearStatus
  let noStatus := Function.update checked 5 []
  have clearQuery := clear_executes (21:Fin 64) noStatus
  have queryValue : noStatus 21=(store 1).reverse := by
    simp [noStatus,checked,ready,initialized,queryCopied]
  rw [queryValue,List.length_reverse] at clearQuery
  have final : Function.update noStatus 21 []=searched store query nodes := by
    funext r
    fin_cases r <;> simp [noStatus,checked,ready,initialized,queryCopied,copied,searched,empty]
  rw [final] at clearQuery
  refine ⟨_,?_,sourceCopy.sequence (queryCopy.sequence (statusPush.sequence
    (foundPush.sequence (relocated.sequence (clearStatus.sequence clearQuery)))))⟩
  have localInput : localStore 0=store 0 := by simp [localStore,scanRoles,ready,initialized,queryCopied,copied]
  have localQuery : (localStore 17).length=(store 1).length := by
    simp [localStore,scanRoles,ready,initialized,queryCopied]
  rw [localInput,localQuery] at scanBound
  let K := (store 0).length+(store 1).length+1
  have positive : 1 ≤ K := by omega
  have fields : (store 0).length+(store 1).length ≤ K := by omega
  have linear : K ≤ K^4 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^4 := one_le_pow₀ positive
  change _ ≤ 6000*K^4
  change scanTime ≤ 5000*K^4 at scanBound
  simp only [List.length_cons,List.length_nil]
  nlinarith only [scanBound,fields,linear,one]

end Counting.StackMachine.DagUpdate.Intern
