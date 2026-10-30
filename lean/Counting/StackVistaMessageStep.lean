import Counting.StackVistaMessageMerge
import Counting.StackDagImportPolynomial
import Counting.DagSemanticsUpdate

namespace Counting.StackMachine.DagUpdate.Receive
open Routine
set_option backward.isDefEq.respectTransparency false

def messageCodec : Encoding.Codec (Executable.Vista×Nat) :=
  Encoding.product Encoding.vista Encoding.natural

def messageStep : Routine 94 := sequence Import.importNodes mergeTail

def messageStepBudget (pool : Array Executable.Node) (message : Executable.Vista×Nat)
    (edges : List (Nat×Nat)) (sourceLength : Nat) : Nat :=
  Import.importNodesBudget pool message.1.nodes.toList sourceLength+1+
    mergeTailBudget (Executable.importVista pool message.1).2 message.1.bottom message.2 edges

def messageResult (store : Store 94) (state : Executable.MergeState)
    (message : Executable.Vista×Nat) (suffix : List Bool) : Store 94 :=
  let next := Executable.mergeMessage state message
  Function.update (Function.update (Function.update store 70 suffix)
    64 ((Encoding.array Encoding.node).encode next.1))
    75 ((Encoding.list edgeCodec).encode next.2)

/-- Import one received DAG, obtain its remapped bottom, and add its binary
multiplicity. This is the actual transition used by `rawUpdate`. -/
theorem messageStep_executes (store : Store 94) (state : Executable.MergeState)
    (message : Executable.Vista×Nat) (suffix : List Bool)
    (source : store 70=messageCodec.encode message++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (edgesAt : store 75=(Encoding.list edgeCodec).encode state.2)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,r.val≤73 → r≠64 → r≠70 → r≠71 → store r=[]) :
    ∃ time ≤ messageStepBudget state.1 message state.2 (store 70).length,
      Executes messageStep store time (messageResult store state message suffix) := by
  let tail := Encoding.natural.encode message.1.bottom++Encoding.natural.encode message.2++suffix
  have input : store 70=(Encoding.array Encoding.node).encode message.1.nodes++tail := by
    simpa only [messageCodec,Encoding.product,Encoding.vista,Encoding.transport,
      Encoding.array,List.append_assoc,tail] using source
  obtain ⟨importTime,importBound,importRun⟩ := Import.importNodes_executes_importVista
    store state.1 message.1 tail input poolAt status (by
      intro r eligible
      rcases eligible with ⟨small,ne⟩|rfl|rfl
      · apply empty r (by omega) ne
        · intro eq;subst r;norm_num at small
        · intro eq;subst r;norm_num at small
      · exact empty _ (by decide) (by decide) (by decide) (by decide)
      · exact empty _ (by decide) (by decide) (by decide) (by decide))
  let imported := Function.update (Function.update (Function.update store 70 tail)
    1 ((Encoding.array Encoding.natural).encode (Executable.importVista state.1 message.1).2))
    64 ((Encoding.array Encoding.node).encode (Executable.importVista state.1 message.1).1)
  have scratch (r : Fin 96) (small : r.val≤34) (ne : r≠1) : imported r=[] := by
    have n64 : r≠64 := by intro eq;subst r;norm_num at small
    have n70 : r≠70 := by intro eq;subst r;norm_num at small
    have n71 : r≠71 := by intro eq;subst r;norm_num at small
    simp [imported,n64,n70,ne,empty r (by omega) n64 n70 n71]
  obtain ⟨tailTime,tailBound,tailRun⟩ := mergeTail_executes imported
    (Executable.importVista state.1 message.1).2 message.1.bottom message.2 state.2 suffix
    (by simp [imported,tail]) (by simp [imported])
    (by simp [imported,edgesAt]) scratch
  have final : Function.update (Function.update (Function.update imported 70 suffix) 1 []) 75
      ((Encoding.list edgeCodec).encode
        (Executable.addCount ((Executable.importVista state.1 message.1).2[message.1.bottom]?.getD 0)
          message.2 state.2))=messageResult store state message suffix := by
    funext r
    by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
      by_cases r75 : r=75 <;>
      simp [messageResult,Executable.mergeMessage,imported,r1,r64,r70,r75,empty]
  rw [final] at tailRun
  exact ⟨_,by unfold messageStepBudget;omega,importRun.sequence tailRun⟩

end Counting.StackMachine.DagUpdate.Receive
