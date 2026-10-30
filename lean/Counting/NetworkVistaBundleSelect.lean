import Counting.NetworkVistaBundleEmit
import Counting.StackBranchNonempty

namespace Counting.StackMachine.NetworkVista
open Routine

def selectBundle : Routine 14 := branchNonempty 5 emitBundle (skip 14)

def selectedBundleStore (store:Store 14) : Store 14 :=
  if (store 5).isEmpty then store else emitBundleStore store

theorem selectBundle_executes (store:Store 14) (e8:store 8=[]) (e9:store 9=[]) :
    ∃time ≤ 7*(store 0).length+9*(store 5).length+18,
      Executes selectBundle store time (selectedBundleStore store) := by
  cases amount:store 5 with
  | nil=>
    refine ⟨1,by omega,?_⟩
    simpa [selectBundle,selectedBundleStore,amount] using
      branchNonempty_empty (5:Fin 16) emitBundle (skip 14) store store 0 amount (skip_executes store)
  | cons bit tail=>
    refine ⟨7*(store 0).length+9*(bit::tail).length+15+3,by omega,?_⟩
    simpa [selectBundle,selectedBundleStore,amount] using
      branchNonempty_cons (5:Fin 16) emitBundle (skip 14) store (emitBundleStore store) bit tail
        (7*(store 0).length+9*(store 5).length+15) amount (emitBundle_executes store e8 e9)

theorem selectedBundleStore_typed (store:Store 14) (vista:Executable.Vista) (count:Nat)
    (view:store 0=Encoding.vista.encode vista) (amount:store 5=count.bits) :
    selectedBundleStore store=
      if count=0 then store else
        Function.update (Function.update (Function.update store 5 [])
          3 (((Encoding.product Encoding.vista Encoding.natural).encode (vista,count)).reverse++store 3))
          4 (true::store 4) := by
  have empty:count.bits.isEmpty=true ↔ count=0:=by
    rw [List.isEmpty_iff]
    constructor
    · intro zero
      have value:=congrArg Encoding.value zero
      simpa only [Encoding.value_bits,Encoding.value] using value
    · intro zero;subst count;rfl
  simp only [selectedBundleStore,amount,empty,emitBundleStore,view,Encoding.product,Encoding.natural]

end Counting.StackMachine.NetworkVista
