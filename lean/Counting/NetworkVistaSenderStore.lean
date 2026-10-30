import Counting.NetworkVistaSenderLayout

namespace Counting.StackMachine.NetworkVista
open Routine

theorem bundleReplicatePush (n:Nat) (rest:List Bool) :
    List.replicate n true++true::rest=true::(List.replicate n true++rest) := by
  induction n with
  | zero=>rfl
  | succ n ih=>simp only [List.replicate_succ,List.cons_append,ih]

theorem senderItemStore_other (store:Store 38) (vista:Executable.Vista) (amount:Nat)
    (viewSuffix rowSuffix:List Bool) (r:Fin 40)
    (n21:r≠21) (n22:r≠22) (n24:r≠24) (n25:r≠25) :
    senderItemStore store vista amount viewSuffix rowSuffix r=store r := by
  simp [senderItemStore,ite_apply,n21,n22,n24,n25]

theorem senderItemStore_empty (store:Store 38) (vista:Executable.Vista) (amount:Nat)
    (viewSuffix rowSuffix:List Bool) (empty:SenderEmpty store) :
    SenderEmpty (senderItemStore store vista amount viewSuffix rowSuffix) := by
  constructor
  · intro r small n1
    rw [senderItemStore_other]
    · exact empty.1 r small n1
    all_goals intro same;subst r;norm_num at small
  · intro r low high
    rw [senderItemStore_other]
    · exact empty.2 r low high
    all_goals intro same;subst r;norm_num at low

theorem senderItemStore_viewSuffix (store:Store 38) (vista:Executable.Vista) (amount:Nat)
    (viewSuffix rowSuffix:List Bool) :
    senderItemStore store vista amount viewSuffix rowSuffix 21=viewSuffix := by simp [senderItemStore,ite_apply]

theorem senderItemStore_rowSuffix (store:Store 38) (vista:Executable.Vista) (amount:Nat)
    (viewSuffix rowSuffix:List Bool) :
    senderItemStore store vista amount viewSuffix rowSuffix 22=rowSuffix := by simp [senderItemStore,ite_apply]

end Counting.StackMachine.NetworkVista
