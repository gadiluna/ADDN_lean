import Counting.StackDagDistinctPrefix
import Counting.DagDistinctCriterion

namespace Counting.StackMachine.DagValidation

theorem distinctRange_iff (values : List Executable.Node) (current : Executable.Node) (start count : Nat) :
    distinctRange values current start count=true ↔
      ∀ i,start≤ i → i<start+count → current≠values[i]?.getD default := by
  induction count generalizing start with
  | zero=>
    simp only [distinctRange,Nat.add_zero,true_iff]
    intro i lower upper
    omega
  | succ count ih=>
    rw [distinctRange,Bool.and_eq_true,ih,decide_eq_true_eq]
    constructor
    · rintro ⟨first,rest⟩ i lower upper
      by_cases equal : i=start
      · simpa only [equal] using first
      · exact rest i (by omega) (by omega)
    · intro all
      exact ⟨all start le_rfl (by omega),fun i lower upper=>all i (by omega) (by omega)⟩

theorem distinctRange_prefix (values : List Executable.Node) (current : Executable.Node) (count : Nat) :
    distinctRange values current 0 count=(List.range count).all (fun i=>values[i]?.getD default != current):=by
  apply Bool.eq_iff_iff.mpr
  simp only [distinctRange_iff,List.all_eq_true,List.mem_range,Nat.zero_add,Nat.zero_le,forall_true_left,bne_iff_ne]
  apply forall_congr'
  intro i
  exact imp_congr_right (fun _=>ne_comm)

theorem distinctAllRange_iff (values : List Executable.Node) (start count : Nat) :
    distinctAllRange values start count=true ↔
      ∀ i,start≤ i → i<start+count → distinctRange values (values[i]?.getD default) 0 i=true := by
  induction count generalizing start with
  | zero=>
    simp only [distinctAllRange,Nat.add_zero,true_iff]
    intro i lower upper
    omega
  | succ count ih=>
    rw [distinctAllRange,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨first,rest⟩ i lower upper
      by_cases equal : i=start
      · simpa only [equal] using first
      · exact rest i (by omega) (by omega)
    · intro all
      exact ⟨all start le_rfl (by omega),fun i lower upper=>all i (by omega) (by omega)⟩

theorem distinctAllRange_array (nodes : Array Executable.Node) :
    distinctAllRange nodes.toList 0 nodes.size=Executable.distinctNodesCheck nodes:=by
  apply Bool.eq_iff_iff.mpr
  simp only [distinctAllRange_iff,Executable.distinctNodesCheck,List.all_eq_true,List.mem_range,
    Nat.zero_add,Nat.zero_le,forall_true_left]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  rw [distinctRange_prefix]
  simp [Executable.distinctEarlier]

theorem distinctAllRange_eraseDups (nodes : Array Executable.Node) :
    distinctAllRange nodes.toList 0 nodes.size=true ↔ nodes.toList.eraseDups.length=nodes.size := by
  rw [distinctAllRange_array,Executable.distinctNodesCheck_iff_eraseDups]

end Counting.StackMachine.DagValidation
