import Counting.DagSemanticsValidityCanonical

namespace Counting.Executable

def distinctEarlier (nodes : Array Node) (index : Nat) : Bool :=
  (List.range index).all (fun earlier =>
    nodes[earlier]?.getD default != nodes[index]?.getD default)

def distinctNodesCheck (nodes : Array Node) : Bool :=
  (List.range nodes.size).all (distinctEarlier nodes)

theorem distinctEarlier_iff (nodes : Array Node) (index : Nat) (inside : index < nodes.size) :
    distinctEarlier nodes index=true ↔
      ∀ earlier (before : earlier < index), nodes[earlier]'(before.trans inside) ≠ nodes[index] := by
  simp only [distinctEarlier,List.all_eq_true,List.mem_range,bne_iff_ne]
  constructor <;> intro checked earlier before
  · simpa only [Array.getElem?_eq_getElem (before.trans inside),Array.getElem?_eq_getElem inside,
      Option.getD_some] using checked earlier before
  · simpa only [Array.getElem?_eq_getElem (before.trans inside),Array.getElem?_eq_getElem inside,
      Option.getD_some] using checked earlier before

theorem distinctNodesCheck_iff_nodup (nodes : Array Node) :
    distinctNodesCheck nodes=true ↔ nodes.toList.Nodup := by
  rw [distinctNodesCheck,List.all_eq_true,List.nodup_iff_getElem?_ne_getElem?]
  constructor
  · intro checked earlier index before inside
    have indexInside : index < nodes.size := by simpa only [Array.length_toList] using inside
    have unequal := (distinctEarlier_iff nodes index indexInside).mp
      (checked index (List.mem_range.mpr indexInside)) earlier before
    simpa only [List.getElem?_eq_getElem (before.trans inside),List.getElem?_eq_getElem inside,
      Array.getElem_toList,ne_eq,Option.some.injEq] using unequal
  · intro distinct index member
    have inside := List.mem_range.mp member
    apply (distinctEarlier_iff nodes index inside).mpr
    intro earlier before
    have unequal := distinct earlier index before (by simpa only [Array.length_toList] using inside)
    have earlierInside : earlier < nodes.toList.length := by
      simpa only [Array.length_toList] using before.trans inside
    have indexInside : index < nodes.toList.length := by
      simpa only [Array.length_toList] using inside
    simpa only [List.getElem?_eq_getElem earlierInside,List.getElem?_eq_getElem indexInside,
      Array.getElem_toList,ne_eq,Option.some.injEq] using unequal

theorem distinctNodesCheck_iff_eraseDups (nodes : Array Node) :
    distinctNodesCheck nodes=true ↔ nodes.toList.eraseDups.length=nodes.size := by
  rw [distinctNodesCheck_iff_nodup]
  constructor
  · intro distinct
    rw [eraseDups_eq_of_nodup nodes.toList distinct,Array.length_toList]
  · intro sameLength
    have properties := eraseDups_sublist_nodup nodes.toList
    have equal : nodes.toList.eraseDups=nodes.toList :=
      properties.1.eq_of_length (by simpa only [Array.length_toList] using sameLength)
    rw [←equal]
    exact properties.2

end Counting.Executable
