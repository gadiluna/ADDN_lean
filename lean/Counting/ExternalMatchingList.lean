import Counting.ExternalMatching

namespace Counting.External

abbrev MatchingEdge (q : Nat) := Fin q × (Fin q × Fin q)

def listToThreeDM (q : Nat) (edges : List (MatchingEdge q)) : ThreeDM q edges.length where
  edge j part := let t := edges[j.val];if part=0 then t.1 else if part=1 then t.2.1 else t.2.2

def listArc (q : Nat) (edges : List (MatchingEdge q)) (x y z : Fin q) : Bool := decide ((x,y,z)∈edges)

theorem listToThreeDM_allowed (q : Nat) (edges : List (MatchingEdge q)) (j : Fin edges.length) :
    listArc q edges ((listToThreeDM q edges).edge j 0) ((listToThreeDM q edges).edge j 1)
      ((listToThreeDM q edges).edge j 2)=true := by
  simp only [listToThreeDM,show (0:Fin 3)≠1 from by decide,show (1:Fin 3)≠0 from by decide,
    show (2:Fin 3)≠0 from by decide,show (2:Fin 3)≠1 from by decide,ite_true,ite_false,listArc,decide_eq_true_eq]
  exact List.getElem_mem j.isLt

theorem listToThreeDM_sound (q : Nat) (edges : List (MatchingEdge q))
    (yes : (listToThreeDM q edges).Yes) : Nonempty (FinMatching q (listArc q edges)) := by
  obtain ⟨chosen,perfect⟩ := yes
  let I := listToThreeDM q edges
  refine ⟨⟨I.coordinateEquiv perfect 1,I.coordinateEquiv perfect 2,?_⟩⟩
  intro x
  change listArc q edges x (I.edge (I.selectedIndex perfect x) 1) (I.edge (I.selectedIndex perfect x) 2)=true
  have allowed := listToThreeDM_allowed q edges (I.selectedIndex perfect x)
  change listArc q edges (I.edge (I.selectedIndex perfect x) 0) (I.edge (I.selectedIndex perfect x) 1)
    (I.edge (I.selectedIndex perfect x) 2)=true at allowed
  rw [(I.selectedIndex_spec perfect x).2] at allowed
  exact allowed

theorem listToThreeDM_complete (q : Nat) (edges : List (MatchingEdge q)) (M : FinMatching q (listArc q edges)) :
    (listToThreeDM q edges).Yes := by
  classical
  have represented (x : Fin q) : ∃ j : Fin edges.length,edges[j.val]=(x,M.partner x,M.port x) := by
    have member : (x,M.partner x,M.port x)∈edges := of_decide_eq_true (M.allowed x)
    obtain ⟨j,less,equal⟩ := List.mem_iff_getElem.mp member
    exact ⟨⟨j,less⟩,equal⟩
  let chosenIndex := fun x=>(represented x).choose
  let coordinate := fun part : Fin 3 => if part=0 then Equiv.refl (Fin q) else if part=1 then M.partner else M.port
  have coordinateEq (x : Fin q) (part : Fin 3) :
      (listToThreeDM q edges).edge (chosenIndex x) part=coordinate part x := by
    have equal := (represented x).choose_spec
    change edges[(chosenIndex x).val]=(x,M.partner x,M.port x) at equal
    simp only [listToThreeDM,equal,coordinate]
    split_ifs <;> rfl
  refine ⟨Finset.univ.image chosenIndex,?_⟩
  intro part v
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨chosenIndex ((coordinate part).symm v),?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,?_⟩
    rw [coordinateEq,Equiv.apply_symm_apply]
  · intro j member
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp member).1
    have value := (Finset.mem_filter.mp member).2
    rw [coordinateEq] at value
    exact congrArg chosenIndex ((coordinate part).apply_eq_iff_eq_symm_apply.mp value)

/-- Arbitrary explicit edge lists, including duplicates, represent exactly
the permitted matching relation. Enumeration order is semantically irrelevant. -/
theorem listToThreeDM_iff (q : Nat) (edges : List (MatchingEdge q)) :
    (listToThreeDM q edges).Yes ↔ Nonempty (FinMatching q (listArc q edges)) :=
  ⟨listToThreeDM_sound q edges,fun ⟨M⟩=>listToThreeDM_complete q edges M⟩

end Counting.External
