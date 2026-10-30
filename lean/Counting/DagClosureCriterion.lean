import Counting.DagSemanticsValidityClosure
import Counting.DagSemanticsValidityNodes

/-! A finite scan criterion for exact backward closure in topologically
indexed DAGs. It uses actual parent/red references and needs no mutable
reachability array in the checking program. -/
namespace Counting.Executable

def DagReference (vista : Vista) (source target : Nat) : Prop :=
  (vista.node source).parent=some target ∨
    ∃ edge∈(vista.node source).incoming,edge.1=target

theorem DagReference.lt {vista : Vista} (topological : Topological vista)
    {source target : Nat} (inside : source<vista.nodes.size)
    (reference : DagReference vista source target) : target<source := by
  rcases reference with parent | ⟨edge,member,rfl⟩
  · exact (topological source inside).1 target parent
  · exact (topological source inside).2 edge member

theorem DagReach.of_reference {vista : Vista} {root source target : Nat}
    (reached : DagReach vista root source) (inside : source<vista.nodes.size)
    (reference : DagReference vista source target) : DagReach vista root target := by
  rcases reference with parent | ⟨edge,member,rfl⟩
  · exact reached.parent inside parent
  · exact reached.incoming inside member

theorem DagReach.le_root {vista : Vista} (topological : Topological vista)
    {root target : Nat} (reached : DagReach vista root target) : target≤root := by
  induction reached with
  | root => exact Nat.le_refl _
  | @parent source target _ inside parent ih =>
      exact ((topological source inside).1 target parent).le.trans ih
  | @incoming source edge _ inside member ih =>
      exact ((topological source inside).2 edge member).le.trans ih

theorem DagReach.exists_predecessor {vista : Vista} {root target : Nat}
    (reached : DagReach vista root target) (different : target≠root) :
    ∃ source,source<vista.nodes.size ∧ DagReference vista source target := by
  cases reached with
  | root => exact False.elim (different rfl)
  | @parent source target _ inside parent => exact ⟨source,inside,Or.inl parent⟩
  | @incoming source edge _ inside member => exact ⟨source,inside,Or.inr ⟨edge,member,rfl⟩⟩

theorem allReachable_of_closure_all (vista : Vista) (all : (closure vista).all id=true) :
    AllReachable vista := by
  have marked := closure_marked (DagReach vista vista.bottom) vista DagReach.root
    (fun _ inside reached _ parent => reached.parent inside parent)
    (fun _ inside reached edge member => reached.incoming inside member)
  intro i inside
  have closureInside : i<(closure vista).size := by simpa only [closure_size] using inside
  have seen := (Array.all_eq_true.mp all) i closureInside
  exact marked i (by simpa only [Array.getElem?_eq_getElem closureInside,Option.getD_some,id_eq] using seen)

/-- The bottom is the final stored index, and every earlier node has at least
one direct reference from a later stored node. -/
def BackwardCover (vista : Vista) : Prop :=
  vista.bottom+1=vista.nodes.size ∧
    ∀ target,target<vista.bottom →
      ∃ source,target<source ∧ source<vista.nodes.size ∧ DagReference vista source target

theorem backwardCover_of_allReachable (vista : Vista) (topological : Topological vista)
    (bottomInside : vista.bottom<vista.nodes.size) (reachable : AllReachable vista) :
    BackwardCover vista := by
  have lastInside : vista.nodes.size-1<vista.nodes.size := by omega
  have lastBelow := (reachable (vista.nodes.size-1) lastInside).le_root topological
  refine ⟨by omega,?_⟩
  intro target below
  obtain ⟨source,inside,reference⟩ := (reachable target (by omega)).exists_predecessor (by omega)
  exact ⟨source,reference.lt topological inside,inside,reference⟩

theorem allReachable_of_backwardCover (vista : Vista) (cover : BackwardCover vista) :
    AllReachable vista := by
  have descend (distance : Nat) : ∀ target,target≤vista.bottom → vista.bottom-target=distance →
      DagReach vista vista.bottom target := by
    induction distance using Nat.strong_induction_on with
    | h distance ih =>
      intro target below distanceEq
      by_cases same : target=vista.bottom
      · subst target;exact .root
      obtain ⟨source,later,inside,reference⟩ := cover.2 target (by omega)
      have sourceBelow : source≤vista.bottom := by have last:=cover.1;omega
      have nearer : vista.bottom-source<distance := by omega
      exact (ih (vista.bottom-source) nearer source sourceBelow rfl).of_reference inside reference
  intro target inside
  exact descend (vista.bottom-target) target (by have last:=cover.1;omega) rfl

/-- Equivalence with the actual bounded closure array. It is enough to scan
all target/source pairs once after checking topological node references. -/
theorem closure_all_iff_backwardCover (vista : Vista) (topological : Topological vista)
    (bottomInside : vista.bottom<vista.nodes.size) :
    (closure vista).all id=true ↔ BackwardCover vista := by
  constructor
  · intro closed
    exact backwardCover_of_allReachable vista topological bottomInside (allReachable_of_closure_all vista closed)
  · intro cover
    exact closure_complete vista topological bottomInside (allReachable_of_backwardCover vista cover)

theorem nodesValid_closure_iff_backwardCover (vista : Vista) (nodes : NodesValid vista)
    (bottomInside : vista.bottom<vista.nodes.size) :
    (closure vista).all id=true ↔ BackwardCover vista :=
  closure_all_iff_backwardCover vista (nodesValid_topological vista nodes) bottomInside

def referenceCheck (vista : Vista) (source target : Nat) : Bool :=
  (vista.node source).parent==some target ||
    (vista.node source).incoming.any (fun edge => edge.1==target)

theorem referenceCheck_iff (vista : Vista) (source target : Nat) :
    referenceCheck vista source target=true ↔ DagReference vista source target := by
  simp [referenceCheck,DagReference]

/-- Both scans are bounded by the explicit node count, even for an invalid
bottom index. This is a specification for the physical scan implementation. -/
def backwardCoverCheck (vista : Vista) : Bool :=
  vista.bottom+1==vista.nodes.size &&
    (List.range vista.nodes.size).all (fun target => target==vista.bottom ||
      (List.range vista.nodes.size).any (fun source => target<source && referenceCheck vista source target))

theorem backwardCoverCheck_iff (vista : Vista) :
    backwardCoverCheck vista=true ↔ BackwardCover vista := by
  simp only [backwardCoverCheck,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,
    List.mem_range,Bool.or_eq_true,List.any_eq_true,decide_eq_true_eq,referenceCheck_iff]
  constructor
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target below
    rcases covered target (by omega) with same | ⟨source,inside,later,reference⟩
    · omega
    · exact ⟨source,later,inside,reference⟩
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target inside
    by_cases same : target=vista.bottom
    · exact Or.inl same
    obtain ⟨source,later,inside,reference⟩ := covered target (by omega)
    exact Or.inr ⟨source,inside,later,reference⟩

theorem backwardCoverCheck_eq_closure_all (vista : Vista) (topological : Topological vista)
    (bottomInside : vista.bottom<vista.nodes.size) :
    backwardCoverCheck vista=(closure vista).all id := by
  apply Bool.eq_iff_iff.mpr
  exact (backwardCoverCheck_iff vista).trans (closure_all_iff_backwardCover vista topological bottomInside).symm

/-- Topological validity makes the strict source comparison redundant. -/
def backwardCoverAnyCheck (vista : Vista) : Bool :=
  vista.bottom+1==vista.nodes.size &&
    (List.range vista.nodes.size).all (fun target => target==vista.bottom ||
      (List.range vista.nodes.size).any (fun source => referenceCheck vista source target))

theorem backwardCoverAnyCheck_eq (vista : Vista) (topological : Topological vista) :
    backwardCoverAnyCheck vista=backwardCoverCheck vista := by
  apply Bool.eq_iff_iff.mpr
  simp only [backwardCoverAnyCheck,backwardCoverCheck,Bool.and_eq_true,beq_iff_eq,
    List.all_eq_true,List.mem_range,Bool.or_eq_true,List.any_eq_true,
    decide_eq_true_eq,referenceCheck_iff]
  constructor
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target inside
    rcases covered target inside with same | ⟨source,sourceInside,reference⟩
    · exact Or.inl same
    · exact Or.inr ⟨source,sourceInside,reference.lt topological sourceInside,reference⟩
  · rintro ⟨last,covered⟩
    refine ⟨last,?_⟩
    intro target inside
    rcases covered target inside with same | ⟨source,sourceInside,_,reference⟩
    · exact Or.inl same
    · exact Or.inr ⟨source,sourceInside,reference⟩

theorem backwardCoverAnyCheck_eq_closure_all (vista : Vista) (topological : Topological vista)
    (bottomInside : vista.bottom < vista.nodes.size) :
    backwardCoverAnyCheck vista=(closure vista).all id := by
  rw [backwardCoverAnyCheck_eq vista topological]
  exact backwardCoverCheck_eq_closure_all vista topological bottomInside

end Counting.Executable
