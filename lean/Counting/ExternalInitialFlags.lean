import Counting.ExternalInitialCounters

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def afterSelection : Fin 6 ↪ Fin 24 := ⟨![1,0,7,13,14,15], by decide⟩
def headSelection : Fin 6 ↪ Fin 24 := ⟨![0,1,8,13,14,15], by decide⟩
def lookupSelection : Fin 7 ↪ Fin 24 := ⟨![2,6,9,10,13,14,15], by decide⟩
def outsideSelection : Fin 6 ↪ Fin 24 := ⟨![12,6,11,13,14,15], by decide⟩

def InitialWorkspace.afterRoles (w : InitialWorkspace extra) : Fin 6 ↪ Fin (extra+24) := afterSelection.trans w
def InitialWorkspace.headRoles (w : InitialWorkspace extra) : Fin 6 ↪ Fin (extra+24) := headSelection.trans w
def InitialWorkspace.lookupRoles (w : InitialWorkspace extra) : Fin 7 ↪ Fin (extra+24) := lookupSelection.trans w
def InitialWorkspace.outsideRoles (w : InitialWorkspace extra) : Fin 6 ↪ Fin (extra+24) := outsideSelection.trans w

def initialAfter (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  Compare.preservingLengthLE (extra+18) w.afterRoles

def initialHead (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  Compare.preservingEquality (extra+18) w.headRoles

def initialLookup (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  Lookup.preservingLookup (extra+17) w.lookupRoles

def initialOutside (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  Compare.preservingLengthLE (extra+18) w.outsideRoles

theorem initialAfter_executes (extra : Nat) (w : InitialWorkspace extra) (place offset : Nat)
    (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (empty : ∀ i ∈ ([13,14,15] : List (Fin 24)), store (w i)=[]) :
    Executes (initialAfter extra w) store (6*(offset+place)+9)
      (Function.update store (w 7) (decide (offset≤place)::store (w 7))) := by
  simpa +instances [initialAfter,InitialWorkspace.afterRoles,afterSelection,Compare.preservingLengthCost_eq,placeValue,offsetValue] using
    Compare.preservingLengthLE_executes (extra+18) w.afterRoles store
      (by simpa [InitialWorkspace.afterRoles,afterSelection] using empty 13 (by simp))
      (by simpa [InitialWorkspace.afterRoles,afterSelection] using empty 14 (by simp))
      (by simpa [InitialWorkspace.afterRoles,afterSelection] using empty 15 (by simp))

theorem initialHead_executes (extra : Nat) (w : InitialWorkspace extra) (place offset : Nat)
    (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (empty : ∀ i ∈ ([13,14,15] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ 6*(place+offset)+11,
      Executes (initialHead extra w) store transitions
        (Function.update store (w 8) (decide (place=offset)::store (w 8))) := by
  have run := Compare.preservingEquality_executes (extra+18) w.headRoles store
    (by simpa [InitialWorkspace.headRoles,headSelection] using empty 13 (by simp))
    (by simpa [InitialWorkspace.headRoles,headSelection] using empty 14 (by simp))
    (by simpa [InitialWorkspace.headRoles,headSelection] using empty 15 (by simp))
  have unaryEquality : (List.replicate place true=List.replicate offset true) ↔ place=offset := by
    constructor
    · intro h; simpa only [List.length_replicate] using congrArg List.length h
    · intro h; rw [h]
  refine ⟨Compare.preservingCost (List.replicate place true) (List.replicate offset true),?_,?_⟩
  · simpa only [List.length_replicate] using Compare.preservingCost_le (List.replicate place true) (List.replicate offset true)
  · simpa +instances [initialHead,InitialWorkspace.headRoles,headSelection,placeValue,offsetValue,unaryEquality] using run

theorem initialLookup_executes (extra : Nat) (w : InitialWorkspace extra) (index : Nat)
    (store : Fin (extra+24) → List Bool) (indexValue : store (w 6)=List.replicate index true)
    (empty : ∀ i ∈ ([13,14,15] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ 6*(store (w 2)).length+7*index+13,
      Executes (initialLookup extra w) store transitions
        (Function.update (Function.update store (w 9) ((store (w 2))[index]?.toList++store (w 9)))
          (w 10) ((store (w 2))[index]?.isSome::store (w 10))) := by
  have run := Lookup.preservingLookup_executes (extra+17) w.lookupRoles store
    (by simpa [InitialWorkspace.lookupRoles,lookupSelection] using empty 13 (by simp))
    (by simpa [InitialWorkspace.lookupRoles,lookupSelection] using empty 14 (by simp))
    (by simpa [InitialWorkspace.lookupRoles,lookupSelection] using empty 15 (by simp))
  refine ⟨Lookup.lookupCost (store (w 2)) (List.replicate index true),?_,?_⟩
  · simpa only [List.length_replicate] using Lookup.lookupCost_le (store (w 2)) (List.replicate index true)
  · simpa +instances [initialLookup,InitialWorkspace.lookupRoles,lookupSelection,indexValue] using run

theorem initialOutside_executes (extra : Nat) (w : InitialWorkspace extra) (index stop : Nat)
    (store : Fin (extra+24) → List Bool)
    (indexValue : store (w 6)=List.replicate index true) (stopValue : store (w 12)=List.replicate stop true)
    (empty : ∀ i ∈ ([13,14,15] : List (Fin 24)), store (w i)=[]) :
    Executes (initialOutside extra w) store (6*(stop+index)+9)
      (Function.update store (w 11) (decide (stop≤ index)::store (w 11))) := by
  simpa +instances [initialOutside,InitialWorkspace.outsideRoles,outsideSelection,Compare.preservingLengthCost_eq,indexValue,stopValue] using
    Compare.preservingLengthLE_executes (extra+18) w.outsideRoles store
      (by simpa [InitialWorkspace.outsideRoles,outsideSelection] using empty 13 (by simp))
      (by simpa [InitialWorkspace.outsideRoles,outsideSelection] using empty 14 (by simp))
      (by simpa [InitialWorkspace.outsideRoles,outsideSelection] using empty 15 (by simp))

end Counting.External.CookLevin.StackGenerator
