import Counting.ExternalInitialPrepare
import Counting.ExternalInitialPredicate
import Counting.StackReadBranch

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def initialLeafSelection : Fin 6 ↪ Fin 24 := ⟨![0,17,5,18,19,20], by decide⟩
def InitialWorkspace.leafRoles (w : InitialWorkspace extra) : PolynomialWorkspace (extra+18) := initialLeafSelection.trans w

def initialLeafCoefficient (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) :=
  scaledClausesCoefficient (Cellular.alphabet program) (unaryTemplate (Cellular.alphabet program) (initialAllowed program head kind))

def initialHalfCoefficient (program : Machine.Program) (head : Bool) :=
  initialLeafCoefficient program head .blank+initialLeafCoefficient program head .zero+
    initialLeafCoefficient program head .one+initialLeafCoefficient program head .witness

def initialCoefficient (program : Machine.Program) := initialHalfCoefficient program false+initialHalfCoefficient program true

theorem initialLeafCoefficient_le (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) :
    initialLeafCoefficient program head kind ≤ initialCoefficient program := by
  cases head <;> cases kind <;> unfold initialCoefficient initialHalfCoefficient <;> omega

def initialBytes (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind) (place : Nat) :=
  Encoding.sequence clauseCodec (shiftedClauses (Cellular.alphabet program*place)
    (unaryTemplate (Cellular.alphabet program) (initialAllowed program head kind)))

def initialLeaf (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (head : Bool) (kind : InitialSymbolKind) : Routine (extra+22) :=
  initialUnaryRoutine (extra+18) w.leafRoles program head kind

theorem initialLeaf_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (head : Bool) (kind : InitialSymbolKind) (place : Nat) (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true)
    (empty : ∀ i ∈ ([17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialCoefficient program*(place+1)^2,
      Executes (initialLeaf extra w program head kind) store transitions
        (Function.update store (w 5) (initialBytes program head kind place++store (w 5))) := by
  obtain ⟨transitions,bound,run⟩ := scaledClauses_executes (extra+18) w.leafRoles (Cellular.alphabet program)
    (unaryTemplate (Cellular.alphabet program) (initialAllowed program head kind)) store
    (by simpa [InitialWorkspace.leafRoles,initialLeafSelection] using empty 17 (by simp))
    (by simpa [InitialWorkspace.leafRoles,initialLeafSelection] using empty 18 (by simp))
    (by simpa [InitialWorkspace.leafRoles,initialLeafSelection] using empty 19 (by simp))
    (by simpa [InitialWorkspace.leafRoles,initialLeafSelection] using empty 20 (by simp))
  have length : (store (w.leafRoles 0)).length=place := by simp [InitialWorkspace.leafRoles,initialLeafSelection,placeValue]
  rw [length] at bound run
  refine ⟨transitions,bound.trans (Nat.mul_le_mul_right _ (initialLeafCoefficient_le program head kind)),?_⟩
  simpa +instances [initialLeaf,initialUnaryRoutine,unaryRoutine,initialBytes,InitialWorkspace.leafRoles,initialLeafSelection] using run

def selectedKind (after : Bool) (found : Option Bool) (outside : Bool) : InitialSymbolKind :=
  if after then match found with
    | some bit => bitKind bit
    | none => if outside then .blank else .witness
  else .blank

def initialBitSelect (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) (head : Bool) : Routine (extra+22) :=
  branchRead (w 9) (initialLeaf extra w program head .one) (initialLeaf extra w program head .zero)

def initialAbsentSelect (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) (head : Bool) : Routine (extra+22) :=
  branchRead (w 11) (initialLeaf extra w program head .blank) (initialLeaf extra w program head .witness)

def initialPresentSelect (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) (head : Bool) : Routine (extra+22) :=
  branchRead (w 10) (initialBitSelect extra w program head) (initialAbsentSelect extra w program head)

def initialKindSelect (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) (head : Bool) : Routine (extra+22) :=
  branchRead (w 7) (initialPresentSelect extra w program head) (initialLeaf extra w program head .blank)

theorem initialKindSelect_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (head after outside : Bool) (found : Option Bool) (place : Nat) (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true)
    (afterValue : store (w 7)=[after]) (bitValue : store (w 9)=found.toList)
    (presentValue : store (w 10)=[found.isSome]) (outsideValue : store (w 11)=[outside])
    (empty : ∀ i ∈ ([17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialCoefficient program*(place+1)^2+9,
      Executes (initialKindSelect extra w program head) store transitions
        (Function.update store (w 5) (initialBytes program head (selectedKind after found outside) place++store (w 5))) := by
  cases after
  · obtain ⟨transitions,bound,run⟩ := initialLeaf_executes extra w program head .blank place store placeValue empty
    have selected := branchRead_executes (w 7) (initialPresentSelect extra w program head) (initialLeaf extra w program head .blank)
      false [] store _ transitions afterValue run
    exact ⟨transitions+3,by omega,selected⟩
  · cases found with
    | none =>
        obtain ⟨transitions,bound,run⟩ := initialLeaf_executes extra w program head (if outside then .blank else .witness)
          place store placeValue empty
        have leaf : Executes (if outside then initialLeaf extra w program head .blank else initialLeaf extra w program head .witness)
            store transitions (Function.update store (w 5)
              (initialBytes program head (if outside then .blank else .witness) place++store (w 5))) := by
          cases outside <;> exact run
        have chosen : Executes (initialAbsentSelect extra w program head) store (transitions+3)
            (Function.update store (w 5) (initialBytes program head (if outside then .blank else .witness) place++store (w 5))) := branchRead_executes (w 11) (initialLeaf extra w program head .blank) (initialLeaf extra w program head .witness)
          outside [] store _ transitions outsideValue leaf
        have present : Executes (initialPresentSelect extra w program head) store (transitions+3+3)
            (Function.update store (w 5) (initialBytes program head (selectedKind true none outside) place++store (w 5))) := branchRead_executes (w 10) (initialBitSelect extra w program head) (initialAbsentSelect extra w program head)
          false [] store _ (transitions+3) presentValue chosen
        have afterRun : Executes (initialKindSelect extra w program head) store (transitions+3+3+3)
            (Function.update store (w 5) (initialBytes program head (selectedKind true none outside) place++store (w 5))) := branchRead_executes (w 7) (initialPresentSelect extra w program head) (initialLeaf extra w program head .blank)
          true [] store _ (transitions+3+3) afterValue present
        exact ⟨transitions+3+3+3,by omega,afterRun⟩
    | some bit =>
        obtain ⟨transitions,bound,run⟩ := initialLeaf_executes extra w program head (bitKind bit) place store placeValue empty
        have leaf : Executes (if bit then initialLeaf extra w program head .one else initialLeaf extra w program head .zero)
            store transitions (Function.update store (w 5) (initialBytes program head (bitKind bit) place++store (w 5))) := by
          cases bit <;> exact run
        have chosen : Executes (initialBitSelect extra w program head) store (transitions+3)
            (Function.update store (w 5) (initialBytes program head (bitKind bit) place++store (w 5))) := branchRead_executes (w 9) (initialLeaf extra w program head .one) (initialLeaf extra w program head .zero)
          bit [] store _ transitions bitValue leaf
        have present : Executes (initialPresentSelect extra w program head) store (transitions+3+3)
            (Function.update store (w 5) (initialBytes program head (bitKind bit) place++store (w 5))) := branchRead_executes (w 10) (initialBitSelect extra w program head) (initialAbsentSelect extra w program head)
          true [] store _ (transitions+3) presentValue chosen
        have afterRun : Executes (initialKindSelect extra w program head) store (transitions+3+3+3)
            (Function.update store (w 5) (initialBytes program head (selectedKind true (some bit) outside) place++store (w 5))) := branchRead_executes (w 7) (initialPresentSelect extra w program head) (initialLeaf extra w program head .blank)
          true [] store _ (transitions+3+3) afterValue present
        exact ⟨transitions+3+3+3,by omega,afterRun⟩

def initialSelect (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  branchRead (w 8) (initialKindSelect extra w program true) (initialKindSelect extra w program false)

theorem initialSelect_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    (head after outside : Bool) (found : Option Bool) (place : Nat) (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (headValue : store (w 8)=[head])
    (afterValue : store (w 7)=[after]) (bitValue : store (w 9)=found.toList)
    (presentValue : store (w 10)=[found.isSome]) (outsideValue : store (w 11)=[outside])
    (empty : ∀ i ∈ ([17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialCoefficient program*(place+1)^2+12,
      Executes (initialSelect extra w program) store transitions
        (Function.update store (w 5) (initialBytes program head (selectedKind after found outside) place++store (w 5))) := by
  obtain ⟨transitions,bound,run⟩ := initialKindSelect_executes extra w program head after outside found place store
    placeValue afterValue bitValue presentValue outsideValue empty
  have body : Executes (if head then initialKindSelect extra w program true else initialKindSelect extra w program false)
      store transitions (Function.update store (w 5) (initialBytes program head (selectedKind after found outside) place++store (w 5))) := by
    cases head <;> exact run
  exact ⟨transitions+3,by omega,branchRead_executes (w 8) _ _ head [] store _ transitions headValue body⟩

end Counting.External.CookLevin.StackGenerator
