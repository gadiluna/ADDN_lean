import Counting.ExternalInitialGenerator
import Counting.ExternalFinalClause
import Counting.ExternalOneHotGenerator
import Counting.ExternalTransitionLoop

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Persistent roles: time, width, offset, framed input, witness capacity,
output, and cell count at index 26. The other referenced roles are scratch. -/
abbrev GeneratorWorkspace (extra : Nat) := Fin 32 ↪ Fin (extra+32)

def generatorInitialSelection : Fin 24 ↪ Fin 32 :=
  ⟨![6,2,3,4,1,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,31,21,22,23],by decide⟩
def generatorCoordinateSelection : Fin 12 ↪ Fin 32 := ⟨![27,1,6,7,8,9,10,5,11,12,13,31],by decide⟩
def generatorOneHotSelection : Fin 6 ↪ Fin 32 := ⟨![26,7,5,18,19,31],by decide⟩

def GeneratorWorkspace.initialRoles (w : GeneratorWorkspace extra) : InitialWorkspace (extra+8) := generatorInitialSelection.trans w
def GeneratorWorkspace.coordinateRoles (w : GeneratorWorkspace extra) : CoordinateWorkspace (extra+20) := generatorCoordinateSelection.trans w
def GeneratorWorkspace.oneHotRoles (w : GeneratorWorkspace extra) : PolynomialWorkspace (extra+26) := generatorOneHotSelection.trans w

def generatorScratch : List (Fin 32) := [6,7,8,9,10,11,12,13,14,15,16,18,19,20,27,31]

theorem generatorScratch_output (r : Fin 32) (member : r ∈ generatorScratch) : r ≠ 5 := by
  simp only [generatorScratch,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem generatorScratch_emit (w : GeneratorWorkspace extra) (store : Fin (extra+32) → List Bool)
    (empty : ∀ i ∈ generatorScratch, store (w i)=[]) (payload : List Bool) :
    ∀ i ∈ generatorScratch, (Function.update store (w 5) payload) (w i)=[] := by
  intro i hi
  simpa [w.injective.eq_iff,generatorScratch_output i hi] using empty i hi

def formulaBodyBound (program : Machine.Program) (time width capacity : Nat) :=
  5*time+6+finalClauseBound program time width+transitionsBound program time width+
    initialRowBound program width capacity+
    ((time+1)*width)*((oneHotBodyCoefficient (Cellular.alphabet program))*((time+1)*width+1)^2+2)+1

end Counting.External.CookLevin.StackGenerator
