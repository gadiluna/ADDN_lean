import Counting.ExternalSATLiteral
import Counting.StackEncodingListReadHeader

namespace Counting.External.SATVerification
open StackMachine.EncodingPrograms

def headerPositions : Fin 3 → (Fin 17 ↪ Fin 32)
  | 0 => ⟨![0,1,2,18,23,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
  | 1 => ⟨![0,1,2,18,24,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
  | 2 => ⟨![0,1,2,18,25,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩

def satHeaderRoles (extra : Nat) (w : SATWorkspace extra) (which : Fin 3) : FullListWorkspace (extra+15) :=
  (headerPositions which).trans w

def clauseScratch : List (Fin 32) := [2,3,4,5,6,9,10,11,12,13,14,18,19,20,21,22,24,26,28]

theorem literalScratch_subset (i : Fin 32) (member : i∈literalScratch) : i∈clauseScratch := by
  simp only [literalScratch,clauseScratch,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
  tauto

end Counting.External.SATVerification
