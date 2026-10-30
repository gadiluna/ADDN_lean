import Counting.ExternalMatchingClauseLoop
import Counting.ExternalMatchingVariableOuter
import Counting.ExternalMatchingDimensions
import Counting.ExternalCNFHeaders

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

abbrev GeneratorWorkspace (extra : Nat) := Fin 64 ↪ Fin (extra+64)
def literalPositions : Fin 48 ↪ Fin 64 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 64=>i.val) h)⟩
def GeneratorWorkspace.literal (w : GeneratorWorkspace extra) : LiteralWorkspace (extra+16) := literalPositions.trans w
def generatorDimensionPositions : Fin 12 ↪ Fin 64 := ⟨![17,25,32,33,48,49,50,52,53,54,55,56],by decide⟩
def GeneratorWorkspace.dimensions (w : GeneratorWorkspace extra) : MatchingDimensions.Workspace (extra+52) := generatorDimensionPositions.trans w
def generatorVariablePositions : Fin 16 ↪ Fin 64 := ⟨![52,53,54,40,41,42,36,43,44,45,46,47,55,56,57,58],by decide⟩
def GeneratorWorkspace.variable (w : GeneratorWorkspace extra) : VariableOuterWorkspace (extra+48) := generatorVariablePositions.trans w
def generatorCompletionPositions : Fin 15 ↪ Fin 64 := ⟨![52,53,54,40,41,42,36,43,44,45,46,47,55,48,58],by decide⟩
def GeneratorWorkspace.completion (w : GeneratorWorkspace extra) : RowWorkspace (extra+49) := generatorCompletionPositions.trans w
def generatorTablePositions : Fin 17 ↪ Fin 64 := ⟨![0,1,2,18,52,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩
def GeneratorWorkspace.table (w : GeneratorWorkspace extra) : FullListWorkspace (extra+47) := generatorTablePositions.trans w
def generatorHeaderPositions : Fin 6 ↪ Fin 64 := ⟨![48,50,1,18,19,59],by decide⟩
def GeneratorWorkspace.headers (w : GeneratorWorkspace extra) : CNFMachine.HeaderWorkspace (extra+58) := generatorHeaderPositions.trans w

def generatorScratch : List (Fin 64) := (List.finRange 64).filter (fun i=>i≠0 ∧ i≠1 ∧ i≠17 ∧ i≠25 ∧ i≠31 ∧ i≠51)

end Counting.External.MatchingMachine
