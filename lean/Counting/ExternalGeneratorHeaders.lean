import Counting.ExternalGeneratorWorkspace
import Counting.StackEmitSyntax

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def generatorClauseHeaderSelection : Fin 5 ↪ Fin 32 := ⟨![23,5,18,19,31],by decide⟩
def generatorVariableHeaderSelection : Fin 5 ↪ Fin 32 := ⟨![22,5,18,19,31],by decide⟩
def GeneratorWorkspace.clauseHeaderRoles (w : GeneratorWorkspace extra) : PowerWorkspace (extra+27) := generatorClauseHeaderSelection.trans w
def GeneratorWorkspace.variableHeaderRoles (w : GeneratorWorkspace extra) : PowerWorkspace (extra+27) := generatorVariableHeaderSelection.trans w

def formulaHeadersRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+30) :=
  sequence (emitNatural (extra+27) w.clauseHeaderRoles) (emitVariableTable (extra+27) w.variableHeaderRoles)

def formulaHeadersBound (variableCount clauseCount : Nat) := 20*(clauseCount+1)^2+1+28*(variableCount+1)^2

theorem formulaHeadersRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra) (variableCount clauseCount : Nat)
    (store : Fin (extra+32) → List Bool)
    (variablesValue : store (w 22)=List.replicate variableCount true) (clausesLength : (store (w 23)).length=clauseCount)
    (counterEmpty : store (w 18)=[]) (binaryEmpty : store (w 19)=[]) (workEmpty : store (w 31)=[]) :
    ∃ transitions ≤ formulaHeadersBound variableCount clauseCount,
      Executes (formulaHeadersRoutine extra w) store transitions
        (Function.update store (w 5)
          ((Encoding.list Encoding.boolean).encode (List.replicate variableCount true)++
            Encoding.natural.encode clauseCount++store (w 5))) := by
  obtain ⟨clauseTime,clauseBound,clauseRun⟩ := emitNatural_executes (extra+27) w.clauseHeaderRoles store
    (by simpa [GeneratorWorkspace.clauseHeaderRoles,generatorClauseHeaderSelection] using counterEmpty)
    (by simpa [GeneratorWorkspace.clauseHeaderRoles,generatorClauseHeaderSelection] using binaryEmpty)
    (by simpa [GeneratorWorkspace.clauseHeaderRoles,generatorClauseHeaderSelection] using workEmpty)
  have sourceLength : (store (w.clauseHeaderRoles 0)).length=clauseCount := clausesLength
  rw [sourceLength] at clauseBound clauseRun
  let middle := Function.update store (w 5) (Encoding.natural.encode clauseCount++store (w 5))
  have first : Executes (emitNatural (extra+27) w.clauseHeaderRoles) store clauseTime middle := by
    simpa [GeneratorWorkspace.clauseHeaderRoles,generatorClauseHeaderSelection,middle] using clauseRun
  obtain ⟨variableTime,variableBound,variableRun⟩ := emitVariableTable_executes (extra+27) w.variableHeaderRoles variableCount middle
    (by simp [GeneratorWorkspace.variableHeaderRoles,generatorVariableHeaderSelection,middle,w.injective.eq_iff,variablesValue])
    (by simp [GeneratorWorkspace.variableHeaderRoles,generatorVariableHeaderSelection,middle,w.injective.eq_iff,counterEmpty])
    (by simp [GeneratorWorkspace.variableHeaderRoles,generatorVariableHeaderSelection,middle,w.injective.eq_iff,binaryEmpty])
    (by simp [GeneratorWorkspace.variableHeaderRoles,generatorVariableHeaderSelection,middle,w.injective.eq_iff,workEmpty])
  have combined := first.sequence variableRun
  refine ⟨clauseTime+1+variableTime,by unfold formulaHeadersBound; omega,?_⟩
  simpa [formulaHeadersRoutine,GeneratorWorkspace.variableHeaderRoles,generatorVariableHeaderSelection,middle,List.append_assoc] using combined

end Counting.External.CookLevin.StackGenerator
