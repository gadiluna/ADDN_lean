import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists
import Counting.StackNaturalPayloadRead

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The canonical component reader shares the full verifier's register file.
It consumes register70, accumulates status in85, and uses71 only while
reversing the parser's emitted code. Other persistent registers are untouched. -/
def componentRoles : Fin 17 ↪ Fin 100 :=
  ⟨![70,85,71,0,1,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def readComponent {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (target : Fin 100) : Routine 98 :=
  sequence (mapRegisters componentRoles parser.routine)
    (ofProgram (ListPrograms.reverseProgram 98 71 target))

/-- Charged extraction of a complete canonical encoded component. This
contract is used only after the total input parser has established its
canonical form; it does not assert acceptance of arbitrary malformed data. -/
theorem readComponent_executes {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (target : Fin 100)
    (targetSource : target≠70) (targetTemporary : target≠71)
    (store : Store 98) (value : α) (suffix : List Bool)
    (accepted : Bool) (tail : List Bool)
    (input : store 70=codec.encode value++suffix) (status : store 85=accepted::tail)
    (temporary : store 71=[]) (output : store target=[])
    (work : ∀i:Fin 17,i≠0 → i≠1 → i≠2 → store (componentRoles i)=[]) :
    ∃ time ≤ Complexity.polynomial parser.coefficient parser.exponent (store 70).length+
        2*(codec.encode value).length+2,
      Executes (readComponent parser target) store time
        (Function.update (Function.update store 70 suffix) target (codec.encode value)) := by
  let relocated := parser.relabel componentRoles
  have empty (r : Fin 100) (member : r∈relocated.work) : store r=[] := by
    change r∈parser.work.map componentRoles at member
    obtain ⟨i,inWork,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨a,b,c⟩ := parser.separate i inWork
    exact work i a b c
  obtain ⟨time,bound,parsing⟩ := relocated.executes store accepted tail status empty
  change time ≤ Complexity.polynomial parser.coefficient parser.exponent (store 70).length at bound
  change Executes (mapRegisters componentRoles parser.routine) store time
    (parseStore (70:Fin 100) 85 71 store accepted tail (parser.effect (store 70))) at parsing
  rw [input,parser.roundtrip] at parsing
  let parsed := Function.update (Function.update store 70 suffix) 71 (codec.encode value).reverse
  have parsedStore : parseStore (70:Fin 100) 85 71 store accepted tail
      ⟨suffix,codec.encode value,true⟩=parsed := by
    funext r
    by_cases a:r=70 <;> by_cases b:r=85 <;> by_cases c:r=71 <;>
      simp_all [parseStore,parsed]
  rw [parsedStore] at parsing
  have reversing := reverse_executes 98 (71:Fin 100) target (Ne.symm targetTemporary) parsed
  have sourceAt : parsed 71=(codec.encode value).reverse := by simp [parsed]
  have targetAt : parsed target=[] := by simp [parsed,targetSource,targetTemporary,output]
  rw [sourceAt,targetAt,List.reverse_reverse,List.append_nil,List.length_reverse] at reversing
  have final : Function.update (Function.update parsed 71 []) target (codec.encode value)=
      Function.update (Function.update store 70 suffix) target (codec.encode value) := by
    funext r
    by_cases a:r=target <;> by_cases b:r=71 <;> by_cases c:r=70 <;>
      simp_all [parsed]
  rw [final] at reversing
  exact ⟨_,by omega,
    parsing.sequence reversing⟩

end Counting.StackMachine.RealizabilityCheck
