import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

namespace Counting.StackMachine.NetworkVista.Forward
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def parserRoles : Fin 17 ↪ Fin 20 where
  toFun i:=if i=0 then 17 else ⟨i.val,by have:=i.isLt;omega⟩
  inj':=by
    intro a b same
    by_cases a0:a=0 <;> by_cases b0:b=0
    · simp_all
    · subst a
      simp only [ite_true,if_neg b0] at same
      have value:=congrArg (fun r:Fin 20=>r.val) same
      change 17=b.val at value
      have:=b.isLt
      omega
    · subst b
      simp only [ite_true,if_neg a0] at same
      have value:=congrArg (fun r:Fin 20=>r.val) same
      change a.val=17 at value
      have:=a.isLt
      omega
    · simp only [if_neg a0,if_neg b0] at same
      exact Fin.ext (congrArg (fun r:Fin 20=>r.val) same)

variable {α:Type} {codec:Encoding.Codec α} (parser:VerifiedParser 15 0 1 2 α codec)

def wideParser : VerifiedParser 18 17 1 2 α codec := parser.relabel parserRoles

def parseForward : Routine 18 := sequence (wideParser parser).routine
  (ofProgram (ListPrograms.reverseProgram 18 2 19))

def forwardStore (store:Store 18) (accepted:Bool) (tail:List Bool) (effect:ParseEffect) : Store 18 :=
  Function.update (Function.update (Function.update store 17 effect.suffix)
    1 ((accepted && effect.accepted)::tail)) 19 effect.code

theorem parseForward_executes (store:Store 18) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r∈(wideParser parser).work,store r=[])
    (e2:store 2=[]) (e19:store 19=[]) :
    ∃time ≤ 3*Complexity.polynomial parser.coefficient parser.exponent (store 17).length+2,
      Executes (parseForward parser) store time
        (forwardStore store accepted tail (parser.effect (store 17))) := by
  obtain ⟨time,bound,run⟩:=(wideParser parser).executes store accepted tail status work
  let effect:=parser.effect (store 17)
  let parsed:=parseStore 17 1 2 store accepted tail effect
  have reversing:=reverse_executes 18 (2:Fin 20) 19 (by decide) parsed
  rw [show parsed 2=effect.code.reverse by simp [parsed,parseStore,e2],
    show parsed 19=[] by simp [parsed,parseStore,e19],List.append_nil,List.reverse_reverse,List.length_reverse] at reversing
  have final:Function.update (Function.update parsed 2 []) 19 effect.code=
      forwardStore store accepted tail effect:=by
    funext r
    by_cases n1:r=1 <;> by_cases n2:r=2 <;> by_cases n17:r=17 <;> by_cases n19:r=19 <;>
      simp [parsed,parseStore,forwardStore,n1,n2,n17,n19,e2]
  rw [final] at reversing
  have codeBound:=parser.code_le (store 17)
  change effect.code.length≤_ at codeBound
  change time≤Complexity.polynomial parser.coefficient parser.exponent (store 17).length at bound
  exact ⟨time+1+(2*effect.code.length+1),by omega,run.sequence reversing⟩

theorem parseForward_canonical (store:Store 18) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r∈(wideParser parser).work,store r=[])
    (e2:store 2=[]) (e19:store 19=[]) (value:α) (suffix:List Bool)
    (source:store 17=codec.encode value++suffix) :
    ∃time ≤ 3*Complexity.polynomial parser.coefficient parser.exponent (store 17).length+2,
      Executes (parseForward parser) store time
        (Function.update (Function.update store 17 suffix) 19 (codec.encode value)) := by
  obtain ⟨time,bound,run⟩:=parseForward_executes parser store accepted tail status work e2 e19
  rw [source,parser.roundtrip] at run
  refine ⟨time,bound,?_⟩
  simpa only [forwardStore,Bool.and_true,←status,
    Function.update_comm (by decide : (17:Fin 20)≠1),Function.update_eq_self] using run

end Counting.StackMachine.NetworkVista.Forward
