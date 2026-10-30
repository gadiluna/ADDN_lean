import Counting.StackEncodingParserRead
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

/-! A concrete preserving indexed reader for any of the 17-register
codec parsers. The parser runs on an actual copy of the serialized input;
the unary index is copied and consumed in register 20. This generic
operation is used by the offline network simulator to retrieve previous
views and matrix rows. -/
namespace Counting.StackMachine.NetworkVista.Reader
open EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

def parserRoles : Fin 17 ↪ Fin 21 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 21=>r.val) equal

variable {α : Type} {codec : Encoding.Codec α}
  (parser : VerifiedParser 15 0 1 2 α codec)

def wideParser : VerifiedParser 19 0 1 2 α codec := parser.relabel parserRoles

def preservingRead : Routine 19 :=
  sequence (ofProgram (ListPrograms.copyProgram 18 17 0 3))
    (sequence (ofProgram (ListPrograms.copyProgram 18 18 20 3))
      (sequence ((wideParser parser).read 20)
        (sequence (clear 0) (ofProgram (ListPrograms.reverseProgram 19 2 19)))))

def preservingStore (store : Store 19) (accepted : Bool) (tail : List Bool)
    (effect : ParseEffect) : Store 19 :=
  Function.update (Function.update store 1 ((accepted && effect.accepted)::tail)) 19 effect.code

theorem preservingRead_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail)
    (workspaceEmpty : ∀ r : Fin 17,r≠1 → store (parserRoles r)=[])
    (outputEmpty : store 19=[]) (scratchEmpty : store 20=[]) :
    ∃ time ≤ (2*(store 18).length+3)*(Complexity.polynomial parser.coefficient parser.exponent (store 17).length)+
        6*(store 17).length+7*(store 18).length+14,
      Executes (preservingRead parser) store time
        (preservingStore store accepted tail (readEffect parser.effect (store 18).length (store 17))) := by
  have empty0 : store 0=[]:=workspaceEmpty 0 (by decide)
  have empty2 : store 2=[]:=workspaceEmpty 2 (by decide)
  have empty3 : store 3=[]:=workspaceEmpty 3 (by decide)
  have empty20 : store 20=[]:=scratchEmpty
  have copySource:=copy_executes 18 17 0 3 (by decide) (by decide) (by decide) store empty3
  rw [empty0,List.append_nil] at copySource
  let sourceCopied:=Function.update store 0 (store 17)
  have copyIndex:=copy_executes 18 18 20 3 (by decide) (by decide) (by decide) sourceCopied
    (by simp [sourceCopied,empty3])
  have indexSource : sourceCopied 18=store 18:=by simp [sourceCopied]
  have indexTarget : sourceCopied 20=[]:=by simp [sourceCopied,empty20]
  rw [indexSource,indexTarget,List.append_nil] at copyIndex
  let copied:=Function.update sourceCopied 20 (store 18)
  have copiedSource : copied 0=store 17:=by simp [copied,sourceCopied]
  have copiedIndex : copied 20=store 18:=by simp [copied]
  have copiedStatus : copied 1=accepted::tail:=by simp [copied,sourceCopied,statusEq]
  have copiedOutput : copied 2=[]:=by simp [copied,sourceCopied,empty2]
  have work (r : Fin 21) (member : r∈(wideParser parser).work) : copied r=[] := by
    change r∈parser.work.map parserRoles at member
    obtain ⟨i,inside,rfl⟩:=Finset.mem_map.mp member
    obtain ⟨i0,i1,_⟩:=parser.separate i inside
    have r0 : parserRoles i≠0:=by intro h;apply i0;exact parserRoles.injective h
    have r20 : parserRoles i≠20:=by
      intro h
      have value:=congrArg (fun r:Fin 21=>r.val) h
      change i.val=20 at value
      have:=i.isLt
      omega
    simp only [copied,sourceCopied,Function.update_of_ne r0,Function.update_of_ne r20]
    exact workspaceEmpty i i1
  obtain ⟨readTime,readBound,readRun⟩:=(wideParser parser).read_executes (by decide) (by decide) (by decide)
    20 (by decide) (by decide) (by decide) (by
      intro present
      obtain ⟨i,_,same⟩:=Finset.mem_map.mp present
      have value:=congrArg (fun r:Fin 21=>r.val) same
      change i.val=20 at value
      have:=i.isLt
      omega) (store 18) copied accepted tail copiedStatus
    work copiedOutput copiedIndex (store 17).length (by rw [copiedSource])
  rw [copiedSource] at readRun
  let effect:=readEffect parser.effect (store 18).length (store 17)
  let parsed:=parseStore 0 1 2 (Function.update copied 20 []) accepted tail effect
  have parsedSource : parsed 0=effect.suffix:=by simp [parsed,parseStore]
  have parsedOutput : parsed 2=effect.code.reverse:=by
    simp [parsed,parseStore,copied,sourceCopied,empty2]
  have parsedTarget : parsed 19=[]:=by simp [parsed,parseStore,copied,sourceCopied,outputEmpty]
  have clearing:=clear_executes 0 parsed
  rw [parsedSource] at clearing
  have reversing:=reverse_executes 19 2 19 (by decide) (Function.update parsed 0 [])
  have reverseSource : Function.update parsed 0 [] 2=effect.code.reverse:=by simp [parsedOutput]
  have reverseTarget : Function.update parsed 0 [] 19=[]:=by simp [parsedTarget]
  rw [reverseSource,reverseTarget,List.length_reverse,List.reverse_reverse,List.append_nil] at reversing
  have composed:=copySource.sequence (copyIndex.sequence (readRun.sequence (clearing.sequence reversing)))
  have resultEq : Function.update (Function.update (Function.update parsed 0 []) 2 []) 19 effect.code=
      preservingStore store accepted tail effect := by
    funext r
    by_cases r0 : r=0
    · subst r; simp [preservingStore,empty0]
    · by_cases r1 : r=1
      · subst r; simp [parsed,parseStore,preservingStore]
      · by_cases r2 : r=2
        · subst r; simp [preservingStore,empty2]
        · by_cases r20 : r=20
          · subst r; simp [parsed,parseStore,preservingStore,empty20]
          · by_cases r19 : r=19
            · subst r; simp [preservingStore]
            · simp [parsed,parseStore,preservingStore,copied,sourceCopied,r0,r1,r2,r20,r19]
  rw [resultEq] at composed
  refine ⟨_,?_,composed⟩
  have suffixBound:=parser.read_suffix_le (store 18).length (store 17)
  have codeBound:=parser.read_code_le (store 18).length (store 17)
  change effect.code.length≤(Complexity.polynomial parser.coefficient parser.exponent (store 17).length) at codeBound
  change readTime≤(store 18).length*(2*((Complexity.polynomial parser.coefficient parser.exponent (store 17).length))+2)+
    (Complexity.polynomial parser.coefficient parser.exponent (store 17).length)+4 at readBound
  change effect.suffix.length≤(store 17).length at suffixBound
  nlinarith

theorem preservingRead_get (store : Store 19) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail)
    (workspaceEmpty : ∀ r : Fin 17,r≠1 → store (parserRoles r)=[])
    (outputEmpty : store 19=[]) (scratchEmpty : store 20=[]) (values : List α) (index : Fin values.length)
    (suffix : List Bool) (sourceEq : store 17=Encoding.sequence codec values++suffix)
    (indexEq : (store 18).length=index.val) :
    ∃ time ≤ (2*(store 18).length+3)*(Complexity.polynomial parser.coefficient parser.exponent (store 17).length)+
        6*(store 17).length+7*(store 18).length+14,
      Executes (preservingRead parser) store time (Function.update store 19 (codec.encode values[index])) := by
  obtain ⟨time,bounded,executed⟩:=preservingRead_executes parser store accepted tail statusEq workspaceEmpty outputEmpty scratchEmpty
  rw [sourceEq,indexEq,parser.read_get] at executed
  have same : preservingStore store accepted tail
      ⟨Encoding.sequence codec (values.drop (index.val+1))++suffix,
        codec.encode values[index],true⟩=
      Function.update store 19 (codec.encode values[index]) := by
    simp only [preservingStore,Bool.and_true,←statusEq,Function.update_eq_self]
  rw [same] at executed
  exact ⟨time,bounded,executed⟩

end Counting.StackMachine.NetworkVista.Reader
