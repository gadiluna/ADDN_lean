import Counting.StackEncodingDagRead
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

/-! A node reader with persistent source and unary index. Registers 17 and
18 are preserved, register 19 receives the selected forward serialization,
and register 1 combines the previous status with the parser result. All
other registers are restored. The 17-register parser is relocated by a
proved instruction rewrite, not by a free register-file operation. -/
namespace Counting.StackMachine.EncodingPrograms.DagParser
open Routine
set_option backward.isDefEq.respectTransparency false

def nodeRoles : Fin 17 ↪ Fin 20 where
  toFun r:=⟨r.val,by have:=r.isLt;omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 20=>r.val) equal

def wideNode : VerifiedParser 18 0 1 2 Executable.Node Encoding.node := node.relabel nodeRoles

def preservingNodeRead : Routine 18 :=
  sequence (ofProgram (ListPrograms.copyProgram 17 17 0 3))
    (sequence (ofProgram (ListPrograms.copyProgram 17 18 8 3))
      (sequence (wideNode.read 8)
        (sequence (clear 0) (ofProgram (ListPrograms.reverseProgram 18 2 19)))))

def preservingNodeStore (store : Store 18) (accepted : Bool) (tail : List Bool)
    (effect : ParseEffect) : Store 18 :=
  Function.update (Function.update store 1 ((accepted && effect.accepted)::tail)) 19 effect.code

theorem preservingNodeRead_executes (store : Store 18) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail)
    (workspaceEmpty : ∀ r : Fin 17,r≠1 → store (nodeRoles r)=[])
    (outputEmpty : store 19=[]) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+14,
      Executes preservingNodeRead store time
        (preservingNodeStore store accepted tail (nodeReadEffect (store 18).length (store 17))) := by
  have empty0 : store 0=[]:=workspaceEmpty 0 (by decide)
  have empty2 : store 2=[]:=workspaceEmpty 2 (by decide)
  have empty3 : store 3=[]:=workspaceEmpty 3 (by decide)
  have empty8 : store 8=[]:=workspaceEmpty 8 (by decide)
  have copySource:=copy_executes 17 17 0 3 (by decide) (by decide) (by decide) store empty3
  rw [empty0,List.append_nil] at copySource
  let sourceCopied:=Function.update store 0 (store 17)
  have copyIndex:=copy_executes 17 18 8 3 (by decide) (by decide) (by decide) sourceCopied
    (by simp [sourceCopied,empty3])
  have indexSource : sourceCopied 18=store 18:=by simp [sourceCopied]
  have indexTarget : sourceCopied 8=[]:=by simp [sourceCopied,empty8]
  rw [indexSource,indexTarget,List.append_nil] at copyIndex
  let copied:=Function.update sourceCopied 8 (store 18)
  have copiedSource : copied 0=store 17:=by simp [copied,sourceCopied]
  have copiedIndex : copied 8=store 18:=by simp [copied]
  have copiedStatus : copied 1=accepted::tail:=by simp [copied,sourceCopied,statusEq]
  have copiedOutput : copied 2=[]:=by simp [copied,sourceCopied,empty2]
  have work (r : Fin 20) (member : r∈wideNode.work) : copied r=[] := by
    change r∈node.work.map nodeRoles at member
    obtain ⟨i,inside,rfl⟩:=Finset.mem_map.mp member
    obtain ⟨i0,i1,_⟩:=node.separate i inside
    have i8 : i≠8:=by intro h;subst i;exact (by decide : (8:Fin 17)∉node.work) inside
    have r0 : nodeRoles i≠0:=by intro h;apply i0;exact nodeRoles.injective h
    have r8 : nodeRoles i≠8:=by intro h;apply i8;exact nodeRoles.injective h
    simp only [copied,sourceCopied,Function.update_of_ne r0,Function.update_of_ne r8]
    exact workspaceEmpty i i1
  obtain ⟨readTime,readBound,readRun⟩:=wideNode.read_executes (by decide) (by decide) (by decide)
    8 (by decide) (by decide) (by decide) (by decide) (store 18) copied accepted tail copiedStatus
    work copiedOutput copiedIndex (store 17).length (by rw [copiedSource])
  rw [copiedSource] at readRun
  let effect:=nodeReadEffect (store 18).length (store 17)
  let parsed:=parseStore 0 1 2 (Function.update copied 8 []) accepted tail effect
  have parsedSource : parsed 0=effect.suffix:=by simp [parsed,parseStore]
  have parsedOutput : parsed 2=effect.code.reverse:=by
    simp [parsed,parseStore,copied,sourceCopied,empty2]
  have parsedTarget : parsed 19=[]:=by simp [parsed,parseStore,copied,sourceCopied,outputEmpty]
  have clearing:=clear_executes 0 parsed
  rw [parsedSource] at clearing
  have reversing:=reverse_executes 18 2 19 (by decide) (Function.update parsed 0 [])
  have reverseSource : Function.update parsed 0 [] 2=effect.code.reverse:=by simp [parsedOutput]
  have reverseTarget : Function.update parsed 0 [] 19=[]:=by simp [parsedTarget]
  rw [reverseSource,reverseTarget,List.length_reverse,List.reverse_reverse,List.append_nil] at reversing
  have composed:=copySource.sequence (copyIndex.sequence (readRun.sequence (clearing.sequence reversing)))
  have resultEq : Function.update (Function.update (Function.update parsed 0 []) 2 []) 19 effect.code=
      preservingNodeStore store accepted tail effect := by
    funext r
    by_cases r0 : r=0
    · subst r; simp [preservingNodeStore,empty0]
    · by_cases r1 : r=1
      · subst r; simp [parsed,parseStore,preservingNodeStore]
      · by_cases r2 : r=2
        · subst r; simp [preservingNodeStore,empty2]
        · by_cases r8 : r=8
          · subst r; simp [parsed,parseStore,preservingNodeStore,empty8]
          · by_cases r19 : r=19
            · subst r; simp [preservingNodeStore]
            · simp [parsed,parseStore,preservingNodeStore,copied,sourceCopied,r0,r1,r2,r8,r19]
  rw [resultEq] at composed
  refine ⟨_,?_,composed⟩
  have suffixBound:=node.read_suffix_le (store 18).length (store 17)
  have codeBound:=node.read_code_le (store 18).length (store 17)
  change effect.code.length≤2029*((store 17).length+1)^3 at codeBound
  change readTime≤(store 18).length*(2*(2029*((store 17).length+1)^3)+2)+
    2029*((store 17).length+1)^3+4 at readBound
  change effect.suffix.length≤(store 17).length at suffixBound
  nlinarith

theorem preservingNodeRead_get (store : Store 18) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail)
    (workspaceEmpty : ∀ r : Fin 17,r≠1 → store (nodeRoles r)=[])
    (outputEmpty : store 19=[]) (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) (sourceEq : store 17=Encoding.sequence Encoding.node values++suffix)
    (indexEq : (store 18).length=index.val) :
    ∃ time ≤ (2*(store 18).length+3)*2029*((store 17).length+1)^3+
        6*(store 17).length+7*(store 18).length+14,
      Executes preservingNodeRead store time (Function.update store 19 (Encoding.node.encode values[index])) := by
  obtain ⟨time,bounded,executed⟩:=preservingNodeRead_executes store accepted tail statusEq workspaceEmpty outputEmpty
  rw [sourceEq,indexEq,nodeRead_get] at executed
  have same : preservingNodeStore store accepted tail
      ⟨Encoding.sequence Encoding.node (values.drop (index.val+1))++suffix,
        Encoding.node.encode values[index],true⟩=
      Function.update store 19 (Encoding.node.encode values[index]) := by
    simp only [preservingNodeStore,Bool.and_true,←statusEq,Function.update_eq_self]
  rw [same] at executed
  exact ⟨time,bounded,executed⟩

end Counting.StackMachine.EncodingPrograms.DagParser
