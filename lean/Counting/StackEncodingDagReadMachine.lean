import Counting.StackEncodingDagRead
import Counting.StackCompilerComplete

/-! A concrete clean-output Turing-machine adapter for node access. The
input is a framed unary index followed by a sequence of node encodings.
The output is the selected parser's code followed by its acceptance bit.
This format deliberately does not pretend to validate an enclosing list
header or the graph structure of a node. -/
namespace Counting.StackMachine.EncodingPrograms.DagParser
open Routine
set_option backward.isDefEq.respectTransparency false

def nodeReadMachineRoutine : Routine 15 :=
  sequence (ofProgram (flaggedProgram 13 0 8 3 1))
    (sequence nodeRead (ofProgram (ListPrograms.reverseProgram 15 2 1)))

def nodeReadMachineProgram : Program := nodeReadMachineRoutine.program

def nodeReadOutput (input : List Bool) : List Bool :=
  let result:=nodeReadEffect (unframePayload input).length (unframeSuffix input)
  result.code++[(Encoding.unframe input).isSome && result.accepted]

theorem nodeReadOutput_roundtrip (index : List Bool) (before : List Executable.Node)
    (value : Executable.Node) (suffix : List Bool) (length : index.length=before.length) :
    nodeReadOutput (Encoding.frame index++Encoding.sequence Encoding.node before++
      Encoding.node.encode value++suffix)=Encoding.node.encode value++[true] := by
  have parsed : Encoding.unframe (Encoding.frame index++
      (Encoding.sequence Encoding.node before++Encoding.node.encode value++suffix))=
      some (index,Encoding.sequence Encoding.node before++Encoding.node.encode value++suffix) :=
    Encoding.unframe_frame _ _
  simp only [List.append_assoc] at parsed ⊢
  simp only [nodeReadOutput,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some,
    Option.isSome_some,length]
  have access:=nodeRead_roundtrip before value suffix
  simp only [List.append_assoc] at access
  rw [access]
  rfl

theorem nodeRead_computes : ComputesIn nodeReadMachineProgram nodeReadOutput
    (Complexity.polynomial 6100 4) := by
  intro input
  let start : Store 15 := fun r => if r=0 then input else []
  obtain ⟨frameTime,frameBound,frameRun⟩:=flagged_executes 13 0 8 3 1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) start (by simp [start])
  rw [flagged_result_updates 13 0 8 3 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) start (by simp [start])] at frameRun
  let framed : Store 15 := Function.update
    (Function.update (Function.update start 0 (unframeSuffix input)) 8 (unframePayload input)) 1
    [(Encoding.unframe input).isSome]
  have frameAs : Executes (ofProgram (flaggedProgram 13 0 8 3 1)) start frameTime framed := by
    simpa only [start,ite_true,show (8:Fin 17)≠0 by decide,show (1:Fin 17)≠0 by decide,
      if_false,List.append_nil] using frameRun
  have source : framed 0=unframeSuffix input := by simp [framed]
  have counter : framed 8=unframePayload input := by simp [framed]
  have status : framed 1=(Encoding.unframe input).isSome::[] := by simp [framed]
  have output : framed 2=[] := by simp [framed,start]
  have work (r : Fin 17) (member : r∈node.work) : framed r=[] := by
    obtain ⟨r0,r1,_⟩:=node.separate r member
    have r8 : r≠8 := by intro same; subst r; exact (by decide : (8:Fin 17)∉node.work) member
    simp [framed,start,r0,r1,r8]
  obtain ⟨readTime,readBound,readRun⟩:=nodeRead_executes framed (Encoding.unframe input).isSome []
    status work output
  rw [source,counter] at readBound readRun
  let effect:=nodeReadEffect (unframePayload input).length (unframeSuffix input)
  let readStore:=parseStore 0 1 2 (Function.update framed 8 [])
    (Encoding.unframe input).isSome [] effect
  have readOutput : readStore 2=effect.code.reverse := by simp [readStore,parseStore,framed,start]
  have readStatus : readStore 1=[(Encoding.unframe input).isSome && effect.accepted] := by
    simp [readStore,parseStore]
  have reversing:=reverse_executes 15 2 1 (by decide) readStore
  rw [readOutput,readStatus,List.length_reverse,List.reverse_reverse] at reversing
  have composed:=frameAs.sequence (readRun.sequence reversing)
  obtain ⟨finish,ran,halted,result⟩:=composed
  refine ⟨frameTime+1+(readTime+1+(2*effect.code.length+1)),finish,?_,⟨ran,halted⟩,?_⟩
  · have indexBound:=unframe_payload_length input
    have suffixBound:=unframe_suffix_length input
    have codeBound:=node.read_code_le (unframePayload input).length (unframeSuffix input)
    change effect.code.length≤2029*((unframeSuffix input).length+1)^3 at codeBound
    have power : ((unframeSuffix input).length+1)^3 ≤ (input.length+1)^3 := by gcongr
    have selectedBound : effect.code.length≤2029*(input.length+1)^3 :=
      codeBound.trans (Nat.mul_le_mul_left 2029 power)
    have reading : readTime≤(2*input.length+1)*2029*(input.length+1)^3+2*input.length+4 := by
      apply readBound.trans
      gcongr
    change frameTime≤3*input.length+4 at frameBound
    have positive : 1≤(input.length+1)^3 := Nat.one_le_pow _ _ (by omega)
    have linear : input.length+1≤(input.length+1)^4 := Nat.le_self_pow (by decide) _
    unfold Complexity.polynomial
    rw [show (input.length+1)^4=(input.length+1)^3*(input.length+1) by ring]
    nlinarith
  · rw [result]
    rfl

theorem nodeRead_computesCleanIn : Complexity.ComputesCleanIn
    (Compiler.compile nodeReadMachineProgram) nodeReadOutput
    (Complexity.polynomial 749088000 10) := by
  exact Compiler.computesCleanIn_polynomial 6100 4 nodeRead_computes

end Counting.StackMachine.EncodingPrograms.DagParser
