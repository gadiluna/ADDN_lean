import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRead

/-! Concrete indexed access to canonical node sequences. Register 8 contains
the unary index and is consumed; register 0 retains the suffix after the
selected node; register 2 receives its reversed canonical serialization.
The routine makes no claims about graph validity or a separate list header. -/
namespace Counting.StackMachine.EncodingPrograms.DagParser
open Routine
set_option backward.isDefEq.respectTransparency false

def nodeRead : Routine 15 := node.read 8

def nodeReadEffect (index : Nat) (input : List Bool) : ParseEffect :=
  readEffect node.effect index input

theorem nodeRead_executes (store : Store 15) (accepted : Bool) (tail : List Bool)
    (statusEq : store 1=accepted::tail) (workEmpty : ∀ r∈node.work,store r=[])
    (outputEmpty : store 2=[]) :
    ∃ time ≤ (2*(store 8).length+1)*2029*((store 0).length+1)^3+2*(store 8).length+4,
      Executes nodeRead store time
        (parseStore 0 1 2 (Function.update store 8 []) accepted tail
          (nodeReadEffect (store 8).length (store 0))) := by
  obtain ⟨time,bounded,executed⟩:=node.read_executes (by decide) (by decide) (by decide)
    8 (by decide) (by decide) (by decide) (by decide) (store 8) store accepted tail
    statusEq workEmpty outputEmpty rfl (store 0).length (le_refl _)
  refine ⟨time,?_,executed⟩
  change time≤(store 8).length*(2*(2029*((store 0).length+1)^3)+2)+
    2029*((store 0).length+1)^3+4 at bounded
  nlinarith

theorem nodeRead_accepts_iff (index : Nat) (input : List Bool) :
    (nodeReadEffect index input).accepted=true ↔
      ∃ before : List Executable.Node, ∃ value suffix, before.length=index ∧
        Encoding.sequence Encoding.node before++Encoding.node.encode value++suffix=input :=
  node.read_accepts_iff index input

theorem nodeRead_roundtrip (before : List Executable.Node) (value : Executable.Node)
    (suffix : List Bool) :
    nodeReadEffect before.length
      (Encoding.sequence Encoding.node before++Encoding.node.encode value++suffix)=
      ⟨suffix,Encoding.node.encode value,true⟩ :=
  node.read_roundtrip before value suffix

theorem nodeRead_get (values : List Executable.Node) (index : Fin values.length)
    (suffix : List Bool) :
    nodeReadEffect index.val (Encoding.sequence Encoding.node values++suffix)=
      ⟨Encoding.sequence Encoding.node (values.drop (index.val+1))++suffix,
        Encoding.node.encode values[index],true⟩ :=
  node.read_get values index suffix

end Counting.StackMachine.EncodingPrograms.DagParser
