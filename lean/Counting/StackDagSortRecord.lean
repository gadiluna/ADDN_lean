import Counting.StackDagReadForward
import Counting.StackEncodingParserProduct

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev Record := Nat×Executable.Node

def recordCodec : Encoding.Codec Record := Encoding.product Encoding.natural Encoding.node

def recordParser : VerifiedParser 15 0 1 2 Record recordCodec :=
  DagParser.natural.product (by decide) (by decide) (by decide) DagParser.node

def wideRecord : VerifiedParser 18 0 1 2 Record recordCodec := recordParser.relabel DagParser.nodeRoles

def readRecord : Routine 18 := sequence wideRecord.routine (ofProgram (ListPrograms.reverseProgram 18 2 17))

/-- The sort carries the original local index together with the remapped
signature. The physical reader preserves that complete record and suffix. -/
theorem readRecord_executes (store : Store 18) (record : Record) (suffix : List Bool)
    (accepted : Bool) (tail : List Bool)
    (source : store 0=recordCodec.encode record++suffix) (status : store 1=accepted::tail)
    (empty : ∀ r : Fin 20,2≤r.val → r.val≤17 → store r=[]) :
    ∃ time≤2100*((store 0).length+1)^3,
      Executes readRecord store time
        (Function.update (Function.update store 0 suffix) 17 (recordCodec.encode record)) := by
  have work (r : Fin 20) (member : r∈wideRecord.work) : store r=[] := by
    change r∈recordParser.work.map DagParser.nodeRoles at member
    obtain ⟨small,inside,rfl⟩ := Finset.mem_map.mp member
    obtain ⟨n0,n1,_⟩ := recordParser.separate small inside
    apply empty
    · have zero : small.val≠0 := by intro equal;apply n0;exact Fin.ext equal
      have one : small.val≠1 := by intro equal;apply n1;exact Fin.ext equal
      change 2 ≤ small.val
      omega
    · change small.val≤17
      have := small.isLt
      omega
  obtain ⟨time,bound,ran⟩ := wideRecord.executes store accepted tail status work
  rw [source,wideRecord.roundtrip] at ran
  let parsed := Function.update (Function.update store 0 suffix) 2 (recordCodec.encode record).reverse
  have parsedResult : parseStore 0 1 2 store accepted tail ⟨suffix,recordCodec.encode record,true⟩=parsed := by
    funext r
    by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r2 : r=2 <;>
      simp_all [parseStore,parsed]
  rw [parsedResult] at ran
  have reversed := reverse_executes 18 (2:Fin 20) 17 (by decide) parsed
  have codeAt : parsed 2=(recordCodec.encode record).reverse := by simp [parsed]
  have outputAt : parsed 17=[] := by simp [parsed,empty]
  rw [codeAt,outputAt,List.length_reverse,List.reverse_reverse,List.append_nil] at reversed
  have final : Function.update (Function.update parsed 2 []) 17 (recordCodec.encode record)=
      Function.update (Function.update store 0 suffix) 17 (recordCodec.encode record) := by
    funext r
    by_cases r0 : r=0 <;> by_cases r2 : r=2 <;> by_cases r17 : r=17 <;>
      simp [parsed,r0,r2,r17,empty]
  rw [final] at reversed
  refine ⟨time+1+(2*(recordCodec.encode record).length+1),?_,ran.sequence reversed⟩
  change time≤2070*((store 0).length+1)^3 at bound
  have size : (recordCodec.encode record).length≤(store 0).length := by rw [source,List.length_append];omega
  have linear : (store 0).length+1≤((store 0).length+1)^3 := Nat.le_self_pow (by decide) _
  omega

end Counting.StackMachine.DagUpdate.Sort
