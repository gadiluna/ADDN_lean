import Counting.StackAuditDescendantCompleteInput
import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRelabel
import Counting.StackRoutineLists

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def completeNodeRoles : Fin 17 ↪ Fin 48 :=
  ⟨![17,1,41,0,2,3,4,5,6,7,8,9,10,11,12,13,14],by decide⟩

def completeNodeParser : VerifiedParser 46 17 1 41 (List Executable.Node) (Encoding.list Encoding.node) :=
  DagParser.nodes.relabel completeNodeRoles

abbrev readCompleteNodes : Routine 46 := sequence (pushBit 1 true)
  (sequence completeNodeParser.routine (sequence (clear 17)
    (sequence (clear 1) (ofProgram (ListPrograms.reverseProgram 46 41 46)))))

def completeNodesFile (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) : Store 46 :=
  Function.update (completeInputFile [] anchor.bits last.bits []
    ((Encoding.array Encoding.natural).encode weights)) 46 ((Encoding.array Encoding.node).encode vista.nodes)

/-- Extract the complete serialized node array by a verified parser, paying
for its copy and erasing the unused bottom field. No graph validity is needed. -/
theorem readCompleteNodes_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) :
    ∃ time ≤ 3900*((Encoding.vista.encode vista).length+1)^4,
      Executes readCompleteNodes
        (completeInputFile [] anchor.bits last.bits (Encoding.vista.encode vista)
          ((Encoding.array Encoding.natural).encode weights)) time
        (completeNodesFile vista weights anchor last) := by
  let initial:=completeInputFile [] anchor.bits last.bits (Encoding.vista.encode vista)
    ((Encoding.array Encoding.natural).encode weights)
  have a:=pushBit_executes (1:Fin 48) true initial
  have vacant : initial 1=[] := by simp [initial,completeInputFile]
  rw [vacant] at a
  let flagged:=Function.update initial 1 [true]
  have work (r:Fin 48) (member:r∈completeNodeParser.work) : flagged r=[] := by
    change r∈DagParser.nodes.work.map completeNodeRoles at member
    obtain ⟨i,inside,rfl⟩:=Finset.mem_map.mp member
    obtain ⟨n0,n1,n2⟩:=DagParser.nodes.separate i inside
    fin_cases i <;> simp_all [flagged,initial,completeInputFile,completeNodeRoles]
  obtain ⟨parseTime,parseBound,b⟩:=completeNodeParser.executes flagged true []
    (by simp [flagged]) work
  have source : flagged 17=(Encoding.list Encoding.node).encode vista.nodes.toList++
      Encoding.natural.encode vista.bottom := by simp [flagged,initial,completeInputFile];rfl
  have effect : completeNodeParser.effect (flagged 17)=
      ⟨Encoding.natural.encode vista.bottom,(Encoding.array Encoding.node).encode vista.nodes,true⟩ := by
    rw [source]
    exact DagParser.nodes.roundtrip vista.nodes.toList (Encoding.natural.encode vista.bottom)
  rw [effect] at b
  let parsed:=parseStore 17 1 41 flagged true []
    ⟨Encoding.natural.encode vista.bottom,(Encoding.array Encoding.node).encode vista.nodes,true⟩
  have c:=clear_executes (17:Fin 48) parsed
  have bottom : parsed 17=Encoding.natural.encode vista.bottom := by simp [parsed,parseStore]
  rw [bottom] at c
  let noBottom:=Function.update parsed 17 []
  have d:=clear_executes (1:Fin 48) noBottom
  have status : noBottom 1=[true] := by simp [noBottom,parsed,parseStore]
  rw [status,List.length_singleton] at d
  let cleared:=Function.update noBottom 1 []
  have e:=reverse_executes 46 (41:Fin 48) 46 (by decide) cleared
  have nodes : cleared 41=((Encoding.array Encoding.node).encode vista.nodes).reverse := by
    simp [cleared,noBottom,parsed,parseStore,flagged,initial,completeInputFile]
  have target : cleared 46=[] := by
    simp [cleared,noBottom,parsed,parseStore,flagged,initial,completeInputFile]
  rw [nodes,target,List.length_reverse,List.reverse_reverse,List.append_nil] at e
  have final : Function.update (Function.update cleared 41 []) 46
      ((Encoding.array Encoding.node).encode vista.nodes)=completeNodesFile vista weights anchor last := by
    funext r
    fin_cases r <;> simp [cleared,noBottom,parsed,parseStore,flagged,initial,completeInputFile,completeNodesFile]
  rw [final] at e
  have parsedSize : flagged 17=Encoding.vista.encode vista := by simp [flagged,initial,completeInputFile]
  rw [parsedSize] at parseBound
  change parseTime≤3849*((Encoding.vista.encode vista).length+1)^4 at parseBound
  have split : (Encoding.vista.encode vista).length=
      ((Encoding.array Encoding.node).encode vista.nodes).length+
        (Encoding.natural.encode vista.bottom).length := by
    change (((Encoding.array Encoding.node).encode vista.nodes)++
      Encoding.natural.encode vista.bottom).length=_
    exact List.length_append
  have linear : (Encoding.vista.encode vista).length+1≤((Encoding.vista.encode vista).length+1)^4:=
    Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  change 1+1+(parseTime+1+((Encoding.natural.encode vista.bottom).length+1+1+
    (2+1+(2*((Encoding.array Encoding.node).encode vista.nodes).length+1))))≤
      3900*((Encoding.vista.encode vista).length+1)^4
  omega

end Counting.StackMachine.AuditDescendant
