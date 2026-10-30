import Counting.StackVistaMessageRead
import Counting.StackDagAddCountBounds

namespace Counting.StackMachine.DagUpdate.Receive
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def incomingRoles : AddWorkspace 76 :=
  ⟨![75,4,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],by decide⟩

def finishTail : Routine 94 := sequence (move 93 18 75 0)
  (sequence (clear 1) (sequence (clear 3) (sequence (clear 4) (clear 17))))

def finishedTail (store : Store 94) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update store 75 (store 18)) 18 []) 1 []) 3 []) 4 []) 17 []

theorem finishTail_executes (store : Store 94) (scratch : store 0=[]) (target : store 75=[]) :
    Executes finishTail store
      (6*(store 18).length+(store 1).length+(store 3).length+(store 4).length+(store 17).length+12)
      (finishedTail store) := by
  have moving := move_executes 93 (18:Fin 96) 75 0 (by decide) (by decide) (by decide) store scratch
  rw [target,List.append_nil] at moving
  let moved := Function.update (Function.update store 75 (store 18)) 18 []
  have c1 := clear_executes (1:Fin 96) moved
  have c3 := clear_executes (3:Fin 96) (Function.update moved 1 [])
  have c4 := clear_executes (4:Fin 96) (Function.update (Function.update moved 1 []) 3 [])
  have c17 := clear_executes (17:Fin 96)
    (Function.update (Function.update (Function.update moved 1 []) 3 []) 4 [])
  have run := moving.sequence (c1.sequence (c3.sequence (c4.sequence c17)))
  convert run using 1 <;> first | rfl | (simp [moved];omega)

def mergeTail : Routine 94 := sequence readTail
  (sequence readBottom (sequence (addCount 76 incomingRoles) finishTail))

def mergeTailBudget (mapping : Array Nat) (bottom count : Nat) (edges : List (Nat×Nat)) : Nat :=
  let index := mapping[bottom]?.getD 0
  let mapCode := (Encoding.array Encoding.natural).encode mapping
  let queryCode := Encoding.natural.encode bottom
  let output := (Encoding.list edgeCodec).encode (Executable.addCount index count edges)
  10*bottom.bits.length+5*count.bits.length+10+
    200*(mapCode.length+queryCode.length+1)^3+
    10000*(((Encoding.list edgeCodec).encode edges).length+index.bits.length+count.bits.length+1)^3+
    6*output.length+mapCode.length+queryCode.length+index.bits.length+count.bits.length+15

/-- One received bottom is looked up in its actual import map and its
binary multiplicity is added to the compact incoming list. The map and
scratch fields are consumed; the pool and all caller registers are preserved. -/
theorem mergeTail_executes (store : Store 94) (mapping : Array Nat) (bottom count : Nat)
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (source : store 70=Encoding.natural.encode bottom++Encoding.natural.encode count++suffix)
    (mapAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (edgesAt : store 75=(Encoding.list edgeCodec).encode edges)
    (empty : ∀ r : Fin 96,r.val≤34 → r≠1 → store r=[]) :
    ∃ time ≤ mergeTailBudget mapping bottom count edges,
      Executes mergeTail store time
        (Function.update (Function.update (Function.update store 70 suffix) 1 []) 75
          ((Encoding.list edgeCodec).encode
            (Executable.addCount (mapping[bottom]?.getD 0) count edges))) := by
  let index := mapping[bottom]?.getD 0
  let read := tailResult store bottom count suffix
  have reading := readTail_executes store bottom count suffix source (by
    intro r member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact empty _ (by decide) (by decide))
  have readEmpty (r : Fin 96) (lo : 4≤r.val) (hi : r.val≤15) : read r=[] := by
    have n3 : r≠3 := by intro eq;subst r;norm_num at lo
    have n17 : r≠17 := by intro eq;subst r;norm_num at hi
    have n70 : r≠70 := by intro eq;subst r;norm_num at hi
    have n1 : r≠1 := by intro eq;subst r;norm_num at lo
    simp [read,tailResult,n3,n17,n70,empty r (by omega) n1]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩ := readBottom_executes read mapping bottom
    (by simp [read,tailResult,mapAt]) (by simp [read,tailResult]) readEmpty
  let looked := Function.update read 4 index.bits
  obtain ⟨addTime,addBound,addRun⟩ := addCount_executes_polynomial 76 incomingRoles looked index count edges []
    (by simp [looked,read,tailResult,incomingRoles,edgesAt])
    (by simp [looked,incomingRoles]) (by simp [looked,read,tailResult,incomingRoles]) (by
      intro j n0 n1 n2
      fin_cases j <;> simp_all [looked,read,tailResult,incomingRoles])
  let output := (Encoding.list edgeCodec).encode (Executable.addCount index count edges)
  let added := Function.update (Function.update looked 75 []) 18 output
  have finish := finishTail_executes added
    (by simp [added,looked,read,tailResult,empty]) (by simp [added])
  have final : finishedTail added=
      Function.update (Function.update (Function.update store 70 suffix) 1 []) 75 output := by
    funext r
    by_cases r1 : r=1 <;> by_cases r3 : r=3 <;> by_cases r4 : r=4 <;>
      by_cases r17 : r=17 <;> by_cases r18 : r=18 <;> by_cases r70 : r=70 <;>
      by_cases r75 : r=75 <;>
      simp [finishedTail,added,looked,read,tailResult,r1,r3,r4,r17,r18,r70,r75,empty]
  rw [final] at finish
  have ran := reading.sequence (lookupRun.sequence (addRun.sequence finish))
  refine ⟨_,?_,ran⟩
  simp only [read,tailResult,Function.update_self,
    Function.update_of_ne (show (1:Fin 96)≠17 by decide),
    Function.update_of_ne (show (1:Fin 96)≠3 by decide),
    Function.update_of_ne (show (1:Fin 96)≠70 by decide),
    Function.update_of_ne (show (3:Fin 96)≠17 by decide),mapAt] at lookupBound
  have addInput : looked (incomingRoles 0)=(Encoding.list edgeCodec).encode edges := by
    simp [looked,read,tailResult,incomingRoles,edgesAt]
  have addQuery : looked (incomingRoles 1)=index.bits := by simp [looked,incomingRoles]
  have addCountAt : looked (incomingRoles 2)=count.bits := by simp [looked,read,tailResult,incomingRoles]
  rw [addInput,addQuery,addCountAt] at addBound
  dsimp only [mergeTailBudget,index,output]
  simp [added,looked,read,tailResult,mapAt,index,output]
  simp only [index,Encoding.natural_length] at lookupBound addBound
  omega

end Counting.StackMachine.DagUpdate.Receive
