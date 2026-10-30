import Counting.NetworkVistaArrayRead
import Counting.NetworkRecognitionParser
import Counting.StackRealizabilityCallFile
import Counting.StackRegisterFrames

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Sources: leader flags, previous vistas, matrix. Destinations: own flag,
own vista and own row. External registers 0--6 remain immutable inputs. -/
def ownSource : Fin 3 → Fin 30 := ![1,2,3]
def ownTarget : Fin 3 → Fin 30 := ![8,10,9]

def ownReadRoles (which : Fin 3) : Fin 21 ↪ Fin 130 where
  toFun i := ![0,115,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,
    context (ownSource which),104,context (ownTarget which),20] i
  inj' := by fin_cases which <;> decide

def readOwn {α : Type} {codec : Encoding.Codec α} (which : Fin 3)
    (parser : VerifiedParser 15 0 1 2 α codec) : Routine 128 :=
  relocate (Reader.arrayRead parser) (ownReadRoles which)

theorem readOwn_executes {α : Type} {codec : Encoding.Codec α} (which : Fin 3)
    (parser : VerifiedParser 15 0 1 2 α codec) (data : Fin 30→List Bool)
    (accepted : Bool) (tail : List Bool) (status : data 15=accepted::tail)
    (vacant : data (ownTarget which)=[]) (values : List α) (index : Fin values.length)
    (source : data (ownSource which)=(Encoding.list codec).encode values)
    (position : (data 4).length=index.val) :
    ∃ time ≤ (2*(data 4).length+3)*Complexity.polynomial parser.coefficient parser.exponent
        (data (ownSource which)).length+200*((data (ownSource which)).length+1)^2+8*(data 4).length+30,
      Executes (readOwn which parser) (file data) time
        (file (Function.update data (ownTarget which) (codec.encode values[index]))) := by
  let localStore := file data ∘ ownReadRoles which
  have sourceAt : localStore 17=data (ownSource which) := by simp [localStore,ownReadRoles]
  have indexAt : localStore 18=data 4 := by simp [localStore,ownReadRoles,file]
  obtain ⟨time,bound,run⟩ := Reader.arrayRead_get parser localStore accepted tail
    (by simp [localStore,ownReadRoles,file,status])
    (by intro r different;fin_cases r <;> simp_all [localStore,Reader.parserRoles,ownReadRoles,file])
    (by simp [localStore,ownReadRoles,vacant]) (by simp [localStore,ownReadRoles,file])
    values index [] (by simp [sourceAt,source]) (by simpa only [indexAt] using position)
  rw [sourceAt,indexAt] at bound
  have wide := relocate_executes (Reader.arrayRead parser) (ownReadRoles which) (file data) time _ run
  rw [relocatedStore_update,relocatedStore_original] at wide
  have target : ownReadRoles which 19=context (ownTarget which) := by simp [ownReadRoles]
  rw [target,file_update] at wide
  exact ⟨time,bound,wide⟩

def readLeader : Routine 128 := readOwn 0 DagParser.boolean
def readVista : Routine 128 := readOwn 1 DagParser.vista
def readRow : Routine 128 := readOwn 2 NetworkRecognition.row

def readFields : Routine 128 := sequence readLeader (sequence readVista readRow)

def fieldsData (data : Fin 30→List Bool) (leader : Bool) (vista : Executable.Vista) (row : Array Nat) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update data 8 (Encoding.boolean.encode leader))
    10 (Encoding.vista.encode vista)) 9 ((Encoding.array Encoding.natural).encode row)

theorem readFields_executes (data : Fin 30→List Bool) (n : Nat)
    (leaders : Fin n→Bool) (views : Fin n→Executable.Vista) (rows : Fin n→Array Nat) (index : Fin n)
    (status : data 15=[true]) (e8 : data 8=[]) (e9 : data 9=[]) (e10 : data 10=[])
    (leaderInput : data 1=(Encoding.array Encoding.boolean).encode (Array.ofFn leaders))
    (viewInput : data 2=(Encoding.array Encoding.vista).encode (Array.ofFn views))
    (rowInput : data 3=(Encoding.array (Encoding.array Encoding.natural)).encode (Array.ofFn rows))
    (position : (data 4).length=index.val) :
    ∃ time ≤ 100000*((data 1).length+(data 2).length+(data 3).length+(data 4).length+1)^6,
      Executes readFields (file data) time (file (fieldsData data (leaders index) (views index) (rows index))) := by
  obtain ⟨t0,b0,r0⟩ := readOwn_executes 0 DagParser.boolean data true [] status e8
    (List.ofFn leaders) ⟨index.val,by simp⟩ (by simpa [ownSource,Encoding.array,Encoding.transport,Array.toList_ofFn] using leaderInput) position
  simp only [ownTarget,Fin.getElem_fin,List.getElem_ofFn,Fin.eta] at r0
  let a := Function.update data 8 (Encoding.boolean.encode (leaders index))
  obtain ⟨t1,b1,r1⟩ := readOwn_executes 1 DagParser.vista a true [] (by simp [a,status]) (by simp [a,ownTarget,e10])
    (List.ofFn views) ⟨index.val,by simp⟩ (by simpa [a,ownSource,Encoding.array,Encoding.transport,Array.toList_ofFn] using viewInput) (by simpa [a] using position)
  simp only [ownTarget,Fin.getElem_fin,List.getElem_ofFn,Fin.eta] at r1
  let b := Function.update a 10 (Encoding.vista.encode (views index))
  obtain ⟨t2,b2,r2⟩ := readOwn_executes 2 NetworkRecognition.row b true [] (by simp [b,a,status]) (by simp [b,a,ownTarget,e9])
    (List.ofFn rows) ⟨index.val,by simp⟩ (by simpa [b,a,ownSource,Encoding.array,Encoding.transport,Array.toList_ofFn] using rowInput) (by simpa [b,a] using position)
  simp only [ownTarget,Fin.getElem_fin,List.getElem_ofFn,Fin.eta] at r2
  have joined := r0.sequence (r1.sequence r2)
  refine ⟨t0+1+(t1+1+t2),?_,joined⟩
  let S := (data 1).length+(data 2).length+(data 3).length+(data 4).length+1
  have s0 : (data 1).length+1≤S := by dsimp [S];omega
  have s1 : (data 2).length+1≤S := by dsimp [S];omega
  have s2 : (data 3).length+1≤S := by dsimp [S];omega
  have factor : 2*(data 4).length+3≤3*S := by dsimp [S];omega
  have linear : S≤S^6 := Nat.le_self_pow (by decide) _
  have power2 : S^2≤S^6 := Nat.pow_le_pow_right (by dsimp [S];omega) (by decide)
  have power5 : S^5≤S^6 := Nat.pow_le_pow_right (by dsimp [S];omega) (by decide)
  have common (L C k : Nat) (size:L+1≤S) (coefficient:C≤4000) (exponent:k≤5) :
      (2*(data 4).length+3)*Complexity.polynomial C k L+200*(L+1)^2+8*(data 4).length+30≤
        16000*S^6 := by
    have pk : (L+1)^k≤S^5 := (Nat.pow_le_pow_left size k).trans (Nat.pow_le_pow_right (by dsimp [S];omega) exponent)
    have sq : (L+1)^2≤S^6 := (Nat.pow_le_pow_left size 2).trans power2
    have p : (2*(data 4).length+3)*(C*(L+1)^k)≤3*S*(4000*S^5) := by gcongr
    have mul : 3*S*(4000*S^5)=12000*S^6 := by ring
    rw [mul] at p
    have indexBound : (data 4).length+1≤S := by dsimp [S];omega
    unfold Complexity.polynomial
    nlinarith
  have cost0 := b0.trans (common _ _ _ s0 (by decide) (by decide))
  have cost1 := b1.trans (by simpa [a,ownSource] using common _ DagParser.vista.coefficient DagParser.vista.exponent s1 (by decide) (by decide))
  have cost2 := b2.trans (by simpa [b,a,ownSource] using common _ NetworkRecognition.row.coefficient NetworkRecognition.row.exponent s2 (by decide) (by decide))
  change _≤100000*S^6
  nlinarith

end Counting.StackMachine.NetworkVista.Receiver
