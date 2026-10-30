import Counting.StackNetworkCertificateParser
import Counting.StackEncodingListReadHeader
import Counting.StackRealizabilityCallFile
import Counting.StackDagGuards

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

def viewHeaderRoles : FullListWorkspace 113 :=
  ⟨![110,104,0,1,112,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩
def certHeaderRoles : FullListWorkspace 113 :=
  ⟨![111,104,0,1,113,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def headers : Routine 128 := sequence (readListHeader 113 viewHeaderRoles)
  (readListHeader 113 certHeaderRoles)

theorem header_executes (w : FullListWorkspace 113) (source counter : Fin 30)
    (sourceAt : w 0=context source) (statusAt : w 1=context 4) (counterAt : w 4=context counter)
    {α : Type} (codec : Encoding.Codec α) (positive : ∀value,0<(codec.encode value).length)
    (data : Fin 30→List Bool) (values : List α) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) (encoded : data source=(Encoding.list codec).encode values)
    (empty : ∀ i : Fin 17,i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) → file data (w i)=[]) :
    ∃ time ≤ 1820*((data source).length+1)^3,
      Executes (readListHeader 113 w) (file data) time
        (file (Function.update (Function.update data source (Encoding.sequence codec values))
          counter (List.replicate values.length true))) := by
  obtain ⟨time,cost,run⟩ := readListHeader_canonical 113 w (file data) accepted tail
    (by simpa only [statusAt,file_context] using status) empty codec positive values []
    (by simpa only [sourceAt,file_context,List.append_nil] using encoded)
  rw [sourceAt,file_context] at cost
  rw [sourceAt,counterAt,List.append_nil,file_update,file_update] at run
  exact ⟨time,cost,run⟩

theorem headers_executes (data : Fin 30→List Bool) (views : List Executable.Vista)
    (certificates : List Encoding.TwoOrderData) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail)
    (viewsAt : data 10=(Encoding.list Encoding.vista).encode views)
    (certsAt : data 11=Encoding.networkWitness.encode certificates)
    (e12 : data 12=[]) (e13 : data 13=[]) :
    ∃ time ≤ 3641*((data 10).length+(data 11).length+1)^3,
      Executes headers (file data) time
        (file (Function.update (Function.update (Function.update (Function.update data
          10 (Encoding.sequence Encoding.vista views)) 12 (List.replicate views.length true))
          11 (Encoding.sequence Encoding.twoOrderWitness certificates)) 13
          (List.replicate certificates.length true))) := by
  have emptyV i (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      file data (viewHeaderRoles i)=[] := by
    fin_cases i <;> simp_all [viewHeaderRoles,file]
  obtain ⟨t0,b0,r0⟩ := header_executes viewHeaderRoles 10 12 rfl rfl rfl Encoding.vista
    vista_encoding_positive data views accepted tail status viewsAt emptyV
  let next := Function.update (Function.update data 10 (Encoding.sequence Encoding.vista views))
    12 (List.replicate views.length true)
  have emptyC i (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      file next (certHeaderRoles i)=[] := by
    fin_cases i <;> simp_all [certHeaderRoles,file,next]
  obtain ⟨t1,b1,r1⟩ := header_executes certHeaderRoles 11 13 rfl rfl rfl Encoding.twoOrderWitness
    witness_encoding_positive next certificates accepted tail (by simp [next,status])
    (by simpa [next,Encoding.networkWitness] using certsAt) emptyC
  have n11 : next 11=data 11 := by simp [next]
  rw [n11] at b1
  have pow0 := Nat.pow_le_pow_left (by omega : (data 10).length+1≤(data 10).length+(data 11).length+1) 3
  have pow1 := Nat.pow_le_pow_left (by omega : (data 11).length+1≤(data 10).length+(data 11).length+1) 3
  have one : 1≤((data 10).length+(data 11).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  exact ⟨t0+1+t1,by nlinarith only [b0,b1,pow0,pow1,one],r0.sequence r1⟩

def countRoles : Fin 6 ↪ Fin 130 := ⟨![112,113,104,0,1,2],by decide⟩
def countsEqual : Routine 128 := DagValidation.equalityGuard 124 countRoles

theorem countsEqual_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) :
    ∃ time ≤ 6*((data 12).length+(data 13).length)+15,
      Executes countsEqual (file data) time
        (file (Function.update data 4 ((accepted && decide (data 12=data 13))::tail))) := by
  have run := DagValidation.equalityGuard_executes 124 countRoles (file data) accepted tail
    (by simpa [countRoles,file] using status) (by simp [countRoles,file])
    (by simp [countRoles,file]) (by simp [countRoles,file])
  have a : file data (countRoles 0)=data 12 := by simp [countRoles,file]
  have b : file data (countRoles 1)=data 13 := by simp [countRoles,file]
  rw [a,b] at run
  change Executes countsEqual (file data) (Compare.preservingCost (data 12) (data 13)+4)
    (Function.update (file data) (context 4) ((accepted && decide (data 12=data 13))::tail)) at run
  rw [file_update] at run
  have cost := Compare.preservingCost_le (data 12) (data 13)
  exact ⟨_,by omega,run⟩

end Counting.StackMachine.NetworkCertificate
