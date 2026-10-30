import Counting.StackRealizabilityVistaRead
import Counting.StackRealizabilityExternalFields

namespace Counting.StackMachine.NetworkCertificate
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def moveExternal (source target : Fin 30) : Routine 128 :=
  sequence (copyExternal source target) (clearExternal source)

theorem moveExternal_executes (data : Fin 30→List Bool) (source target : Fin 30)
    (different : source≠target) (empty : data target=[]) :
    Executes (moveExternal source target) (file data) (6*(data source).length+4)
      (file (Function.update (Function.update data target (data source)) source [])) := by
  have copied := copyExternal_executes data source target different
  rw [empty,List.append_nil] at copied
  have cleared := clearExternal_executes (Function.update data target (data source)) source
  rw [Function.update_of_ne different] at cleared
  have result := copied.sequence cleared
  simpa only [moveExternal,show 5*(data source).length+2+1+((data source).length+1)=
    6*(data source).length+4 by omega] using result

def consumeField {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (source target : Fin 30) : Routine 128 :=
  sequence (moveExternal source 5)
    (sequence (VistaComplement.readField parser target) (moveExternal 5 source))

theorem consumeField_executes {α : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser 15 0 1 2 α codec) (data : Fin 30→List Bool)
    (source target : Fin 30) (s5 : source≠5) (s4 : source≠4)
    (t5 : target≠5) (t4 : target≠4) (ts : target≠source)
    (value : α) (suffix : List Bool) (accepted : Bool) (tail : List Bool)
    (encoded : data source=codec.encode value++suffix) (status : data 4=accepted::tail)
    (e5 : data 5=[]) (et : data target=[]) :
    ∃ time ≤ Complexity.polynomial parser.coefficient parser.exponent (data source).length+
        14*(data source).length+12,
      Executes (consumeField parser source target) (file data) time
        (file (Function.update (Function.update data source suffix) target (codec.encode value))) := by
  have moving := moveExternal_executes data source 5 s5 e5
  let d1 := Function.update (Function.update data 5 (data source)) source []
  obtain ⟨t,b,read⟩ := VistaComplement.readField_executes parser d1 target t5 t4
    value suffix accepted tail
    (by simp [d1,Ne.symm s5,encoded])
    (by simp [d1,Ne.symm s4,status])
    (by simp [d1,ts,t5,et])
  let d2 := Function.update (Function.update d1 5 suffix) target (codec.encode value)
  have restoring := moveExternal_executes d2 5 source (Ne.symm s5)
    (by simp [d2,d1,Ne.symm ts,s5])
  have d2source : d2 5=suffix := by simp [d2,Ne.symm t5]
  rw [d2source] at restoring
  have final : Function.update (Function.update d2 source (d2 5)) 5 []=
      Function.update (Function.update data source suffix) target (codec.encode value) := by
    funext r
    by_cases r5 : r=5 <;> by_cases rs : r=source <;> by_cases rt : r=target <;>
      simp_all [d2,d1]
  rw [d2source] at final
  rw [final] at restoring
  have d1source : d1 5=data source := by simp [d1,Ne.symm s5]
  rw [d1source] at b
  refine ⟨_,?_,moving.sequence (read.sequence restoring)⟩
  have lengths : (data source).length=(codec.encode value).length+suffix.length := by
    rw [encoded,List.length_append]
  omega

end Counting.StackMachine.NetworkCertificate
