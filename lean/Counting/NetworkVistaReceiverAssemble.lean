import Counting.NetworkVistaReceiverCollect
import Counting.StackNetworkCertificateItem
import Counting.StackVistaRawPrepare

namespace Counting.StackMachine.NetworkVista.Receiver
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def assembleFields : List (Fin 30) := [8,9,10,12,15]

def assembledData (data : Fin 30→List Bool) (word : List Bool) : Fin 30→List Bool :=
  NetworkCertificate.erased assembleFields (Function.update (Function.update data 11 []) 13 word)

def assemble : Routine 128 := sequence (copyExternal 12 13)
  (sequence (copyExternal 10 13)
    (sequence (frameRoutine 127 (context 11) (context 13) (context 14))
      (sequence (copyExternal 8 13)
        (sequence (copyExternal 0 13) (NetworkCertificate.clearFields assembleFields)))))

theorem assemble_executes (data : Fin 30→List Bool) (round degree : Nat) (leader : Bool)
    (old : Executable.Vista) (messages : List (Executable.Vista×Nat))
    (roundAt : data 0=Encoding.natural.encode round)
    (leaderAt : data 8=Encoding.boolean.encode leader)
    (vistaAt : data 10=Encoding.vista.encode old) (degreeAt : data 11=degree.bits)
    (messagesAt : data 12=(Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages)
    (e13 : data 13=[]) (e14 : data 14=[])
    (bound : Nat) (bounded : ∀r,(data r).length≤bound) :
    ∃ time ≤ 100*(bound+1), Executes assemble (file data) time
      (file (assembledData data (DagUpdate.Raw.inputWord round leader degree old messages))) := by
  have first := copyExternal_executes data 12 13 (by decide)
  rw [e13,List.append_nil] at first
  let a := Function.update data 13 (data 12)
  have second := copyExternal_executes a 10 13 (by decide)
  let b := Function.update a 13 (data 10++data 12)
  have second' : Executes (copyExternal 10 13) (file a) (5*(data 10).length+2) (file b) := by
    simpa [a,b] using second
  have third := frame_executes 127 (context 11) (context 13) (context 14)
    (by intro eq;have := context.injective eq;contradiction)
    (by intro eq;have := context.injective eq;contradiction)
    (by intro eq;have := context.injective eq;contradiction) (file b) (by simp [b,a,e14])
  have frameInput : file b (context 11)=data 11 := by simp [b,a]
  rw [frameInput] at third
  let c := Function.update (Function.update b 11 []) 13 (Encoding.frame (data 11)++(data 10++data 12))
  have frameFinal : frameResult 127 (context 11) (context 13) (context 14) (file b)=file c := by
    funext r
    fin_cases r <;> simp [frameResult,file,context,c,b,a,e14]
  rw [frameFinal] at third
  have fourth := copyExternal_executes c 8 13 (by decide)
  let d := Function.update c 13 (data 8++(Encoding.frame (data 11)++(data 10++data 12)))
  have fourth' : Executes (copyExternal 8 13) (file c) (5*(data 8).length+2) (file d) := by
    simpa [d,c,b,a] using fourth
  have fifth := copyExternal_executes d 0 13 (by decide)
  let word := data 0++(data 8++(Encoding.frame (data 11)++(data 10++data 12)))
  let e := Function.update d 13 word
  have fifth' : Executes (copyExternal 0 13) (file d) (5*(data 0).length+2) (file e) := by
    simpa [e,word,d,c,b,a] using fifth
  have eachBound : ∀r,(e r).length≤6*bound+1 := by
    intro r
    by_cases r13:r=13
    · subst r
      simp only [e,Function.update_self,word,List.length_append,Encoding.frame_length]
      have := bounded 0;have := bounded 8;have := bounded 11;have := bounded 10;have := bounded 12
      omega
    by_cases r11:r=11
    · subst r;simp [e,d,c,b,a]
    simpa [e,d,c,b,a,r13,r11] using (bounded r).trans (by omega : bound≤6*bound+1)
  obtain ⟨t6,b6,r6⟩ := NetworkCertificate.clearFields_executes assembleFields e (6*bound+1) eachBound
  have encoded : word=DagUpdate.Raw.inputWord round leader degree old messages := by
    simp only [word,roundAt,leaderAt,degreeAt,vistaAt,messagesAt,DagUpdate.Raw.inputWord,
      DagUpdate.Raw.inputCodec,Encoding.product,Encoding.natural,DagUpdate.Receive.messageCodec]
  have final : NetworkCertificate.erased assembleFields e=assembledData data word := by
    simp only [e,d,c,b,a,Function.update_idem,assembledData]
    rw [Function.update_comm (by decide : (13:Fin 30)≠11)]
    simp only [Function.update_idem]
  rw [final,encoded] at r6
  refine ⟨_,?_,first.sequence (second'.sequence (third.sequence (fourth'.sequence (fifth'.sequence r6))))⟩
  have b0:=bounded 0;have b8:=bounded 8;have b10:=bounded 10;have b11:=bounded 11;have b12:=bounded 12
  simp only [assembleFields,List.length_cons,List.length_nil] at b6
  omega

end Counting.StackMachine.NetworkVista.Receiver
