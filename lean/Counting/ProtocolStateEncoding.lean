import Counting.EncodingRationalRows
import Counting.EncodingVerifier
import Counting.PositiveNaturalsSpec
import Counting.ExecutableRefinementCore

namespace Counting.StackMachine.ProtocolAdvance

def stateCodec : Encoding.Codec Executable.LocalState :=
  Encoding.transport (Encoding.product (Encoding.framed (Encoding.optional Encoding.natural))
    (Encoding.product Encoding.natural (Encoding.framed Encoding.vista)))
      (fun state=>(state.output,state.leaders,state.vista))
      (fun fields=>⟨fields.2.1,fields.2.2,fields.1⟩) (by intro state;rfl)

def messagesCodec : Encoding.Codec (List (Executable.Vista×Nat)) :=
  Encoding.list (Encoding.product Encoding.vista Encoding.natural)

def inputCodec : Encoding.Codec (Executable.LocalState×List (Executable.Vista×Nat)×Nat) :=
  Encoding.product stateCodec (Encoding.product (Encoding.framed messagesCodec) Encoding.natural)

def answerCodec : Encoding.Codec (Option Executable.LocalState) := Encoding.optional stateCodec

def stateWord (state : Executable.LocalState) : List Bool := stateCodec.encode state

def inputWord (state : Executable.LocalState) (messages : List (Executable.Vista×Nat)) (degree : Nat) : List Bool :=
  inputCodec.encode (state,messages,degree)

def outputWord (state : Option Executable.LocalState) : List Bool := answerCodec.encode state

theorem inputWord_fields (state : Executable.LocalState) (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    inputWord state messages degree=
      Encoding.frame ((Encoding.optional Encoding.natural).encode state.output)++
      Encoding.natural.encode state.leaders++Encoding.frame (Encoding.vista.encode state.vista)++
      Encoding.frame (messagesCodec.encode messages)++Encoding.natural.encode degree := by
  simp [inputWord,inputCodec,stateCodec,Encoding.transport,Encoding.product,Encoding.framed,List.append_assoc]

theorem stateWord_fields (state : Executable.LocalState) :
    stateWord state=Encoding.frame ((Encoding.optional Encoding.natural).encode state.output)++
      Encoding.natural.encode state.leaders++Encoding.frame (Encoding.vista.encode state.vista) := by
  simp [stateWord,stateCodec,Encoding.transport,Encoding.product,Encoding.framed,List.append_assoc]

theorem inputWord_roundtrip (state : Executable.LocalState) (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    inputCodec.decodeExact (inputWord state messages degree)=some (state,messages,degree) := by
  exact (inputCodec.decodeExact_iff _ _).mpr rfl

theorem outputWord_roundtrip (state : Option Executable.LocalState) :
    answerCodec.decodeExact (outputWord state)=some state := by
  exact (answerCodec.decodeExact_iff _ _).mpr rfl

end Counting.StackMachine.ProtocolAdvance
