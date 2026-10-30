import Counting.StackProtocolAdvanceTransfers
import Counting.ProtocolStateEncoding

namespace Counting.StackMachine.ProtocolAdvance
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def metadata (output : List Bool) (leaders : Nat) (vista : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (degree : Nat) (updated : List Bool) : Fin 8 → List Bool :=
  ![output,leaders.bits,Encoding.vista.encode vista,messagesCodec.encode messages,degree.bits,updated,[],[]]

abbrev parseInput : Routine 254 := sequence (readField 0) (sequence (readField 1)
  (sequence (readField 2) (sequence (readField 3) (readField 4))))

theorem parseInput_executes (state : Executable.LocalState) (messages : List (Executable.Vista×Nat)) (degree : Nat) :
    ∃ time≤ 20*((inputWord state messages degree).length+1),
      Executes parseInput (inputStore 254 (inputWord state messages degree)) time
        (file [] [] (metadata ((Encoding.optional Encoding.natural).encode state.output)
          state.leaders state.vista messages degree [])) := by
  let oldOutput:=(Encoding.optional Encoding.natural).encode state.output
  let view:=Encoding.vista.encode state.vista
  let received:=messagesCodec.encode messages
  let zero : Fin 8 → List Bool:=fun _=>[]
  let one:=Function.update zero 0 oldOutput
  let two:=Function.update one 1 state.leaders.bits
  let three:=Function.update two 2 view
  let four:=Function.update three 3 received
  have a:=readField_executes 0 (by decide) oldOutput
    (Encoding.natural.encode state.leaders++Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree) [] zero rfl rfl
  have b:=readField_executes 1 (by decide) state.leaders.bits
    (Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree) [] one
    (by simp [one,zero]) (by simp [one,zero])
  have c:=readField_executes 2 (by decide) view
    (Encoding.frame received++Encoding.natural.encode degree) [] two
    (by simp [two,one,zero]) (by simp [two,one,zero])
  have d:=readField_executes 3 (by decide) received (Encoding.natural.encode degree) [] three
    (by simp [three,two,one,zero]) (by simp [three,two,one,zero])
  have e:=readField_executes 4 (by decide) degree.bits [] [] four
    (by simp [four,three,two,one,zero]) (by simp [four,three,two,one,zero])
  simp only [List.append_nil] at e
  have start:file (Encoding.frame oldOutput++(Encoding.natural.encode state.leaders++
      Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree)) [] zero=
      inputStore 254 (inputWord state messages degree) := by
    rw [inputWord_fields]
    funext r;simp [file,inputStore,zero,oldOutput,view,received,List.append_assoc]
  rw [start] at a
  have mid1:Encoding.natural.encode state.leaders++Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree=
      Encoding.frame state.leaders.bits++(Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree) := by
    simp [Encoding.natural,List.append_assoc]
  rw [mid1] at a
  have mid2:Encoding.frame view++Encoding.frame received++Encoding.natural.encode degree=
      Encoding.frame view++(Encoding.frame received++Encoding.natural.encode degree) := List.append_assoc _ _ _
  rw [mid2] at b
  have final:Function.update four 4 degree.bits=metadata oldOutput state.leaders state.vista messages degree [] := by
    funext r;fin_cases r <;> simp [four,three,two,one,zero,metadata,view,received]
  rw [final] at e
  simp only [List.append_assoc] at a b c d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  rw [inputWord_fields]
  simp only [List.length_append,Encoding.frame_length,Encoding.natural_length,Encoding.bits_length]
  dsimp only [oldOutput,view,received]
  omega

end Counting.StackMachine.ProtocolAdvance
