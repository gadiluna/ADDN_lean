import Counting.StackProtocolUpdateRaw
import Counting.StackDagCanonicalComplete
import Counting.PositiveNaturalsSpec

namespace Counting.StackMachine.ProtocolUpdate
open Routine NetworkComplement Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

theorem output_length_of_execution {registers : Nat} (routine : Routine registers)
    (input output : List Bool) (time : Nat)
    (run : Executes routine (inputStore registers input) time (outputStore registers output)) :
    output.length ≤ input.length+time := by
  obtain ⟨last,ran,_,stored⟩:=run
  have bound:=run_dataLength (initial routine.program input) last time ran
  rw [initial_dataLength] at bound
  have component:(last.store 1).length≤last.dataLength:=
    Finset.single_le_sum (f:=fun r=>(last.store r).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ 1)
  rw [stored] at component
  simpa only [outputStore,↓reduceIte] using component.trans bound

def canonicalData (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : Fin 30→List Bool :=
  Function.update (rawData old messages degree) 6
    (Encoding.vista.encode (canonicalize (rawUpdate old messages degree)))

def canonicalCall : Routine 158 := call DagUpdate.Canonical.completeCanonical (by decide) 5 6
def canonicalCallCoefficient : Nat := 7*DagUpdate.Canonical.completeCanonicalCoefficient+30

theorem canonicalCall_executes (old : Vista) (messages : List (Vista×Nat)) (degree : Nat)
    (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ 0 < m.2 ∧
      (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    ∃time≤canonicalCallCoefficient*((Encoding.vista.encode (rawUpdate old messages degree)).length+1)^136,
      Executes canonicalCall (file (rawData old messages degree)) time (file (canonicalData old messages degree)) ∧
      (Encoding.vista.encode (canonicalize (rawUpdate old messages degree))).length≤
        (DagUpdate.Canonical.completeCanonicalCoefficient+1)*
          ((Encoding.vista.encode (rawUpdate old messages degree)).length+1)^136 := by
  let source:=rawUpdate old messages degree
  have good:=rawUpdate_valid old messages degree valid received
  have nonempty:0 < source.nodes.size := Nat.zero_lt_of_lt (rawUpdate_bottom_lt old messages degree)
  obtain ⟨time,bound,run⟩:=DagUpdate.Canonical.completeCanonical_executes source
    (nodesValid_of_valid source good) nonempty
  have length:=output_length_of_execution DagUpdate.Canonical.completeCanonical _ _ time run
  have rawAt:rawData old messages degree 5=Encoding.vista.encode source := by simp [rawData,source]
  have run' : Executes DagUpdate.Canonical.completeCanonical (inputStore 128 (rawData old messages degree 5)) time
      (outputStore 128 (Encoding.vista.encode (canonicalize source))) := by simpa only [rawAt] using run
  have called:=call_executes DagUpdate.Canonical.completeCanonical (by decide) (rawData old messages degree) 5 6
    (by simp [rawData,assembledData,metadataData,preparedData]) _ time run'
  rw [rawAt] at called
  have linear:(Encoding.vista.encode source).length+1≤((Encoding.vista.encode source).length+1)^136:=
    Nat.le_self_pow (by decide) _
  have outBound:(Encoding.vista.encode (canonicalize source)).length≤
      (DagUpdate.Canonical.completeCanonicalCoefficient+1)*((Encoding.vista.encode source).length+1)^136 := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  refine ⟨_,?_,called,outBound⟩
  change _≤(7*DagUpdate.Canonical.completeCanonicalCoefficient+30)*((Encoding.vista.encode source).length+1)^136
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

def finish : Routine 158 := sequence
  (ofProgram (ListPrograms.copyProgram 157 (context 6) 1 0)) (pushBit 1 true)

def outputWord (output : Option Vista) : List Bool := (Encoding.optional Encoding.vista).encode output

theorem finish_executes (data : Fin 30→List Bool) (vista : Vista) (value : data 6=Encoding.vista.encode vista) :
    ∃output,Executes finish (file data) (5*(Encoding.vista.encode vista).length+4) output ∧
      output 1=outputWord (some vista) := by
  have copy:=copy_executes 157 (context 6) 1 0
    (context_ne_local 6 1 (by decide)) (context_ne_local 6 0 (by decide)) (by decide) (file data) (by simp)
  rw [file_context,value,show file data 1=[] by simp,List.append_nil] at copy
  let copied:=Function.update (file data) 1 (Encoding.vista.encode vista)
  have tag:=pushBit_executes (1:Fin 160) true copied
  rw [show copied 1=Encoding.vista.encode vista by simp [copied]] at tag
  refine ⟨Function.update copied 1 (true::Encoding.vista.encode vista),?_,?_⟩
  · simpa only [finish,show 5*(Encoding.vista.encode vista).length+2+1+1=
      5*(Encoding.vista.encode vista).length+4 by omega] using copy.sequence tag
  · simp [outputWord,Encoding.optional]

end Counting.StackMachine.ProtocolUpdate
