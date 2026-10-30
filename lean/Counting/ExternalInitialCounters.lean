import Counting.ExternalUnaryEmission
import Counting.StackSubtractLength
import Counting.StackComparePreserving
import Counting.StackCompareLengthPreserving
import Counting.StackLookupPreserving

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Position, offset, header word, witness capacity; output is role 5.
Roles 6–20 contain temporary indices, flags, codec data and copy work. -/
abbrev InitialWorkspace (extra : Nat) := Fin 24 ↪ Fin (extra+24)

def initialIndex (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+21) (w 0) (w 6) (w 20)))
    (subtractLength (extra+20) (w 1) (w 6) (w 13) (w 20))

theorem initialIndex_executes (extra : Nat) (w : InitialWorkspace extra) (place offset : Nat)
    (store : Fin (extra+24) → List Bool)
    (placeValue : store (w 0)=List.replicate place true) (offsetValue : store (w 1)=List.replicate offset true)
    (indexEmpty : store (w 6)=[]) (counterEmpty : store (w 13)=[]) (workEmpty : store (w 20)=[]) :
    Executes (initialIndex extra w) store (5*place+7*offset+7)
      (Function.update store (w 6) (List.replicate (place-offset) true)) := by
  have distinct {a b : Fin 24} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let copied := Function.update store (w 6) (List.replicate place true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 0) (w 6) (w 20))) store
      (5*place+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,placeValue,indexEmpty,List.length_replicate,List.append_nil,copied] using
      copy_executes (extra+21) (w 0) (w 6) (w 20)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  have subtract := subtractLength_executes (extra+20) (w 1) (w 6) (w 13) (w 20)
    (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) copied
    (by simp [copied,w.injective.eq_iff,counterEmpty]) (by simp [copied,w.injective.eq_iff,workEmpty])
  have source : copied (w 1)=List.replicate offset true := by simp [copied,w.injective.eq_iff,offsetValue]
  have target : copied (w 6)=List.replicate place true := by simp [copied]
  have subtraction : Executes (subtractLength (extra+20) (w 1) (w 6) (w 13) (w 20)) copied
      (7*offset+4) (Function.update store (w 6) (List.replicate (place-offset) true)) := by
    simpa only [source,target,List.length_replicate,List.drop_replicate,copied,Function.update_idem] using subtract
  have combined := copy.sequence subtraction
  simpa +instances only [initialIndex,ListPrograms.copyProgram,show 5*place+2+1+(7*offset+4)=5*place+7*offset+7 by omega] using combined

def initialEnd (extra : Nat) (w : InitialWorkspace extra) : Routine (extra+22) :=
  sequence (ofProgram (Unary.lengthProgram (extra+21) (w 2) (w 12) (w 20)))
    (ofProgram (ListPrograms.copyProgram (extra+21) (w 3) (w 12) (w 20)))

theorem initialEnd_executes (extra : Nat) (w : InitialWorkspace extra) (capacity : Nat)
    (store : Fin (extra+24) → List Bool) (capacityValue : store (w 3)=List.replicate capacity true)
    (endEmpty : store (w 12)=[]) (workEmpty : store (w 20)=[]) :
    Executes (initialEnd extra w) store (5*(store (w 2)).length+5*capacity+5)
      (Function.update store (w 12) (List.replicate ((store (w 2)).length+capacity) true)) := by
  have distinct {a b : Fin 24} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let measured := Function.update store (w 12) (List.replicate (store (w 2)).length true)
  have measure : Executes (ofProgram (Unary.lengthProgram (extra+21) (w 2) (w 12) (w 20))) store
      (5*(store (w 2)).length+2) measured := by
    simpa +instances only [Unary.lengthProgram,endEmpty,List.append_nil,measured] using
      length_executes (extra+21) (w 2) (w 12) (w 20)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  have add := copy_executes (extra+21) (w 3) (w 12) (w 20)
    (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) measured
    (by simp [measured,w.injective.eq_iff,workEmpty])
  have source : measured (w 3)=List.replicate capacity true := by simp [measured,w.injective.eq_iff,capacityValue]
  have target : measured (w 12)=List.replicate (store (w 2)).length true := by simp [measured]
  have addition : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 3) (w 12) (w 20))) measured
      (5*capacity+2) (Function.update store (w 12) (List.replicate ((store (w 2)).length+capacity) true)) := by
    simpa +instances only [ListPrograms.copyProgram,source,target,List.length_replicate,←List.replicate_add,
      measured,Function.update_idem,Nat.add_comm capacity] using add
  have combined := measure.sequence addition
  simpa +instances only [initialEnd,Unary.lengthProgram,ListPrograms.copyProgram,
    show 5*(store (w 2)).length+2+1+(5*capacity+2)=5*(store (w 2)).length+5*capacity+5 by omega] using combined

end Counting.External.CookLevin.StackGenerator
