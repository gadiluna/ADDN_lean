import Counting.ExternalCoefficientAtom
import Counting.StackUnaryQuotientThree
import Counting.StackRoutineUnary

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Recover q from the explicit universe of size 3q, retain its unary
counter, and compute the binary base q+3. -/
def prepareBase (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 26) (w 20)))
    (sequence (quotientThree (w 26) (w 27))
      (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 27) (w 26) (w 20)))
        (sequence (pushBit (w 52) true)
          (sequence (pushBit (w 52) true)
            (ofProgram (Unary.toBinaryProgram (extra+61) (w 26) (w 52) (w 20)))))))

def baseScratch : List (Fin 64) := [20,26,27,52]

theorem prepareBase_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (q : Nat) (universeInput : store (w 17)=List.replicate (3*q) true)
    (empty : ∀ i∈baseScratch,store (w i)=[]) :
    ∃ time ≤ 100*(q+1)^2, Executes (prepareBase extra w) store time
      (Function.update (Function.update store (w 27) (List.replicate q true)) (w 52) (q+3).bits) := by
  have copying:=copy_executes (extra+61) (w 17) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by decide))
  rw [universeInput,empty 26 (by decide),List.append_nil,List.length_replicate] at copying
  let copied:=Function.update store (w 26) (List.replicate (3*q) true)
  have dividing:=quotientThree_executes (w 26) (w 27) (by simp [w.injective.eq_iff]) q copied (by simp [copied])
  have dividedFinal : Function.update (Function.update copied (w 26) []) (w 27)
      (List.replicate q true++copied (w 27))=Function.update store (w 27) (List.replicate q true) := by
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [copied,w.injective.eq_iff,empty,baseScratch]
    · simp [copied,Function.update_apply,e26,w.injective.eq_iff,empty,baseScratch]
  rw [dividedFinal] at dividing
  let divided:=Function.update store (w 27) (List.replicate q true)
  have copyingQ:=copy_executes (extra+61) (w 27) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) divided
    (by simp [divided,w.injective.eq_iff,empty,baseScratch])
  have qAt : divided (w 27)=List.replicate q true := by simp [divided]
  have counterEmpty : divided (w 26)=[] := by simp [divided,w.injective.eq_iff,empty,baseScratch]
  rw [qAt,counterEmpty,List.append_nil,List.length_replicate] at copyingQ
  let ready:=Function.update divided (w 26) (List.replicate q true)
  let one:=Function.update ready (w 52) [true]
  let three:=Function.update ready (w 52) [true,true]
  have pushOne : Executes (pushBit (w 52) true) ready 1 one := by
    simpa [ready,divided,one,w.injective.eq_iff,empty,baseScratch] using pushBit_executes (w 52) true ready
  have pushThree : Executes (pushBit (w 52) true) one 1 three := by
    simpa [one,three] using pushBit_executes (w 52) true one
  obtain ⟨convertTime,convertBound,converting⟩:=toBinary_executes (extra+61) (w 26) (w 52) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) three 3
    (by simp only [three,Function.update_self];rfl)
    (by simp [three,ready,divided,w.injective.eq_iff,empty,baseScratch])
  have counterAt : three (w 26)=List.replicate q true := by simp [three,ready,w.injective.eq_iff]
  rw [counterAt,List.length_replicate] at convertBound converting
  have final : Function.update (Function.update three (w 26) []) (w 52) (3+q).bits=
      Function.update divided (w 52) (q+3).bits := by
    rw [Nat.add_comm 3 q]
    funext r
    by_cases e52 : r=w 52
    · subst r;simp
    · by_cases e26 : r=w 26
      · subst r;simp [divided,w.injective.eq_iff,empty,baseScratch]
      · simp [three,ready,e52,e26]
  rw [final] at converting
  refine ⟨5*(3*q)+2+1+(4*q+1+1+(5*q+2+1+(1+1+(1+1+convertTime)))),?_,
    copying.sequence (dividing.sequence (copyingQ.sequence (pushOne.sequence (pushThree.sequence converting))))⟩
  nlinarith only [convertBound]

end Counting.External.CoefficientMachine
