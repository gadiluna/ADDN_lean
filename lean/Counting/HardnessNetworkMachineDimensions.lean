import Counting.StackUnaryMultiply
import Counting.StackRoutineBasic
import Counting.StackRoutineRelocate
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.HardnessNetworkDimensions
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Registers 0/1 contain explicit unary q/m. Only outputs 2/3 change;
registers 4/5 are real reusable scratch, and register 6 is untouched. -/
abbrev routine : Routine 5 := sequence (ofProgram (ListPrograms.copyProgram 4 0 2 5))
  (sequence (prepend 2 [true,true,true])
    (sequence (ofProgram (ListPrograms.copyProgram 4 1 4 5))
      (sequence (pushBit 4 true)
        (sequence (repeatedCopy 4 2 4 3 5) (prepend 3 [true,true])))))

def cost (q m : Nat) : Nat := 5*q+5*m+(5*(q+3)+4)*(m+1)+21

theorem routine_executes (store : Store 5) (q m : Nat)
    (first : store 0=List.replicate q true) (second : store 1=List.replicate m true)
    (outB : store 2=[]) (outN : store 3=[]) (counter : store 4=[]) (scratch : store 5=[]) :
    Executes routine store (cost q m)
      (Function.update (Function.update store 2 (List.replicate (q+3) true))
        3 (List.replicate (2+(m+1)*(q+3)) true)) := by
  have a := copy_executes 4 (0:Fin 7) 2 5 (by decide) (by decide) (by decide) store scratch
  rw [first,outB,List.append_nil,List.length_replicate] at a
  let copied := Function.update store 2 (List.replicate q true)
  have b := prepend_executes (2:Fin 7) [true,true,true] copied
  have bs : Function.update copied 2 ([true,true,true]++copied 2)=
      Function.update store 2 (List.replicate (q+3) true) := by
    simp only [copied,Function.update_self,Function.update_idem]
    congr 1
  rw [bs] at b
  let base := Function.update store 2 (List.replicate (q+3) true)
  have c := copy_executes 4 (1:Fin 7) 4 5 (by decide) (by decide) (by decide) base (by simp [base,scratch])
  have mAt : base 1=List.replicate m true := by simp [base,second]
  have countEmpty : base 4=[] := by simp [base,counter]
  rw [mAt,countEmpty,List.append_nil,List.length_replicate] at c
  let copiedM := Function.update base 4 (List.replicate m true)
  have d := pushBit_executes (4:Fin 7) true copiedM
  have ds : Function.update copiedM 4 (true::copiedM 4)=
      Function.update base 4 (List.replicate (m+1) true) := by
    simp only [copiedM,Function.update_self,Function.update_idem,List.replicate_succ]
  rw [ds] at d
  let ready := Function.update base 4 (List.replicate (m+1) true)
  have e := unary_multiply_executes 4 (2:Fin 7) 4 3 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (q+3) (m+1) ready (by simp [ready,base]) (by simp [ready]) (by simp [ready,base,scratch])
  let multiplied := Function.update base 3 (List.replicate ((m+1)*(q+3)) true)
  have es : Function.update (Function.update ready 4 []) 3
      (List.replicate ((m+1)*(q+3)) true++ready 3)=multiplied := by
    have restored : Function.update ready 4 []=base := by
      simp only [ready,Function.update_idem]
      rw [←countEmpty,Function.update_eq_self]
    rw [restored]
    simp [ready,base,outN,multiplied]
  rw [es] at e
  have f := prepend_executes (3:Fin 7) [true,true] multiplied
  have fs : Function.update multiplied 3 ([true,true]++multiplied 3)=
      Function.update base 3 (List.replicate (2+(m+1)*(q+3)) true) := by
    simp only [multiplied,Function.update_self,Function.update_idem]
    congr 1
    change List.replicate 2 true++List.replicate ((m+1)*(q+3)) true=_
    rw [←List.replicate_add]
  rw [fs] at f
  have combined := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))
  convert combined using 1 <;> first | rfl | (simp only [cost,List.length_cons,List.length_nil];omega)

theorem cost_polynomial (q m : Nat) : cost q m≤40*(q+m+1)^2 := by
  unfold cost
  nlinarith [Nat.zero_le (q*q),Nat.zero_le (m*m),Nat.zero_le (q*m)]


theorem relocated_executes (extra : Nat) (roles : Fin 7 ↪ Fin (extra+7))
    (store : Store (extra+5)) (q m : Nat)
    (first : store (roles 0)=List.replicate q true) (second : store (roles 1)=List.replicate m true)
    (outB : store (roles 2)=[]) (outN : store (roles 3)=[])
    (counter : store (roles 4)=[]) (scratch : store (roles 5)=[]) :
    Executes (relocate routine roles) store (cost q m)
      (Function.update (Function.update store (roles 2) (List.replicate (q+3) true))
        (roles 3) (List.replicate (2+(m+1)*(q+3)) true)) := by
  have ran := routine_executes (store ∘ roles) q m first second outB outN counter scratch
  apply relocate_executes_frame routine roles _ _ _ _ (cost q m) rfl _ _ ran
  · intro r;fin_cases r <;> simp [roles.injective.eq_iff]
  · intro r outside
    have n2 : r≠roles 2 := fun eq=>outside 2 eq.symm
    have n3 : r≠roles 3 := fun eq=>outside 3 eq.symm
    simp [n2,n3]

end Counting.StackMachine.HardnessNetworkDimensions
