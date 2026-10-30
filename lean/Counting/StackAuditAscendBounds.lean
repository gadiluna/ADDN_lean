import Counting.StackAuditAscendLoop

namespace Counting.StackMachine.AuditAscend
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Polynomial time in the real table, binary initial code and explicit
unary step budget. Parent indices themselves never become unary budgets. -/
theorem ascendLoop_polynomial (store : Store 30) (vista : Executable.Vista) (code : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=code.bits)
    (empty : ∀ r : Fin 32,r.val≤28 → r≠17 → r≠24 → r≠25 → store r=[])
    (bits : List Bool) (counter : store 25=bits) :
    ∃ time ≤ 100000000*((store 17).length+code.size+bits.length+1)^5,
      Executes ascendLoop store time (loopResult store vista bits.length code) := by
  let width:=max code.size (store 17).length
  obtain ⟨time,bound,ran⟩:=ascendLoop_executes store vista code source current empty width
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) bits counter
  let K:=(store 17).length+code.size+bits.length+1
  have positive : 1≤K := by dsimp only [K];omega
  have factor : (store 17).length+width+1≤2*K := by dsimp only [width,K];omega
  have raised:=Nat.pow_le_pow_left factor 4
  have bodyBound : 5000000*((store 17).length+width+1)^4+2≤80000000*K^4+2 := by
    nlinarith only [raised]
  have rounds : bits.length≤K := by dsimp only [K];omega
  have productBound:=Nat.mul_le_mul rounds bodyBound
  have linear : K≤K^5 := Nat.le_self_pow (by decide) _
  have one : 1≤K^5 := Nat.one_le_pow _ _ positive
  refine ⟨time,?_,ran⟩
  change time≤100000000*K^5
  nlinarith only [bound,productBound,linear,one]

/-- The physical repeated lookup computes the exact executable ancestor,
including None and the zero-step case on arbitrary starting references. -/
theorem ascendLoop_ascend (store : Store 30) (vista : Executable.Vista) (reference : Option Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=(indexCode reference).bits)
    (empty : ∀ r : Fin 32,r.val≤28 → r≠17 → r≠24 → r≠25 → store r=[])
    (bits : List Bool) (counter : store 25=bits) :
    ∃ time ≤ 100000000*((store 17).length+(indexCode reference).size+bits.length+1)^5,
      Executes ascendLoop store time
        (Function.update (Function.update store 25 []) 24
          (indexCode (reference.bind (Executable.ascend vista bits.length))).bits) := by
  simpa only [loopResult,walkCode_ascend] using
    ascendLoop_polynomial store vista (indexCode reference) source current empty bits counter

end Counting.StackMachine.AuditAscend

