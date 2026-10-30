import Counting.StackRealizabilityReachSpec
import Counting.StackEncodingRelabel

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def reachLoopRoles : Fin 14 ↪ Fin 17 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 17=>r.val) equal

def reachLoop17 : Routine 15:=mapRegisters reachLoopRoles (forEach 13 reachItem)

def reachLoop17Store (store : Store 15) (value : Bool) (tail bits : List Bool) : Store 15:=
  Function.update (Function.update (Function.update (Function.update store 13 [])
    5 (reachFold (store 0) (store 1) (store 2).length (store 3).length (store 4).length bits.length value::tail))
    3 (List.replicate bits.length true++store 3))
    4 ((List.replicate bits.length (store 2)).flatten++store 4)

theorem reachLoop17_executes (store : Store 15) (value : Bool) (tail bits : List Bool)
    (accumulated : store 5=value::tail) (counted : store 13=bits)
    (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) :
    ∃ time ≤ bits.length*(60*((store 0).length+(store 1).length+(store 2).length+
        (store 3).length+(store 4).length+1+bits.length*((store 2).length+1))+2)+1,
      Executes reachLoop17 store time (reachLoop17Store store value tail bits):=by
  let original:Store 12:=store ∘ reachLoopRoles
  obtain ⟨time,bound,ran⟩:=reachLoop_executes original value tail bits accumulated counted e6 e7 e9 e10 e11 e12
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame (forEach 13 reachItem) reachLoopRoles store _ original
    (reachLoopStore original value tail bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [reachLoop17Store,reachLoopStore,original,reachLoopRoles]
  · intro r outside
    have n3 : r≠3:=by intro same;subst r;exact outside 3 rfl
    have n4 : r≠4:=by intro same;subst r;exact outside 4 rfl
    have n5 : r≠5:=by intro same;subst r;exact outside 5 rfl
    have n13 : r≠13:=by intro same;subst r;exact outside 13 rfl
    simp [reachLoop17Store,n3,n4,n5,n13]

end Counting.StackMachine.RealizabilityCheck
