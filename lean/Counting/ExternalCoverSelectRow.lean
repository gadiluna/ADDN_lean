import Counting.ExternalCoverMatchAtom

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false

/-- Consume the row-membership bit and witness bit; append a unary unit
exactly when both are true. -/
def selectMembership (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) where
  states := 4
  code control := match control.val with
    | 0 => .pop (w 22) 1 1 2
    | 1 => .pop (w 32) 4 4 4
    | 2 => .pop (w 32) 4 4 3
    | 3 => .push (w 35) true 4
    | _ => .halt

def selectMembershipResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (selected member : Bool) (maskTail memberTail : List Bool) :=
  Function.update (Function.update (Function.update store (w 22) memberTail) (w 32) maskTail) (w 35)
    (if selected && member then true::store (w 35) else store (w 35))

theorem selectMembership_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (selected member : Bool) (maskTail memberTail : List Bool)
    (mask : store (w 32)=selected::maskTail) (membership : store (w 22)=member::memberTail) :
    Executes (selectMembership extra w) store (if selected && member then 3 else 2)
      (selectMembershipResult w store selected member maskTail memberTail) := by
  refine ⟨⟨4,selectMembershipResult w store selected member maskTail memberTail⟩,?_,rfl,rfl⟩
  cases selected <;> cases member <;>
    simp [Machine.run,step,selectMembership,program,mask,membership,w.injective.eq_iff,selectMembershipResult]

end Counting.External.CoverVerification
