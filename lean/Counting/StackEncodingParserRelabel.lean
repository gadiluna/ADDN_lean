import Counting.StackEncodingRelabel
import Counting.StackEncodingParser

namespace Counting.StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

theorem parseStore_project {small large : Nat} (roles : Fin (small+2) ↪ Fin (large+2))
    (source status output : Fin (small+2)) (store : Routine.Store large)
    (accepted : Bool) (tail : List Bool) (effect : ParseEffect) (r : Fin (small+2)) :
    parseStore (roles source) (roles status) (roles output) store accepted tail effect (roles r)=
      parseStore source status output (fun i=>store (roles i)) accepted tail effect r := by
  simp only [parseStore,roles.injective.eq_iff]

namespace VerifiedParser

/-- Relocate a proved parser into any larger register file without changing
its code semantics, output format, or number of stack steps. -/
def relabel {small large : Nat} {source status output : Fin (small+2)}
    {α : Type} {codec : Encoding.Codec α} (roles : Fin (small+2) ↪ Fin (large+2))
    (parser : VerifiedParser small source status output α codec) :
    VerifiedParser large (roles source) (roles status) (roles output) α codec where
  work:=parser.work.map roles
  separate r member:=by
    obtain ⟨i,inside,rfl⟩:=Finset.mem_map.mp member
    obtain ⟨first,second,third⟩:=parser.separate i inside
    exact ⟨fun h=>first (roles.injective h),fun h=>second (roles.injective h),
      fun h=>third (roles.injective h)⟩
  routine:=Routine.mapRegisters roles parser.routine
  effect:=parser.effect
  coefficient:=parser.coefficient
  exponent:=parser.exponent
  suffix_le:=parser.suffix_le
  code_le:=parser.code_le
  sound:=parser.sound
  roundtrip:=parser.roundtrip
  executes store accepted tail statusEq workEmpty:=by
    have work (r : Fin (small+2)) (member : r∈parser.work) : store (roles r)=[] :=
      workEmpty (roles r) (Finset.mem_map.mpr ⟨r,member,rfl⟩)
    obtain ⟨time,bounded,executed⟩:=parser.executes (fun r=>store (roles r)) accepted tail statusEq work
    obtain ⟨result,ran,inside,outside⟩:=Routine.mapRegisters_executes roles parser.routine store time
      (parseStore source status output (fun r=>store (roles r)) accepted tail
        (parser.effect (store (roles source)))) executed
    have resultEq : result=parseStore (roles source) (roles status) (roles output) store accepted tail
        (parser.effect (store (roles source))) := by
      funext r
      by_cases member : ∃ i,roles i=r
      · obtain ⟨i,rfl⟩:=member
        rw [parseStore_project]
        exact inside i
      · have external : ∀ i,roles i≠r := by simpa only [not_exists] using member
        rw [outside r external]
        simp only [parseStore,if_neg (Ne.symm (external source)),if_neg (Ne.symm (external status)),
          if_neg (Ne.symm (external output))]
    rw [resultEq] at ran
    exact ⟨time,bounded,ran⟩

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
