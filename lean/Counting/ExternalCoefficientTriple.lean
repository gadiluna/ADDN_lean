import Counting.ExternalCoefficientLoop
import Counting.StackRoutineFixedPrefix

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def tripleScratch : List (Fin 64) := atomScratch++[23,55]

def coefficientTriple (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (discard (w 0) 5)
    (sequence (prepend (w 23) [true,true,true])
      (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 54) (w 55) (w 20))) (coefficientAtoms extra w)))

def tripleCost (sourceLength universeLength baseLength highLength sumLimit : Nat) :=
  10+1+(6+1+(5*highLength+2+1+(3*(atomCost sourceLength universeLength baseLength sumLimit universeLength+2)+1)))

theorem coefficientTriple_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (base high a b c sumLimit : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++suffix)
    (status : store (w 1)=accepted::tail) (baseInput : store (w 52)=base.bits) (highInput : store (w 54)=high.bits)
    (sumSize : (high+powers base [a,b,c]).bits.length ≤ sumLimit)
    (fits : ∀ e∈[a,b,c],e ≤ (store (w 17)).length)
    (empty : ∀ i∈tripleScratch,store (w i)=[]) :
    ∃ time ≤ tripleCost (store (w 0)).length (store (w 17)).length base.bits.length high.bits.length sumLimit,
      Executes (coefficientTriple extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 55) (high+powers base [a,b,c]).bits) := by
  let body:=Encoding.sequence Encoding.natural [a,b,c]++suffix
  let dropped:=Function.update store (w 0) body
  have dropping:=discard_executes (w 0) 5 store
  have droppedSource : (store (w 0)).drop 5=body := by
    rw [source]
    change ((Encoding.natural.encode 3++Encoding.sequence Encoding.natural [a,b,c])++suffix).drop 5=body
    rw [List.append_assoc,show 5=(Encoding.natural.encode 3).length by decide,List.drop_left]
  rw [droppedSource] at dropping
  have pushing:=prepend_executes (w 23) [true,true,true] dropped
  have counterEmpty : dropped (w 23)=[] := by simp [dropped,w.injective.eq_iff,empty,tripleScratch]
  rw [counterEmpty,List.append_nil] at pushing
  let counted:=Function.update dropped (w 23) [true,true,true]
  have copying:=copy_executes (extra+61) (w 54) (w 55) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) counted
    (by simp [counted,dropped,w.injective.eq_iff,empty,tripleScratch,atomScratch])
  have highAt : counted (w 54)=high.bits := by simp [counted,dropped,w.injective.eq_iff,highInput]
  have targetEmpty : counted (w 55)=[] := by simp [counted,dropped,w.injective.eq_iff,empty,tripleScratch]
  rw [highAt,targetEmpty,List.append_nil] at copying
  let ready:=Function.update counted (w 55) high.bits
  have readyEmpty (i : Fin 64) (member : i∈atomScratch) : ready (w i)=[] := by
    have n0 : i≠0 := by intro same;subst i;simp [atomScratch] at member
    have n23 : i≠23 := by intro same;subst i;simp [atomScratch] at member
    have n55 : i≠55 := by intro same;subst i;simp [atomScratch] at member
    simp [ready,counted,dropped,w.injective.eq_iff,n0,n23,n55,empty i (List.mem_append_left _ member)]
  have bodyBound : body.length ≤ (store (w 0)).length := by
    rw [source]
    change body.length ≤ ((Encoding.natural.encode 3++Encoding.sequence Encoding.natural [a,b,c])++suffix).length
    dsimp [body];simp only [List.length_append];omega
  obtain ⟨loopTime,loopBound,looping⟩:=coefficientAtoms_executes extra w [a,b,c] (store (w 0)).length (store (w 17)).length base sumLimit
    ready high accepted suffix tail (by simp [ready,counted,dropped,w.injective.eq_iff,body])
    (by simpa [ready,counted,dropped,w.injective.eq_iff] using bodyBound)
    (by simp [ready,counted,dropped,w.injective.eq_iff])
    (by simp [ready,counted,dropped,w.injective.eq_iff,baseInput]) (by simp [ready]) sumSize fits
    (by simp [ready,counted,w.injective.eq_iff]) (by simp [ready,counted,dropped,w.injective.eq_iff,status]) readyEmpty
  have final : Function.update (Function.update (Function.update ready (w 23) []) (w 0) suffix)
      (w 55) (high+powers base [a,b,c]).bits=
      Function.update (Function.update store (w 0) suffix) (w 55) (high+powers base [a,b,c]).bits := by
    funext r
    by_cases e55 : r=w 55
    · subst r;simp
    · by_cases e0 : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · by_cases e23 : r=w 23
        · subst r;simp [w.injective.eq_iff,empty,tripleScratch]
        · simp [ready,counted,dropped,e55,e0,e23]
  rw [final] at looping
  refine ⟨10+1+(6+1+(5*high.bits.length+2+1+loopTime)),?_,dropping.sequence (pushing.sequence (copying.sequence looping))⟩
  unfold tripleCost
  simp only [List.length_cons,List.length_nil] at loopBound
  omega

end Counting.External.CoefficientMachine
