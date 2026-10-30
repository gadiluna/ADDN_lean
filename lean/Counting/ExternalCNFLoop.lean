import Counting.ExternalCNFStep
import Counting.StackLoop

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

abbrev LoopWorkspace (extra : Nat) := Fin 46 ↪ Fin (extra+46)
def loopStepRoles (extra : Nat) (w : LoopWorkspace extra) : StepWorkspace (extra+1) :=
  (Fin.castLEEmb (by decide : 45≤46)).trans w

def gateLoop (extra : Nat) (w : LoopWorkspace extra) : Routine (extra+44) :=
  forEach (w 45) (gateStep (extra+1) (loopStepRoles extra w))

def gateRows (current terminal : Nat) : Nat → List (Nat×Bool) → List (List (Nat×Bool))
  | 0,_ => []
  | count+1,literals => gateClauses current (literals.headD (terminal,true))++gateRows (current+1) terminal count literals.tail

theorem sequence_append {α : Type} (codec : Encoding.Codec α) (a b : List α) :
    Encoding.sequence codec (a++b)=Encoding.sequence codec a++Encoding.sequence codec b := by
  induction a with
  | nil => rfl
  | cons head rest ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]

def loopResult (extra : Nat) (w : LoopWorkspace extra) (store : Fin (extra+46) → List Bool)
    (count : Nat) (literals : List (Nat×Bool)) (terminal : Nat) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store (w 45) [])
    (w 24) (List.replicate (literals.drop count).length true))
    (w 0) (Encoding.sequence literalCodec (literals.drop count)++suffix))
    (w 34) (List.replicate count true++store (w 34)))
    (w 42) ((Encoding.sequence (Encoding.list literalCodec)
      (gateRows (store (w 34)).length terminal count literals)).reverse++store (w 42))

theorem gateLoop_executes (extra : Nat) (w : LoopWorkspace extra)
    (count : Nat) (store : Fin (extra+46) → List Bool) (literals : List (Nat×Bool))
    (terminal limitSource limitCode : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence literalCodec literals++suffix)
    (sourceBound : (store (w 0)).length≤limitSource)
    (counter : store (w 24)=List.replicate literals.length true)
    (iterations : store (w 45)=List.replicate count true)
    (status : store (w 1)=accepted::tail)
    (positive : store (w 32)=literalCodec.encode (terminal,true))
    (negative : store (w 33)=literalCodec.encode (terminal,false))
    (empty : ∀ i∈stepScratch,store (w (Fin.castLE (by decide : 45≤46) i))=[])
    (bounded : ∀ j<count,∀ i : Fin 6,
      (literalCodec.encode (gateSource ((store (w 34)).length+j)
        ((literals.drop j).headD (terminal,true)) i)).length≤limitCode) :
    ∃ time ≤ count*(1000*(limitSource+(store (w 32)).length+(store (w 33)).length+limitCode+(store (w 34)).length+count+2)^2+2)+1,
      Executes (gateLoop extra w) store time (loopResult extra w store count literals terminal suffix) := by
  have ne (i j : Fin 46) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  induction count generalizing store literals with
  | zero =>
    have run := repeat_empty (w 45) (gateStep (extra+1) (loopStepRoles extra w)) store iterations
    have unchanged : loopResult extra w store 0 literals terminal suffix=store := by
      have iterationEmpty : store (w 45)=[] := iterations
      simp only [loopResult,List.drop_zero,List.replicate_zero,List.nil_append,gateRows,Encoding.sequence,List.reverse_nil]
      rw [←iterationEmpty,Function.update_eq_self,←counter,Function.update_eq_self,
        ←source,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨⟨1,store⟩,run.1,run.2,unchanged.symm⟩⟩
  | succ count ih =>
    let consumed := Function.update store (w 45) (List.replicate count true)
    have consumedSource : consumed (w 0)=Encoding.sequence literalCodec literals++suffix := by
      simpa [consumed,w.injective.eq_iff] using source
    have consumedEmpty (i : Fin 45) (member : i∈stepScratch) : consumed (w (Fin.castLE (by decide : 45≤46) i))=[] := by
      have diff : Fin.castLE (by decide : 45≤46) i≠(45 : Fin 46) := by intro same;have value:=congrArg Fin.val same;change i.val=45 at value;have:=i.isLt;omega
      simpa only [consumed,Function.update_of_ne (ne _ _ diff)] using empty i member
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := gateStep_executes (extra+1) (loopStepRoles extra w)
      consumed literals terminal limitCode accepted suffix tail consumedSource
      (by simp [loopStepRoles,consumed,w.injective.eq_iff,counter]) (by simp [loopStepRoles,consumed,w.injective.eq_iff,status])
      (by simp [loopStepRoles,consumed,w.injective.eq_iff,positive]) (by simp [loopStepRoles,consumed,w.injective.eq_iff,negative]) consumedEmpty
      (by intro i;simpa [consumed,loopStepRoles,w.injective.eq_iff] using bounded 0 (by omega) i)
    let next := stepResult (extra+1) (loopStepRoles extra w) consumed literals terminal suffix
    have nextSource : next (w 0)=Encoding.sequence literalCodec literals.tail++suffix := by simp [next,stepResult,loopStepRoles,w.injective.eq_iff]
    have nextBound : (next (w 0)).length≤limitSource := by
      rw [nextSource]
      cases literals with
      | nil => simpa [source,Encoding.sequence] using sourceBound
      | cons literal rest =>
        rw [source] at sourceBound
        simp only [Encoding.sequence,List.length_append] at sourceBound
        simpa using (show (Encoding.sequence literalCodec rest++suffix).length≤limitSource by simp only [List.length_append];omega)
    have nextCounter : next (w 24)=List.replicate literals.tail.length true := by simp [next,stepResult,loopStepRoles,w.injective.eq_iff]
    have nextIterations : next (w 45)=List.replicate count true := by simp [next,stepResult,loopStepRoles,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,stepResult,loopStepRoles,consumed,w.injective.eq_iff,status]
    have nextPositive : next (w 32)=literalCodec.encode (terminal,true) := by simp [next,stepResult,loopStepRoles,consumed,w.injective.eq_iff,positive]
    have nextNegative : next (w 33)=literalCodec.encode (terminal,false) := by simp [next,stepResult,loopStepRoles,consumed,w.injective.eq_iff,negative]
    have nextCurrent : next (w 34)=true::store (w 34) := by simp [next,stepResult,loopStepRoles,consumed,w.injective.eq_iff]
    have nextEmpty (i : Fin 45) (member : i∈stepScratch) : next (w (Fin.castLE (by decide : 45≤46) i))=[] := by
      have diffs : i.val≠0 ∧ i.val≠24 ∧ i.val≠34 ∧ i.val≠42 := by
        simp only [stepScratch,List.mem_cons,List.not_mem_nil] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h <;> first | decide | contradiction
      simpa [next,stepResult,loopStepRoles,w.injective.eq_iff,Fin.ext_iff,diffs] using consumedEmpty i member
    have nextCodeBound (j : Nat) (less : j<count) (i : Fin 6) :
        (literalCodec.encode (gateSource ((next (w 34)).length+j)
          ((literals.tail.drop j).headD (terminal,true)) i)).length≤limitCode := by
      rw [nextCurrent]
      simpa only [List.length_cons,List.drop_tail,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bounded (j+1) (by omega) i
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih next literals.tail nextSource nextBound nextCounter nextIterations
      nextStatus nextPositive nextNegative nextEmpty nextCodeBound
    have firstRun := repeat_iteration (w 45) (gateStep (extra+1) (loopStepRoles extra w)) store true
      (List.replicate count true) (by simpa only [List.replicate_succ] using iterations)
      bodyTime finishBody bodyRun bodyHalt
    change Machine.run (step (gateLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,finishBody.store⟩ at firstRun
    refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,?_⟩⟩
    · rw [nextCurrent,nextPositive,nextNegative] at tailBound
      simp only [List.length_cons] at tailBound
      change bodyTime≤1000*((consumed (w 0)).length+(consumed (w 32)).length+(consumed (w 33)).length+limitCode+(consumed (w 34)).length+2)^2 at bodyBound
      have unchanged (i : Fin 46) (different : i≠45) : consumed (w i)=store (w i) := by simp [consumed,w.injective.eq_iff,different]
      rw [unchanged 0 (by decide),unchanged 32 (by decide),unchanged 33 (by decide),unchanged 34 (by decide)] at bodyBound
      let S := limitSource+(store (w 32)).length+(store (w 33)).length+limitCode+(store (w 34)).length+(count+1)+2
      have bodyLimit : bodyTime≤1000*S^2 := bodyBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S];omega) 2))
      have tailLimit : tailTime≤count*(1000*S^2+2)+1 := by
        simpa only [S,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,positive,negative] using tailBound
      change bodyTime+2+tailTime≤(count+1)*(1000*S^2+2)+1
      nlinarith only [bodyLimit,tailLimit]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 45
      · subst r;simp [loopResult,w.injective.eq_iff]
      · by_cases b : r=w 24
        · subst r;simp [loopResult,w.injective.eq_iff,List.drop_tail]
        · by_cases c : r=w 0
          · subst r;simp [loopResult,w.injective.eq_iff,List.drop_tail]
          · by_cases d : r=w 34
            · subst r;simp [loopResult,w.injective.eq_iff,nextCurrent,List.replicate_succ',List.append_assoc]
            · by_cases e : r=w 42
              · subst r
                simp [loopResult,next,stepResult,loopStepRoles,consumed,w.injective.eq_iff,gateRows,
                  sequence_append,List.reverse_append,List.append_assoc]
              · simp [loopResult,next,stepResult,loopStepRoles,consumed,a,b,c,d,e]

end Counting.External.CNFMachine
