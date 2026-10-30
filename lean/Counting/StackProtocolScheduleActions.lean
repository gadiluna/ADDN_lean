import Counting.StackProtocolScheduleFields

namespace Counting.StackMachine.ProtocolSchedule
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev zeroLeader : Routine 14 := DagValidation.emptyFlag 8 2

theorem zeroLeader_executes (leaders round : Nat) :
    ∃ time≤ 3,Executes zeroLeader (fields leaders round 0 0 []) time
      (fields leaders round 0 0 [decide (leaders=0)]) := by
  have run:=DagValidation.emptyFlag_executes (8:Fin 16) 2 (fields leaders round 0 0 [])
  change Executes _ _ (DagValidation.emptyFlagCost leaders.bits)
    (Function.update (fields leaders round 0 0 []) 2 [decide (leaders.bits=[])]) at run
  have nil_iff:leaders.bits=[] ↔ leaders=0 := by
    have zero:Nat.bits 0=[] := rfl
    rw [←zero,Encoding.bits_injective.eq_iff]
  simp only [nil_iff] at run
  have target:Function.update (fields leaders round 0 0 []) 2 [decide (leaders=0)]=
      fields leaders round 0 0 [decide (leaders=0)] := by
    funext r;by_cases flag:r=2 <;> simp [fields,file,flag]
  rw [target] at run
  refine ⟨_,?_,run⟩
  unfold DagValidation.emptyFlagCost;split <;> omega

abbrev oneLeader : Routine 14 := sequence (pushBit 6 true)
  (sequence (Compare.preservingEquality 10 oneRoles) (clear 6))

theorem oneLeader_executes (leaders round : Nat) :
    ∃ time≤ 6*leaders.size+22,
      Executes oneLeader (fields leaders round 0 0 []) time
        (fields leaders round 0 0 [decide (leaders=1)]) := by
  let initial:=fields leaders round 0 0 []
  have a:=pushBit_executes (6:Fin 16) true initial
  change Executes _ initial 1 (Function.update initial 6 [true]) at a
  let ready:=Function.update initial 6 [true]
  have b:=Compare.preservingEquality_executes 10 oneRoles ready
    (by simp [ready,initial,fields,file,oneRoles])
    (by simp [ready,initial,fields,file,oneRoles])
    (by simp [ready,initial,fields,file,oneRoles])
  change Executes _ ready (Compare.preservingCost leaders.bits [true])
    (Function.update ready 2 [decide (leaders.bits=[true])]) at b
  have equal:leaders.bits=[true] ↔ leaders=1 := by
    rw [←Nat.one_bits,Encoding.bits_injective.eq_iff]
  simp only [equal] at b
  let checked:=Function.update ready 2 [decide (leaders=1)]
  have c:=clear_executes (6:Fin 16) checked
  have source:checked 6=[true] := by simp [checked,ready]
  rw [source,List.length_singleton] at c
  have target:Function.update checked 6 []=fields leaders round 0 0 [decide (leaders=1)] := by
    funext r;fin_cases r <;> simp [checked,ready,initial,fields,file]
  rw [target] at c
  have cost:=Compare.preservingCost_le leaders.bits [true]
  simp only [Encoding.bits_length,List.length_singleton] at cost
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

abbrev readRound : Routine 14 := sequence (ofProgram (ListPrograms.copyProgram 13 9 10 15)) (splitRound 10 2)

theorem readRound_executes (leaders round : Nat) :
    Executes readRound (fields leaders round 0 0 []) (5*round.size+5)
      (fields leaders round (round/2) 0 [decide (round%2=1)]) := by
  have a:=copy_executes 13 (9:Fin 16) 10 15 (by decide) (by decide) (by decide)
    (fields leaders round 0 0 []) rfl
  have source:fields leaders round 0 0 [] 9=round.bits := rfl
  have vacant:fields leaders round 0 0 [] 10=[] := rfl
  rw [source,vacant,List.append_nil] at a
  change Executes _ _ (5*round.bits.length+2) (Function.update (fields leaders round 0 0 []) 10 round.bits) at a
  let ready:=fields leaders round round 0 []
  have stored:Function.update (fields leaders round 0 0 []) 10 round.bits=ready := by
    funext r;fin_cases r <;> simp [ready,fields,file]
  rw [stored] at a
  have b:=splitRound_executes (10:Fin 16) 2 (by decide) ready round rfl
  have target:Function.update (Function.update ready 10 (round/2).bits) 2 (decide (round%2=1)::ready 2)=
      fields leaders round (round/2) 0 [decide (round%2=1)] := by
    funext r;fin_cases r <;> simp [ready,fields,file]
  rw [target] at b
  have run:=a.sequence b
  simpa only [Encoding.bits_length,show 5*round.size+2+1+2=5*round.size+5 by omega] using run

abbrev incrementCandidate : Routine 14 := DagValidation.incrementRoutine 13 12 10 13

theorem incrementCandidate_executes (leaders round candidate last : Nat) :
    ∃ time≤ 4*candidate.size+7,
      Executes incrementCandidate (fields leaders round candidate last []) time
        (fields leaders round (candidate+1) last []) := by
  obtain ⟨time,bound,run⟩:=DagValidation.increment_natural 13 (12:Fin 16) 10 13
    (by decide) (by decide) (by decide) (fields leaders round candidate last []) rfl rfl candidate rfl
  have target:Function.update (fields leaders round candidate last []) 10 (candidate+1).bits=
      fields leaders round (candidate+1) last [] := by
    funext r;fin_cases r <;> simp [fields,file]
  exact ⟨time,bound,by rwa [target] at run⟩

abbrev saveLast : Routine 14 := ofProgram (ListPrograms.copyProgram 13 10 11 15)

theorem saveLast_executes (leaders round candidate : Nat) :
    Executes saveLast (fields leaders round candidate 0 []) (5*candidate.size+2)
      (fields leaders round candidate candidate []) := by
  have run:=copy_executes 13 (10:Fin 16) 11 15 (by decide) (by decide) (by decide)
    (fields leaders round candidate 0 []) rfl
  have source:fields leaders round candidate 0 [] 10=candidate.bits := rfl
  have vacant:fields leaders round candidate 0 [] 11=[] := rfl
  rw [source,vacant,List.append_nil] at run
  change Executes _ _ (5*candidate.bits.length+2)
    (Function.update (fields leaders round candidate 0 []) 11 candidate.bits) at run
  have target:Function.update (fields leaders round candidate 0 []) 11 candidate.bits=
      fields leaders round candidate candidate [] := by
    funext r;fin_cases r <;> simp [fields,file]
  rwa [target,Encoding.bits_length] at run

abbrev emitCandidate : Routine 14 := sequence (frameRoutine 13 11 1 15)
  (sequence (frameRoutine 13 10 1 15) (pushBit 1 true))

theorem emitCandidate_executes (leaders round candidate last : Nat) :
    Executes emitCandidate (fields leaders round candidate last []) (5*last.size+5*candidate.size+11)
      (file [] (outputWord (some (candidate,last))) leaders.bits round.bits [] [] []) := by
  let initial:=fields leaders round candidate last []
  have a:=frame_executes_updates 13 (11:Fin 16) 1 15 (by decide) (by decide) (by decide) initial rfl
  let first:=file [] (Encoding.natural.encode last) leaders.bits round.bits candidate.bits [] []
  have firstStore:Function.update (Function.update initial 11 []) 1 (Encoding.frame (initial 11)++initial 1)=first := by
    funext r;fin_cases r <;> simp [initial,first,fields,file,Encoding.natural]
  rw [firstStore] at a
  change Executes _ initial (5*last.bits.length+4) first at a
  have b:=frame_executes_updates 13 (10:Fin 16) 1 15 (by decide) (by decide) (by decide) first rfl
  let payload:=Encoding.natural.encode candidate++Encoding.natural.encode last
  let second:=file [] payload leaders.bits round.bits [] [] []
  have secondStore:Function.update (Function.update first 10 []) 1 (Encoding.frame (first 10)++first 1)=second := by
    funext r;fin_cases r <;> simp [first,second,payload,file,Encoding.natural]
  rw [secondStore] at b
  change Executes _ first (5*candidate.bits.length+4) second at b
  have c:=pushBit_executes (1:Fin 16) true second
  have target:Function.update second 1 (true::second 1)=
      file [] (outputWord (some (candidate,last))) leaders.bits round.bits [] [] [] := by
    funext r;fin_cases r <;> simp [second,payload,file,outputWord,Encoding.optional,Encoding.product]
  rw [target] at c
  have run:=a.sequence (b.sequence c)
  simpa only [Encoding.bits_length,show 5*last.size+4+1+(5*candidate.size+4+1+1)=
      5*last.size+5*candidate.size+11 by omega] using run

end Counting.StackMachine.ProtocolSchedule
