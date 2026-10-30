import Counting.StackEmitIndex
import Counting.EncodingGaussianOperation

namespace Counting.StackMachine.GaussianTranscript
open Routine
set_option backward.isDefEq.respectTransparency false

inductive Kind where
  | swap | scale | add
deriving DecidableEq, Repr

def Kind.tag : Kind → Nat | .swap => 0 | .scale => 1 | .add => 2
def Kind.operation : Kind → Nat → Nat → Rat → RawRowOp
  | .swap,first,second,_ => .swap first second
  | .scale,first,_,factor => .scale first factor
  | .add,first,second,factor => .add first second factor

/-- First index, second index, factor, reversed transcript, count, payload,
copied counter, binary counter and scratch. All indices are unary plus one. -/
abbrev Workspace (extra : Nat) := Fin 9 ↪ Fin (extra+9)

def firstPositions : Fin 5 ↪ Fin 9 := ⟨![0,5,6,7,8],by decide⟩
def secondPositions : Fin 5 ↪ Fin 9 := ⟨![1,5,6,7,8],by decide⟩
def firstRoles (extra : Nat) (w : Workspace extra) : PowerWorkspace (extra+4) := firstPositions.trans w
def secondRoles (extra : Nat) (w : Workspace extra) : PowerWorkspace (extra+4) := secondPositions.trans w

@[simp] theorem firstRoles_apply (extra : Nat) (w : Workspace extra) (i : Fin 5) :
    firstRoles extra w i=w (![0,5,6,7,8] i) := rfl
@[simp] theorem secondRoles_apply (extra : Nat) (w : Workspace extra) (i : Fin 5) :
    secondRoles extra w i=w (![1,5,6,7,8] i) := rfl

def factorWord (kind : Kind) (factor : List Bool) : List Bool :=
  if kind=.swap then Encoding.rational.encode 0 else factor
def secondIndex (kind : Kind) (second : Nat) : Nat := if kind=.scale then 0 else second

def factorRoutine (kind : Kind) (extra : Nat) (w : Workspace extra) : Routine (extra+7) :=
  if kind=.swap then prepend (w 5) (Encoding.rational.encode 0)
  else ofProgram (ListPrograms.copyProgram (extra+6) (w 2) (w 5) (w 8))

theorem factor_executes (kind : Kind) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+9) → List Bool) (scratch : store (w 8)=[]) :
    ∃ time ≤ 5*(factorWord kind (store (w 2))).length+2,
      Executes (factorRoutine kind extra w) store time
        (Function.update store (w 5) (factorWord kind (store (w 2))++store (w 5))) := by
  by_cases swap : kind=.swap
  · refine ⟨2*(Encoding.rational.encode 0).length,by simp only [factorWord,if_pos swap];omega,?_⟩
    simpa only [factorRoutine,factorWord,if_pos swap] using
      prepend_executes (w 5) (Encoding.rational.encode 0) store
  · refine ⟨5*(store (w 2)).length+2,by simp [factorWord,swap],?_⟩
    simpa only [factorRoutine,factorWord,if_neg swap] using
      copy_executes (extra+6) (w 2) (w 5) (w 8)
        (fun same => (by decide : (2:Fin 9)≠5) (w.injective same))
        (fun same => (by decide : (2:Fin 9)≠8) (w.injective same))
        (fun same => (by decide : (5:Fin 9)≠8) (w.injective same)) store scratch

def secondRoutine (kind : Kind) (extra : Nat) (w : Workspace extra) : Routine (extra+7) :=
  if kind=.scale then prepend (w 5) (Encoding.natural.encode 0)
  else emitIndex (extra+4) (secondRoles extra w)

theorem second_executes (kind : Kind) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+9) → List Bool) (second : Nat)
    (source : kind≠.scale → store (w 1)=List.replicate (second+1) true)
    (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) (e8 : store (w 8)=[]) :
    ∃ time ≤ 24*(second+1)^2,
      Executes (secondRoutine kind extra w) store time
        (Function.update store (w 5) (Encoding.natural.encode (secondIndex kind second)++store (w 5))) := by
  by_cases scale : kind=.scale
  · refine ⟨2,?_,?_⟩
    · have positive : 0 < (second+1)^2 := by positivity
      omega
    · simpa [secondRoutine,secondIndex,scale,Encoding.natural,Encoding.frame] using
        prepend_executes (w 5) (Encoding.natural.encode 0) store
  · obtain ⟨time,bounded,ran⟩ := emitIndex_executes (extra+4) (secondRoles extra w) store second
      (source scale) e6 e7 e8
    exact ⟨time,bounded,by simpa [secondRoutine,secondIndex,scale] using ran⟩

def payload (kind : Kind) (first second : Nat) (factor : List Bool) : List Bool :=
  Encoding.natural.encode kind.tag++Encoding.natural.encode first++
    Encoding.natural.encode (secondIndex kind second)++factorWord kind factor

def payloadRoutine (kind : Kind) (extra : Nat) (w : Workspace extra) : Routine (extra+7) :=
  sequence (factorRoutine kind extra w)
    (sequence (secondRoutine kind extra w)
      (sequence (emitIndex (extra+4) (firstRoles extra w))
        (prepend (w 5) (Encoding.natural.encode kind.tag))))

theorem payload_executes (kind : Kind) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+9) → List Bool) (first second : Nat)
    (firstSource : store (w 0)=List.replicate (first+1) true)
    (secondSource : kind≠.scale → store (w 1)=List.replicate (second+1) true)
    (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) (e8 : store (w 8)=[]) :
    ∃ time ≤ 100*(first+second+(factorWord kind (store (w 2))).length+10)^2,
      Executes (payloadRoutine kind extra w) store time
        (Function.update store (w 5) (payload kind first second (store (w 2)))) := by
  obtain ⟨factorTime,factorBound,factorRun⟩ := factor_executes kind extra w store e8
  let factored := Function.update store (w 5) (factorWord kind (store (w 2))++store (w 5))
  obtain ⟨secondTime,secondBound,secondRun⟩ := second_executes kind extra w factored second
    (by simpa [factored,w.injective.eq_iff] using secondSource)
    (by simp [factored,w.injective.eq_iff,e6]) (by simp [factored,w.injective.eq_iff,e7])
    (by simp [factored,w.injective.eq_iff,e8])
  let withSecond := Function.update factored (w 5)
    (Encoding.natural.encode (secondIndex kind second)++factored (w 5))
  obtain ⟨firstTime,firstBound,firstRun⟩ := emitIndex_executes (extra+4) (firstRoles extra w) withSecond first
    (by simpa [withSecond,factored,w.injective.eq_iff] using firstSource)
    (by simp [withSecond,factored,w.injective.eq_iff,e6])
    (by simp [withSecond,factored,w.injective.eq_iff,e7])
    (by simp [withSecond,factored,w.injective.eq_iff,e8])
  let withFirst := Function.update withSecond (w 5) (Encoding.natural.encode first++withSecond (w 5))
  have tagRun := prepend_executes (w 5) (Encoding.natural.encode kind.tag) withFirst
  have combined := factorRun.sequence (secondRun.sequence (firstRun.sequence tagRun))
  have finalStore : Function.update withFirst (w 5) (Encoding.natural.encode kind.tag++withFirst (w 5))=
      Function.update store (w 5) (payload kind first second (store (w 2))) := by
    simp [withFirst,withSecond,factored,payload,e5,List.append_assoc]
  rw [finalStore] at combined
  refine ⟨factorTime+1+(secondTime+1+(firstTime+1+2*(Encoding.natural.encode kind.tag).length)),?_,combined⟩
  have tagBound : (Encoding.natural.encode kind.tag).length ≤ 5 := by cases kind <;> decide
  let size := first+second+(factorWord kind (store (w 2))).length+10
  have firstSize : first+1 ≤ size := by dsimp [size];omega
  have secondSize : second+1 ≤ size := by dsimp [size];omega
  have factorSize : (factorWord kind (store (w 2))).length ≤ size := by dsimp [size];omega
  have large : 1 ≤ size := by dsimp [size];omega
  have firstSquare := Nat.pow_le_pow_left firstSize 2
  have secondSquare := Nat.pow_le_pow_left secondSize 2
  have squareLarge : size ≤ size^2 := by nlinarith only [large]
  change factorTime+1+(secondTime+1+(firstTime+1+2*(Encoding.natural.encode kind.tag).length)) ≤ 100*size^2
  nlinarith only [factorBound,secondBound,firstBound,tagBound,firstSquare,secondSquare,factorSize,squareLarge,large]

theorem payload_canonical (kind : Kind) (first second : Nat) (factor : Rat) :
    payload kind first second (Encoding.rational.encode factor)=
      Encoding.rawRowOp.encode (kind.operation first second factor) := by
  cases kind <;> simp [payload,Kind.operation,Kind.tag,secondIndex,factorWord,List.append_assoc]

end Counting.StackMachine.GaussianTranscript
