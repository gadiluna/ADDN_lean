import Counting.HardnessNetworkMachineRepeat
import Counting.ExternalCoverNaturalRead

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

abbrev LeaderWorkspace (extra : Nat) := Fin 40 ↪ Fin (extra+40)
def leaderReaderPositions : Fin 32 ↪ Fin 40 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 40=>i.val) h)⟩
def LeaderWorkspace.reader (w : LeaderWorkspace extra) : External.SATVerification.SATWorkspace (extra+8) :=
  leaderReaderPositions.trans w
def leaderRepeatPositions : Fin 5 ↪ Fin 40 := ⟨![18,34,35,36,37],by decide⟩
def LeaderWorkspace.repeated (w : LeaderWorkspace extra) : RepeatWorkspace (extra+35) :=
  leaderRepeatPositions.trans w

def leaderBlockScratch : List (Fin 40) := [2,3,5,6,9,18,34,36,37]

def emitLeaderBlock (extra : Nat) (w : LeaderWorkspace extra) : Routine (extra+38) :=
  sequence (External.CoverMachine.readNatural (extra+8) w.reader)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+37) (w 33) (w 34) (w 37)))
      (emitRepeatedCode (extra+35) w.repeated))

def leaderBlockCost (sourceLength count : Nat) := 100*(sourceLength+1)*(count+1)+20

/-- A leader block contains one binary coefficient per explicitly represented
member of a group. Parsing consumes exactly one framed natural number. -/
theorem emitLeaderBlock_executes (extra : Nat) (w : LeaderWorkspace extra)
    (store : Fin (extra+40) → List Bool) (value : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.natural.encode value++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈leaderBlockScratch,store (w i)=[]) :
    ∃ time ≤ leaderBlockCost (store (w 0)).length (store (w 33)).length,
      Executes (emitLeaderBlock extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 35)
          ((Encoding.sequence Encoding.natural (List.replicate (store (w 33)).length value)).reverse++store (w 35))) := by
  obtain ⟨readTime,readBound,reading⟩:=External.CoverMachine.readNatural_executes (extra+8) w.reader store value accepted suffix tail source status
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl
        all_goals simp [LeaderWorkspace.reader,leaderReaderPositions,empty,leaderBlockScratch])
  let parsed:=Function.update (Function.update store (w 0) suffix) (w 18) (Encoding.natural.encode value)
  have readAs : Executes (External.CoverMachine.readNatural (extra+8) w.reader) store readTime parsed := reading
  have copying:=copy_executes (extra+37) (w 33) (w 34) (w 37)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) parsed
    (by simp [parsed,w.injective.eq_iff,empty,leaderBlockScratch])
  have groupAt : parsed (w 33)=store (w 33) := by simp [parsed,w.injective.eq_iff]
  have counterEmpty : parsed (w 34)=[] := by simp [parsed,w.injective.eq_iff,empty,leaderBlockScratch]
  rw [groupAt,counterEmpty,List.append_nil] at copying
  let ready:=Function.update parsed (w 34) (store (w 33))
  have repeated:=emitRepeatedCode_executes (extra+35) w.repeated ready
    (by simp [LeaderWorkspace.repeated,leaderRepeatPositions,ready,parsed,w.injective.eq_iff,empty,leaderBlockScratch])
    (by simp [LeaderWorkspace.repeated,leaderRepeatPositions,ready,parsed,w.injective.eq_iff,empty,leaderBlockScratch])
  have result : repeatedCodeResult w.repeated ready=
      Function.update (Function.update store (w 0) suffix) (w 35)
        ((Encoding.sequence Encoding.natural (List.replicate (store (w 33)).length value)).reverse++store (w 35)) := by
    change Function.update (Function.update (Function.update ready (w 18) []) (w 34) []) (w 35)
      (copies (ready (w 34)).length (ready (w 18)).reverse++ready (w 35))=_
    have code : ready (w 18)=Encoding.natural.encode value := by simp [ready,parsed,w.injective.eq_iff]
    have count : ready (w 34)=store (w 33) := by simp [ready]
    rw [code,count,repeated_natural_code]
    funext r
    by_cases e18 : r=w 18
    · subst r;simp [w.injective.eq_iff,empty,leaderBlockScratch]
    · by_cases e34 : r=w 34
      · subst r;simp [w.injective.eq_iff,empty,leaderBlockScratch]
      · simp [ready,parsed,Function.update_apply,e18,e34,w.injective.eq_iff]
  rw [result] at repeated
  have combined:=readAs.sequence (copying.sequence repeated)
  refine ⟨_,?_,combined⟩
  have codeBound : (Encoding.natural.encode value).length ≤ (store (w 0)).length := by rw [source];simp
  change readTime ≤ 60*((store (w 0)).length+1) at readBound
  simp only [LeaderWorkspace.repeated,leaderRepeatPositions,Function.Embedding.trans_apply] at ⊢
  change readTime+1+(5*(store (w 33)).length+2+1+
    (3*(ready (w 18)).length+(5*(ready (w 18)).length+4)*(ready (w 34)).length+5)) ≤ _
  have codeAt : ready (w 18)=Encoding.natural.encode value := by simp [ready,parsed,w.injective.eq_iff]
  have countAt : ready (w 34)=store (w 33) := by simp [ready]
  rw [codeAt,countAt]
  dsimp only [leaderBlockCost]
  nlinarith only [readBound,codeBound,Nat.mul_le_mul_right (store (w 33)).length codeBound]

end Counting.HardnessNetworkMachine
