import Counting.NetworkRecognitionLeaderHeader
import Counting.NetworkRecognitionSemantics
import Counting.StackEmitNatural
import Counting.StackRoutineClean

namespace Counting.StackMachine.NetworkComplement
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def leaderReady (word : List Bool) : Store 19 :=
  fun r => if r=1 then [true] else if r=17 then word else []

def leaderPrepare : Routine 19 :=
  sequence (ofProgram (ListPrograms.copyProgram 18 0 17 1))
    (sequence (clear 0) (pushBit 1 true))

theorem leaderPrepare_executes (word : List Bool) :
    Executes leaderPrepare (inputStore 19 word) (6*word.length+6) (leaderReady word) := by
  have copy := copy_executes 18 (0:Fin 21) 17 1 (by decide) (by decide) (by decide)
    (inputStore 19 word) (by simp [inputStore])
  rw [show inputStore 19 word 0=word by simp [inputStore],
    show inputStore 19 word 17=[] by simp [inputStore],List.append_nil] at copy
  let copied := Function.update (inputStore 19 word) 17 word
  have erased := clear_executes (0:Fin 21) copied
  rw [show copied 0=word by simp [copied,inputStore]] at erased
  let cleared := Function.update copied 0 []
  have pushed := pushBit_executes (1:Fin 21) true cleared
  rw [show cleared 1=[] by simp [cleared,copied,inputStore]] at pushed
  have final : Function.update cleared 1 [true]=leaderReady word := by
    funext r;fin_cases r <;> simp [cleared,copied,inputStore,leaderReady]
  rw [final] at pushed
  have composed := copy.sequence (erased.sequence pushed)
  simpa only [leaderPrepare,show 5*word.length+2+1+(word.length+1+1+1)=6*word.length+6 by omega] using composed

def leaderEmitRoles : PowerWorkspace 16 := ⟨![20,1,3,4,5],by decide⟩
def leaderEmit : Routine 19 := emitNatural 16 leaderEmitRoles

def leaderCount : Routine 19 := sequence leaderPrepare
  (sequence NetworkRecognition.leaderPrefix
    (sequence (clear 1) (sequence leaderEmit (clearRegisters [0,2,17,20]))))

/-- Count the actual initial leader bits and emit their canonical binary
natural encoding. The whole work area is erased before returning. -/
theorem leaderCount_executes (input : Simulation.Input) :
    ∃time≤3000*((Encoding.networkInput.encode input).length+1)^3,
      Executes leaderCount (inputStore 19 (Encoding.networkInput.encode input)) time
        (outputStore 19 (Encoding.natural.encode (Encoding.inputLeaderCount input))) := by
  let word := Encoding.networkInput.encode input
  let values := input.leaders.toList
  let suffix := (Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds
  have first := leaderPrepare_executes word
  obtain ⟨t1,b1,r1⟩ := NetworkRecognition.leaderPrefix_executes (leaderReady word) true []
    (by simp [leaderReady]) (by intro r h n;simp [leaderReady,n,show r≠17 by intro e;subst r;omega])
    (by simp [leaderReady]) (by simp [leaderReady]) (by simp [leaderReady]) values suffix (by rfl)
  let scanned := NetworkRecognition.leaderPrefixStore (leaderReady word) values suffix
  have erased := clear_executes (1:Fin 21) scanned
  rw [show scanned 1=[true] by simp [scanned,NetworkRecognition.leaderPrefixStore,leaderReady]] at erased
  let ready := Function.update scanned 1 []
  obtain ⟨t3,b3,r3⟩ := emitNatural_executes 16 leaderEmitRoles ready
    (by simp [ready,scanned,NetworkRecognition.leaderPrefixStore,leaderReady,leaderEmitRoles])
    (by simp [ready,scanned,NetworkRecognition.leaderPrefixStore,leaderReady,leaderEmitRoles])
    (by simp [ready,scanned,NetworkRecognition.leaderPrefixStore,leaderReady,leaderEmitRoles])
  have counter : ready (leaderEmitRoles 0)=List.replicate (values.count true) true := by
    simp [ready,scanned,NetworkRecognition.leaderPrefixStore,leaderEmitRoles]
  rw [counter,List.length_replicate] at b3 r3
  have oldout : ready (leaderEmitRoles 1)=[] := by simp [ready,leaderEmitRoles]
  rw [oldout,List.append_nil] at r3
  let emitted := Function.update ready 1 (Encoding.natural.encode (values.count true))
  have leaders : values.count true=Encoding.inputLeaderCount input := by
    symm;exact Encoding.inputLeaderCount_eq_count input
  have population := Encoding.network_agents_le_length input
  change input.leaders.size≤word.length at population
  have count := List.count_le_length (a:=true) (l:=values)
  have valuesLength : values.length=input.leaders.size := Array.length_toList
  have suffixBound : suffix.length≤word.length := by
    dsimp [suffix,word]
    rw [Encoding.networkInput_length]
    omega
  have encodedBound : (Encoding.natural.encode (values.count true)).length≤3*(word.length+1) := by
    rw [Encoding.natural_length]
    have small : (values.count true).size≤values.count true := Nat.size_le.mpr Nat.lt_two_pow_self
    change input.leaders.size≤word.length at population
    omega
  have countBound : values.count true≤word.length := by omega
  have sizeBound : (values.count true).size≤values.count true := Nat.size_le.mpr Nat.lt_two_pow_self
  have allBound : ∀r,(emitted r).length≤3*(word.length+1) := by
    intro r
    fin_cases r <;> simp [emitted,ready,scanned,NetworkRecognition.leaderPrefixStore,leaderReady]
    all_goals omega
  obtain ⟨t4,b4,r4⟩ := clearRegisters_executes [0,2,17,20] emitted (3*(word.length+1)) allBound
  have final : clearedStore [0,2,17,20] emitted=
      outputStore 19 (Encoding.natural.encode (Encoding.inputLeaderCount input)) := by
    funext r
    fin_cases r <;> simp [clearedStore,emitted,ready,scanned,NetworkRecognition.leaderPrefixStore,
      leaderReady,outputStore,leaders]
  rw [final] at r4
  have p2 : (values.count true+1)^2≤(word.length+1)^3 := by
    apply (Nat.pow_le_pow_left (show values.count true+1≤word.length+1 by omega) 2).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have emitBound := b3.trans (Nat.mul_le_mul_left 20 p2)
  have linear : word.length+1≤(word.length+1)^3 := Nat.le_self_pow (by decide) _
  have one : 1≤(word.length+1)^3 := Nat.one_le_pow _ _ (by omega)
  change t1≤1900*(word.length+1)^3 at b1
  simp only [List.length_cons,List.length_nil] at b4
  refine ⟨6*word.length+6+1+(t1+1+(2+1+(t3+1+t4))),?_,first.sequence (r1.sequence (erased.sequence (r3.sequence r4)))⟩
  change _≤3000*(word.length+1)^3
  omega

end Counting.StackMachine.NetworkComplement
