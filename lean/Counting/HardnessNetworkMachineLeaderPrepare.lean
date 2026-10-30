import Counting.HardnessNetworkMachineLeaderFirst
import Counting.ExternalSATHeader
import Counting.ExternalCoverNormalizeEmit

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms External.SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def leaderHeaderPositions : Fin 6 ↪ Fin 40 := ⟨![32,35,18,34,19,37],by decide⟩
def LeaderWorkspace.header (w : LeaderWorkspace extra) : External.CoverNormalization.EmitWorkspace (extra+34) :=
  leaderHeaderPositions.trans w

def leaderPrepareScratch : List (Fin 40) := [2,3,4,5,6,9,10,11,12,13,14,18,19,23,34,37]

def prepareLeaderRow (extra : Nat) (w : LeaderWorkspace extra) : Routine (extra+38) :=
  sequence (External.CoverNormalization.emitReversedNatural (extra+34) w.header)
    (sequence (prepend (w 35) [false])
      (sequence (readListHeader (extra+23) (satHeaderRoles (extra+8) w.reader 0)) (discardBit (w 23))))

def leaderPrepared (w : LeaderWorkspace extra) (store : Fin (extra+40) → List Bool)
    (first : Nat) (rest : List Nat) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0)
    (Encoding.sequence Encoding.natural (first::rest)++suffix)) (w 23) (List.replicate rest.length true)) (w 35)
    (false::((Encoding.natural.encode (store (w 32)).length).reverse++store (w 35)))

theorem prepareLeaderRow_executes (extra : Nat) (w : LeaderWorkspace extra)
    (store : Fin (extra+40) → List Bool) (first : Nat) (rest : List Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode (first::rest)++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈leaderPrepareScratch,store (w i)=[]) :
    ∃ time ≤ 30*((store (w 32)).length+1)^2+1820*((store (w 0)).length+1)^3+7,
      Executes (prepareLeaderRow extra w) store time (leaderPrepared w store first rest suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=External.CoverNormalization.emitReversedNatural_executes (extra+34) w.header store
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals simp [LeaderWorkspace.header,leaderHeaderPositions,empty,leaderPrepareScratch])
  let header:=Function.update store (w 35) ((Encoding.natural.encode (store (w 32)).length).reverse++store (w 35))
  have headerAs : Executes (External.CoverNormalization.emitReversedNatural (extra+34) w.header) store headerTime header := headerRun
  have zeroRun:=prepend_executes (w 35) [false] header
  let zeroed:=Function.update store (w 35) (false::((Encoding.natural.encode (store (w 32)).length).reverse++store (w 35)))
  have zeroAs : Executes (prepend (w 35) [false]) header 2 zeroed := by
    simpa [zeroed,header] using zeroRun
  have parseEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      zeroed (satHeaderRoles (extra+8) w.reader 0 i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,LeaderWorkspace.reader,leaderReaderPositions,zeroed,w.injective.eq_iff,empty,leaderPrepareScratch]
  obtain ⟨parseTime,parseBound,parsing⟩:=readListHeader_canonical (extra+23) (satHeaderRoles (extra+8) w.reader 0) zeroed accepted tail
    (by simp [satHeaderRoles,headerPositions,LeaderWorkspace.reader,leaderReaderPositions,zeroed,w.injective.eq_iff,status])
    parseEmpty Encoding.natural (by intro value;rw [Encoding.natural_length];omega) (first::rest) suffix
    (by simp [satHeaderRoles,headerPositions,LeaderWorkspace.reader,leaderReaderPositions,zeroed,w.injective.eq_iff,source])
  let parsed:=Function.update (Function.update zeroed (w 0) (Encoding.sequence Encoding.natural (first::rest)++suffix))
    (w 23) (List.replicate (rest.length+1) true)
  have parseAs : Executes (readListHeader (extra+23) (satHeaderRoles (extra+8) w.reader 0)) zeroed parseTime parsed := parsing
  have dropping:=discardBit_executes (w 23) parsed
  have final : Function.update parsed (w 23) (parsed (w 23)).tail=leaderPrepared w store first rest suffix := by
    funext r
    by_cases e23 : r=w 23
    · subst r;simp [parsed,leaderPrepared,w.injective.eq_iff,List.replicate_succ]
    · by_cases e0 : r=w 0
      · subst r;simp [parsed,zeroed,leaderPrepared,w.injective.eq_iff]
      · simp [parsed,zeroed,leaderPrepared,Function.update_apply,e23,e0]
  rw [final] at dropping
  have combined:=headerAs.sequence (zeroAs.sequence (parseAs.sequence dropping))
  refine ⟨_,?_,combined⟩
  change headerTime ≤ 30*((store (w 32)).length+1)^2 at headerBound
  have parseLimit : parseTime ≤ 1820*((store (w 0)).length+1)^3 := by
    simpa [satHeaderRoles,headerPositions,LeaderWorkspace.reader,leaderReaderPositions,zeroed,w.injective.eq_iff] using parseBound
  omega

end Counting.HardnessNetworkMachine
