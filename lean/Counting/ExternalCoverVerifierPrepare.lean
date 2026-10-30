import Counting.ExternalCoverPrepare
import Counting.StackRoutineMove
import Counting.X3CEncoding

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev VerifierWorkspace (extra : Nat) := MatchingMachine.GeneratorWorkspace extra

def verifierPrepareScratch : List (Fin 64) := coverPrepareScratch++[34,41,42]

def verifierPrepare (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (coverPrepare extra w)
    (sequence (move (extra+61) (w 0) (w 34) (w 41))
      (sequence (clear (w 23)) (ofProgram (ListPrograms.copyProgram (extra+61) (w 17) (w 42) (w 41)))))

def verifierPrepareResult (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool)
    (raw : X3CEncoding.Raw) :=
  Function.update (Function.update (Function.update store (w 0) []) (w 34)
    (Encoding.sequence (Encoding.list Encoding.natural) raw.2)) (w 42) (store (w 17))

theorem verifierPrepare_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (raw : X3CEncoding.Raw) (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=X3CEncoding.rawCodec.encode raw) (status : store (w 1)=accepted::tail)
    (universeSize : (store (w 17)).length=raw.1.length)
    (empty : ∀ i∈verifierPrepareScratch,store (w i)=[]) :
    ∃ time ≤ 4100*((store (w 0)).length+raw.1.length+1)^3,
      Executes (verifierPrepare extra w) store time (verifierPrepareResult w store raw) := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := coverPrepare_executes extra w store raw accepted tail source status
    (fun i member=>empty i (List.mem_append_left _ member))
  let stream := Encoding.sequence (Encoding.list Encoding.natural) raw.2
  let prepared := Function.update (Function.update store (w 0) stream) (w 23) (List.replicate raw.2.length true)
  have moving := move_executes (extra+61) (w 0) (w 34) (w 41)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) prepared
    (by simp [prepared,w.injective.eq_iff,empty,verifierPrepareScratch])
  have sourceAt : prepared (w 0)=stream := by simp [prepared,w.injective.eq_iff]
  have targetAt : prepared (w 34)=[] := by simp [prepared,w.injective.eq_iff,empty,verifierPrepareScratch]
  rw [sourceAt,targetAt,List.append_nil] at moving
  let moved := Function.update (Function.update prepared (w 34) stream) (w 0) []
  have clearing := clear_executes (w 23) moved
  have counterAt : moved (w 23)=List.replicate raw.2.length true := by simp [moved,prepared,w.injective.eq_iff]
  rw [counterAt,List.length_replicate] at clearing
  let cleared := Function.update moved (w 23) []
  have copying := copy_executes (extra+61) (w 17) (w 42) (w 41)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) cleared
    (by simp [cleared,moved,prepared,w.injective.eq_iff,empty,verifierPrepareScratch])
  have universeAt : cleared (w 17)=store (w 17) := by simp [cleared,moved,prepared,w.injective.eq_iff]
  have outsideAt : cleared (w 42)=[] := by simp [cleared,moved,prepared,w.injective.eq_iff,empty,verifierPrepareScratch]
  rw [universeAt,outsideAt,List.append_nil,universeSize] at copying
  have final : Function.update cleared (w 42) (store (w 17))=verifierPrepareResult w store raw := by
    funext r
    by_cases e23 : r=w 23
    · subst r;simp [verifierPrepareResult,cleared,w.injective.eq_iff,empty,verifierPrepareScratch,coverPrepareScratch]
    · by_cases e0 : r=w 0
      · subst r;simp [verifierPrepareResult,cleared,moved,w.injective.eq_iff]
      · simp [verifierPrepareResult,cleared,moved,prepared,stream,Function.update_apply,e23,e0]
  rw [final] at copying
  refine ⟨prepareTime+1+(6*stream.length+4+1+(raw.2.length+1+1+(5*raw.1.length+2))),?_,
    preparing.sequence (moving.sequence (clearing.sequence copying))⟩
  have streamBound : stream.length ≤ (store (w 0)).length := by
    rw [source]
    change stream.length ≤ ((Encoding.list Encoding.boolean).encode raw.1++(Encoding.natural.encode raw.2.length++stream)).length
    simp only [List.length_append];omega
  have rowsBound : raw.2.length ≤ stream.length := by
    apply StackMachine.EncodingPrograms.VerifiedParser.sequence_count_le
    intro row
    simp only [Encoding.list,List.length_append,Encoding.natural_length]
    omega
  let size := (store (w 0)).length+raw.1.length+1
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp [size];omega)
  change prepareTime ≤ 4000*size^3 at prepareBound
  change _ ≤ 4100*size^3
  dsimp only [size] at *
  omega

end Counting.External.CoverVerification
