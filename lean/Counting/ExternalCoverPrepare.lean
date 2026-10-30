import Counting.ExternalMatchingGeneratorLayout
import Counting.ExternalThreeDMEncoding
import Counting.StackLookupDrop

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def coverPrepare (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (readListHeader (extra+47) (w.table))
    (sequence (ofProgram (Lookup.dropProgram (extra+62) (w 0) (w 52)))
      (readListHeader (extra+47) (satHeaderRoles (extra+32) ((w.literal).reader) 0)))

def coverPrepareScratch : List (Fin 64) := [2,3,4,5,6,9,10,11,12,13,14,18,23,52]

theorem coverPrepare_executes (extra : Nat) (w : GeneratorWorkspace extra) (store : Fin (extra+64) → List Bool)
    (raw : ThreeDMEncoding.Raw) (accepted : Bool) (tail : List Bool)
    (source : store (w 0)=ThreeDMEncoding.rawCodec.encode raw) (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈coverPrepareScratch,store (w i)=[]) :
    ∃ time ≤ 4000*((store (w 0)).length+raw.1.length+1)^3,
      Executes (coverPrepare extra w) store time
        (Function.update (Function.update store (w 0)
          (Encoding.sequence (Encoding.list Encoding.natural) raw.2)) (w 23) (List.replicate raw.2.length true)) := by
  let code := (Encoding.list (Encoding.list Encoding.natural)).encode raw.2
  have sourceAs : store (w 0)=(Encoding.list Encoding.boolean).encode raw.1++code := source
  have firstEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (w.table i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [GeneratorWorkspace.table,generatorTablePositions,empty,coverPrepareScratch]
  obtain ⟨t0,b0,r0⟩ := readListHeader_canonical (extra+47) (w.table) store accepted tail status firstEmpty
    Encoding.boolean (by intro bit;exact Nat.zero_lt_succ _) raw.1 code sourceAs
  let s1 := Function.update (Function.update store (w 0) (raw.1++code)) (w 52) (List.replicate raw.1.length true)
  have r0as : Executes (readListHeader (extra+47) (w.table)) store t0 s1 := by
    change Executes _ store t0 (Function.update (Function.update store (w 0) (Encoding.sequence Encoding.boolean raw.1++code)) (w 52) (List.replicate raw.1.length true)) at r0
    simpa only [s1,sequence_boolean] using r0
  have dropping := Lookup.drop_executes (extra+62) (w 0) (w 52) (fun same=>by have:=w.injective same;contradiction) s1
  let s2 := Function.update store (w 0) code
  have droppedResult : Function.update (Function.update s1 (w 52) []) (w 0) ((s1 (w 0)).drop (s1 (w 52)).length)=s2 := by
    funext r
    by_cases a : r=w 52
    · subst r;simp [s2,w.injective.eq_iff,empty 52 (by decide)]
    · by_cases b : r=w 0
      · subst r;simp [s1,s2,w.injective.eq_iff]
      · simp [s1,s2,a,b,w.injective.eq_iff]
  rw [droppedResult] at dropping
  have dropTime : 2*(s1 (w 52)).length+1=2*raw.1.length+1 := by simp [s1]
  rw [dropTime] at dropping
  have secondEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      s2 (satHeaderRoles (extra+32) ((w.literal).reader) 0 i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,LiteralWorkspace.reader,GeneratorWorkspace.literal,literalPositions,s2,w.injective.eq_iff,empty,coverPrepareScratch]
  have positive (clause : List Nat) : 0<((Encoding.list Encoding.natural).encode clause).length := by
    simp only [Encoding.list,List.length_append,Encoding.natural_length];omega
  obtain ⟨t1,b1,r1⟩ := readListHeader_canonical (extra+47) (satHeaderRoles (extra+32) ((w.literal).reader) 0) s2 accepted tail
    (by simp [satHeaderRoles,headerPositions,LiteralWorkspace.reader,GeneratorWorkspace.literal,literalPositions,s2,w.injective.eq_iff,status]) secondEmpty
    (Encoding.list Encoding.natural) positive raw.2 [] (by change s2 (w 0)=_;simp [s2,code])
  let s3 := Function.update (Function.update s2 (w 0) (Encoding.sequence (Encoding.list Encoding.natural) raw.2))
    (w 23) (List.replicate raw.2.length true)
  have r1as : Executes (readListHeader (extra+47) (satHeaderRoles (extra+32) ((w.literal).reader) 0)) s2 t1 s3 := by
    change Executes _ s2 t1 (Function.update (Function.update s2 (w 0) (Encoding.sequence (Encoding.list Encoding.natural) raw.2++[])) (w 23) (List.replicate raw.2.length true)) at r1
    simpa only [List.append_nil,s3] using r1
  have combined := r0as.sequence (dropping.sequence r1as)
  refine ⟨t0+1+(2*raw.1.length+1+1+t1),?_,?_⟩
  · have codeBound : code.length≤(store (w 0)).length := by rw [sourceAs];simp
    change t0≤1820*((store (w 0)).length+1)^3 at b0
    have secondBound : t1≤1820*(code.length+1)^3 := by simpa [satHeaderRoles,headerPositions,LiteralWorkspace.reader,GeneratorWorkspace.literal,literalPositions,s2] using b1
    let S := (store (w 0)).length+raw.1.length+1
    have p0 : ((store (w 0)).length+1)^3≤S^3 := Nat.pow_le_pow_left (by dsimp [S];omega) 3
    have p1 : (code.length+1)^3≤S^3 := Nat.pow_le_pow_left (by dsimp [S];omega) 3
    have linear : S≤S^3 := Nat.le_self_pow (by decide : 3≠0) S
    have pos : 1≤S^3 := Nat.one_le_pow 3 S (by dsimp [S];omega)
    change _≤4000*S^3
    have nle : raw.1.length≤S := by dsimp [S];omega
    nlinarith only [b0,secondBound,p0,p1,linear,pos,nle]
  · simpa only [coverPrepare,s3,s2,Function.update_idem] using combined

end Counting.External.CoverMachine
