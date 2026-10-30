import Counting.ExternalCNFOptionalAtom
import Counting.ExternalCNFFresh
import Counting.StackRoutineClearSelected

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

abbrev StepWorkspace (extra : Nat) := Fin 45 ↪ Fin (extra+45)
def stepOptionalRoles (extra : Nat) (w : StepWorkspace extra) : OptionalWorkspace (extra+11) :=
  (Fin.castLEEmb (by decide : 34≤45)).trans w

def stepFreshPositions : Fin 8 ↪ Fin 45 := ⟨![34,35,36,37,38,39,40,41],by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def stepFreshRoles (extra : Nat) (w : StepWorkspace extra) : FreshWorkspace (extra+37) := stepFreshPositions.trans w

def stepGatePositions : Fin 9 ↪ Fin 45 := ⟨![35,36,37,38,30,31,42,43,44],by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def stepGateRoles (extra : Nat) (w : StepWorkspace extra) : GateWorkspace (extra+36) := stepGatePositions.trans w

def stepOutputs : List (Fin 45) := [30,31,35,36,37,38]
def stepScratch : List (Fin 45) := [2,3,4,5,6,9,10,18,21,30,31,35,36,37,38,39,40,41,43,44]

theorem stepOutputs_covered (i : Fin 45) (member : i∈stepOutputs) :
    ∃ j : Fin 6,stepGatePositions (Fin.castLE (by decide) j)=i := by
  simp only [stepOutputs,List.mem_cons,List.not_mem_nil] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|h
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · contradiction

theorem stepOutputs_different (i : Fin 45) (member : i∈stepOutputs) :
    i≠0 ∧ i≠24 ∧ i≠34 ∧ i≠42 ∧ i∈stepScratch := by
  simp only [stepOutputs,List.mem_cons,List.not_mem_nil] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|h <;> simp_all [stepScratch]

def gateStep (extra : Nat) (w : StepWorkspace extra) : Routine (extra+43) :=
  sequence (optionalAtom (extra+11) (stepOptionalRoles extra w))
    (sequence (freshPair (extra+37) (stepFreshRoles extra w))
      (sequence (gateEmitter (extra+36) (stepGateRoles extra w))
        (clearRegisters (stepOutputs.map w))))

def stepResult (extra : Nat) (w : StepWorkspace extra) (store : Fin (extra+45) → List Bool)
    (literals : List (Nat×Bool)) (terminal : Nat) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store
    (w 24) (List.replicate literals.tail.length true))
    (w 0) (Encoding.sequence literalCodec literals.tail++suffix))
    (w 34) (true::store (w 34)))
    (w 42) ((Encoding.sequence (Encoding.list literalCodec)
      (gateClauses (store (w 34)).length (literals.headD (terminal,true)))).reverse++store (w 42))

theorem gateStep_executes (extra : Nat) (w : StepWorkspace extra)
    (store : Fin (extra+45) → List Bool) (literals : List (Nat×Bool)) (terminal limit : Nat)
    (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence literalCodec literals++suffix)
    (counter : store (w 24)=List.replicate literals.length true)
    (status : store (w 1)=accepted::tail)
    (positive : store (w 32)=literalCodec.encode (terminal,true))
    (negative : store (w 33)=literalCodec.encode (terminal,false))
    (empty : ∀ i∈stepScratch,store (w i)=[])
    (bounded : ∀ i : Fin 6,
      (literalCodec.encode (gateSource (store (w 34)).length (literals.headD (terminal,true)) i)).length≤limit) :
    ∃ time ≤ 1000*((store (w 0)).length+(store (w 32)).length+(store (w 33)).length+limit+(store (w 34)).length+2)^2,
      Executes (gateStep extra w) store time (stepResult extra w store literals terminal suffix) := by
  let current := (store (w 34)).length
  let atom := literals.headD (terminal,true)
  let s0 := Function.update (Function.update (Function.update (Function.update store
    (w 24) (List.replicate literals.tail.length true))
    (w 0) (Encoding.sequence literalCodec literals.tail++suffix))
    (w 30) (literalCodec.encode atom)) (w 31) (literalCodec.encode (atom.1,!atom.2))
  obtain ⟨t0,b0,r0⟩ := optionalAtom_executes (extra+11) (stepOptionalRoles extra w) store literals terminal accepted suffix tail
    source counter status positive negative (by
      intro i member
      have inside : Fin.castLE (by decide : 34≤45) i∈stepScratch := by
        simp only [optionalScratch,List.mem_cons,List.not_mem_nil] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h <;> simp_all [stepScratch]
      exact empty _ inside)
  change Executes _ store t0 s0 at r0
  obtain ⟨t1,b1,r1⟩ := freshPair_executes (extra+37) (stepFreshRoles extra w) s0
    (by simp [stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,empty 39 (by decide)])
    (by simp [stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,empty 40 (by decide)])
    (by simp [stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,empty 41 (by decide)])
  let s1 := freshResult (extra+37) (stepFreshRoles extra w) s0
  have codes (i : Fin 6) : s1 (stepGateRoles extra w (Fin.castLE (by decide) i))=literalCodec.encode (gateSource current atom i) := by
    fin_cases i <;> simp [s1,freshResult,stepGateRoles,stepGatePositions,stepFreshRoles,stepFreshPositions,s0,
      w.injective.eq_iff,gateSource,current,literalCodec,empty 35 (by decide),empty 36 (by decide),empty 37 (by decide),empty 38 (by decide)]
  obtain ⟨t2,b2,r2⟩ := gateEmitter_executes (extra+36) (stepGateRoles extra w) s1 current atom limit codes bounded
    (by simp [s1,freshResult,stepGateRoles,stepGatePositions,stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,empty 43 (by decide)])
    (by simp [s1,freshResult,stepGateRoles,stepGatePositions,stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,empty 44 (by decide)])
  let word := (Encoding.sequence (Encoding.list literalCodec) (gateClauses current atom)).reverse
  let s2 := Function.update s1 (w 42) (word++s1 (w 42))
  change Executes _ s1 t2 s2 at r2
  have selectedBound (r : Fin (extra+45)) (member : r∈stepOutputs.map w) : (s2 r).length≤limit := by
    obtain ⟨i,inList,equalR⟩ := List.mem_map.mp member
    rw [←equalR]
    obtain ⟨j,equal⟩ := stepOutputs_covered i inList
    have different : i≠42 := (stepOutputs_different i inList).2.2.2.1
    change (Function.update s1 (w 42) (word++s1 (w 42)) (w i)).length≤limit
    rw [Function.update_of_ne (w.injective.ne different),←equal]
    change (s1 (stepGateRoles extra w (Fin.castLE (by decide) j))).length≤limit
    rw [codes]
    exact bounded j
  obtain ⟨t3,b3,r3⟩ := clearRegisters_selected_executes (stepOutputs.map w) s2 limit selectedBound
  have finalStore : clearedStore (stepOutputs.map w) s2=stepResult extra w store literals terminal suffix := by
    funext r
    by_cases selected : r∈stepOutputs.map w
    · obtain ⟨i,member,equal⟩ := List.mem_map.mp selected
      have mapped : w i∈stepOutputs.map w := List.mem_map.mpr ⟨i,member,rfl⟩
      obtain ⟨a,b,c,d,inside⟩ := stepOutputs_different i member
      rw [←equal]
      simp [clearedStore,mapped,stepResult,w.injective.eq_iff,a,b,c,d,empty i inside]
    · have different (i : Fin 45) (member : i∈stepOutputs) : r≠w i := by
        intro equal;apply selected;rw [equal];exact List.mem_map.mpr ⟨i,member,rfl⟩
      simp only [clearedStore,if_neg selected]
      simp [s2,s1,s0,freshResult,stepFreshRoles,stepFreshPositions,stepResult,word,current,atom,Function.update_apply,
        different 30 (by decide),different 31 (by decide),different 35 (by decide),different 36 (by decide),
        different 37 (by decide),different 38 (by decide),w.injective.eq_iff]
  rw [finalStore] at r3
  have combined := r0.sequence (r1.sequence (r2.sequence r3))
  refine ⟨t0+1+(t1+1+(t2+1+t3)),?_,combined⟩
  have b1as : t1≤100*(current+2)^2 := by
    simpa [stepFreshRoles,stepFreshPositions,s0,w.injective.eq_iff,current] using b1
  change t0≤200*((store (w 0)).length+(store (w 32)).length+(store (w 33)).length+1) at b0
  change t3≤6*(limit+2) at b3
  let S := (store (w 0)).length+(store (w 32)).length+(store (w 33)).length+limit+current+2
  have sq : (current+2)^2≤S^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
  have linear : S≤S^2 := Nat.le_self_pow (by decide : 2≠0) S
  have pos : 1≤S^2 := Nat.one_le_pow 2 S (by dsimp [S];omega)
  have part : (store (w 0)).length+(store (w 32)).length+(store (w 33)).length+1≤S := by dsimp [S];omega
  have lim : limit+2≤S := by dsimp [S];omega
  change _≤1000*S^2
  nlinarith only [b0,b1as,b2,b3,sq,linear,pos,part,lim]

end Counting.External.CNFMachine
