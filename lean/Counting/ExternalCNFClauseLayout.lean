import Counting.ExternalCNFLoop
import Counting.ExternalCNFPrepare
import Counting.ExternalCNFTerminals
import Counting.ExternalSATHeader

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev ClauseWorkspace (extra : Nat) := Fin 52 ↪ Fin (extra+52)
def clauseParserRoles (extra : Nat) (w : ClauseWorkspace extra) : SATWorkspace (extra+20) :=
  (Fin.castLEEmb (by decide : 32≤52)).trans w
def clauseLoopRoles (extra : Nat) (w : ClauseWorkspace extra) : LoopWorkspace (extra+6) :=
  (Fin.castLEEmb (by decide : 46≤52)).trans w

def clausePreparePositions : Fin 11 ↪ Fin 52 := ⟨![34,47,45,49,48,32,33,50,39,40,41],by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def clausePreparationRoles (extra : Nat) (w : ClauseWorkspace extra) : PrepareWorkspace (extra+41) :=
  clausePreparePositions.trans w

def clauseTerminalPositions : Fin 6 ↪ Fin 52 := ⟨![48,33,32,42,43,44],by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def clauseTerminalRoles (extra : Nat) (w : ClauseWorkspace extra) : TripleWorkspace (extra+46) :=
  clauseTerminalPositions.trans w

def generatorClauseScratch : List (Fin 52) :=
  [2,3,4,5,6,9,10,11,12,13,14,18,21,24,30,31,32,33,35,36,37,38,39,40,41,43,44,45,48,49,50]

def generatorClausePrepare (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (readListHeader (extra+35) (satHeaderRoles (extra+20) (clauseParserRoles extra w) 1))
    (prepareClause (extra+41) (clausePreparationRoles extra w))

def clausePrepared (extra : Nat) (w : ClauseWorkspace extra) (store : Fin (extra+52) → List Bool)
    (literals : List (Nat×Bool)) (suffix : List Bool) :=
  let current := (store (w 34)).length
  let width := (store (w 47)).length
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 0) (Encoding.sequence literalCodec literals++suffix)) (w 24) (List.replicate literals.length true))
    (w 45) (store (w 47))) (w 48) (literalCodec.encode (current,true)))
    (w 32) (literalCodec.encode (current+width,true))) (w 33) (literalCodec.encode (current+width,false))

theorem generatorClausePrepare_executes (extra : Nat) (w : ClauseWorkspace extra)
    (store : Fin (extra+52) → List Bool) (literals : List (Nat×Bool)) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list literalCodec).encode literals++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈generatorClauseScratch,store (w i)=[]) :
    ∃ time ≤ 2000*((store (w 0)).length+(store (w 34)).length+(store (w 47)).length+2)^3,
      Executes (generatorClausePrepare extra w) store time (clausePrepared extra w store literals suffix) := by
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles (extra+20) (clauseParserRoles extra w) 1) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,clauseParserRoles,empty,generatorClauseScratch]
  have positive (literal : Nat×Bool) : 0<(literalCodec.encode literal).length := by
    simp [literalCodec,Encoding.product,Encoding.boolean]
  obtain ⟨t0,b0,r0⟩ := readListHeader_canonical (extra+35) (satHeaderRoles (extra+20) (clauseParserRoles extra w) 1)
    store accepted tail status headerEmpty literalCodec positive literals suffix source
  let ready := Function.update (Function.update store (w 0) (Encoding.sequence literalCodec literals++suffix))
    (w 24) (List.replicate literals.length true)
  change Executes _ store t0 ready at r0
  have preparationEmpty (i : Fin 11) (member : i∈([2,3,4,5,6,7,8,9,10] : List (Fin 11))) :
      ready (clausePreparationRoles extra w i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [clausePreparationRoles,clausePreparePositions,ready,w.injective.eq_iff,empty,generatorClauseScratch]
  obtain ⟨t1,b1,r1⟩ := prepareClause_executes (extra+41) (clausePreparationRoles extra w) ready preparationEmpty
  have exactResult : prepareResult (extra+41) (clausePreparationRoles extra w) ready=clausePrepared extra w store literals suffix := by
    simp [prepareResult,clausePreparationRoles,clausePreparePositions,ready,clausePrepared,w.injective.eq_iff,literalCodec]
  rw [exactResult] at r1
  refine ⟨t0+1+t1,?_,r0.sequence r1⟩
  have prepareBound : t1≤150*((store (w 34)).length+(store (w 47)).length+2)^2 := by
    simpa [clausePreparationRoles,clausePreparePositions,ready,w.injective.eq_iff] using b1
  change t0≤1820*((store (w 0)).length+1)^3 at b0
  let S := (store (w 0)).length+(store (w 34)).length+(store (w 47)).length+2
  have initialPow : ((store (w 0)).length+1)^3≤S^3 := Nat.pow_le_pow_left (by dsimp [S];omega) 3
  have preparationPow : ((store (w 34)).length+(store (w 47)).length+2)^2≤S^3 :=
    (Nat.pow_le_pow_left (by dsimp [S];omega) 2).trans (Nat.pow_le_pow_right (by dsimp [S];omega : 1≤S) (by decide))
  have pos : 1≤S^3 := Nat.one_le_pow 3 S (by dsimp [S];omega)
  change _≤2000*S^3
  nlinarith only [b0,prepareBound,initialPow,preparationPow,pos]

end Counting.External.CNFMachine
