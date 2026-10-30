import Counting.HardnessNetworkMachineLayout

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def buildNetwork : Routine 94 :=
  sequence (relocate HardnessNetworkDimensions.routine dimensionRoles)
    (sequence (emitLeaderRow 56 leaderRoles)
      (sequence (emitPathMatrix 80 pathRoles)
        (sequence (emitStarMatrix 80 starRoles)
          (sequence (emitNetworkSerialization 87 serializationRoles) finishNetwork))))

def buildNetworkCost (q : Nat) (coefficients : List Nat) :=
  let B:=q+3
  let N:=networkOrder B coefficients
  let leaderLength:=((Encoding.list Encoding.natural).encode (leaderRow B coefficients)).length
  let pathLength:=((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix B coefficients)).length
  let starLength:=((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix B coefficients)).length
  HardnessNetworkDimensions.cost q coefficients.tail.length+
    leaderRowCost ((Encoding.list Encoding.natural).encode coefficients).length N B coefficients.tail.length+
    pathCost N leaderLength B coefficients.tail.length+starCost N leaderLength+
    serializationCost N B pathLength starLength+2*(networkWord B coefficients).length+9

/-- Build the entire matrix-encoded network from its computed coefficient
list and explicit q/m counters. The implementation has only finite stack
instructions; all network buffers are private to this concrete reduction. -/
theorem buildNetwork_executes (store : Store 94) (q first : Nat) (rest : List Nat)
    (source : store 0=(Encoding.list Encoding.natural).encode (first::rest))
    (status : store 1=[true]) (qValue : store 27=List.replicate q true)
    (countValue : store 25=List.replicate rest.length true)
    (empty : ∀ i∈networkScratch,store i=[]) :
    ∃ time ≤ buildNetworkCost q (first::rest),∃ result,
      Executes buildNetwork store time result ∧ result 1=networkWord (q+3) (first::rest) := by
  let B:=q+3
  let N:=networkOrder B (first::rest)
  let leaderCode:=(Encoding.list Encoding.natural).encode (leaderRow B (first::rest))
  let pathCode:=(Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix B (first::rest))
  let starCode:=(Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix B (first::rest))
  let word:=networkWord B (first::rest)
  have dimensions:=HardnessNetworkDimensions.relocated_executes 89 dimensionRoles store q rest.length qValue countValue
    (empty 64 (by simp)) (empty 65 (by simp)) (empty 67 (by simp)) (empty 68 (by simp))
  let dimensioned:=Function.update (Function.update store 64 (List.replicate B true)) 65 (List.replicate N true)
  have dimensionsAs : Executes (relocate HardnessNetworkDimensions.routine dimensionRoles) store
      (HardnessNetworkDimensions.cost q rest.length) dimensioned := by
    simpa [dimensionRoles,dimensioned,N,networkOrder,B] using dimensions
  have leaderEmpty (i : Fin 40) (member : i∈leaderScratch) : dimensioned (leaderRoles i)=[] := by
    fin_cases i <;> simp [leaderScratch,leaderPrepareScratch,leaderBlockScratch] at member ⊢
    all_goals simp [leaderRoles,leaderPositions,dimensioned,empty]
  obtain ⟨leaderTime,leaderBound,leaderRun⟩:=emitLeaderRow_executes 56 leaderRoles dimensioned first rest true [] []
    (by simp [leaderRoles,leaderPositions,dimensioned,source])
    (by simp [leaderRoles,leaderPositions,dimensioned,status])
    (by simp [leaderRoles,leaderPositions,dimensioned,N,networkOrder]) leaderEmpty
  let leadered:=Function.update (Function.update dimensioned 0 []) 66 leaderCode.reverse
  have leaderAs : Executes (emitLeaderRow 56 leaderRoles) dimensioned leaderTime leadered := by
    simpa [leaderRoles,leaderPositions,leadered,dimensioned,leaderCode,empty] using leaderRun
  have pathEmpty (i : Fin 16) (member : i∈pathScratch) : leadered (pathRoles i)=[] := by
    fin_cases i <;> simp [pathScratch] at member ⊢
    all_goals simp [pathRoles,leadered,dimensioned,empty]
  obtain ⟨pathTime,pathBound,pathRun⟩:=emitPathMatrix_executes 80 pathRoles leadered B first rest (by dsimp [B];omega)
    (by simp [pathRoles,leadered,dimensioned,N])
    (by simp [pathRoles,leadered,dimensioned])
    (by simp [pathRoles,leadered,dimensioned,countValue])
    (by simp [pathRoles,leadered,leaderCode]) pathEmpty
  let pathed:=Function.update leadered 69 pathCode.reverse
  have pathAs : Executes (emitPathMatrix 80 pathRoles) leadered pathTime pathed := by
    simpa [pathRoles,leadered,dimensioned,empty,pathed,pathCode] using pathRun
  have starEmpty (i : Fin 16) (member : i∈starScratch) : pathed (starRoles i)=[] := by
    fin_cases i <;> simp [starScratch] at member ⊢
    all_goals simp [starRoles,pathed,leadered,dimensioned,empty]
  obtain ⟨starTime,starBound,starRun⟩:=emitStarMatrix_executes 80 starRoles pathed (leaderRow B (first::rest))
    (by simp [starRoles,pathed,leadered,dimensioned,N,networkOrder])
    (by simp [starRoles,pathed,leadered,leaderCode]) starEmpty
  let starred:=Function.update pathed 79 starCode.reverse
  have starAs : Executes (emitStarMatrix 80 starRoles) pathed starTime starred := by
    simpa [starRoles,pathed,leadered,dimensioned,empty,starred,starCode,starMatrix,N] using starRun
  have serializationEmpty (i : Fin 9) (member : i∈([5,6,7,8] : List (Fin 9))) : starred (serializationRoles i)=[] := by
    fin_cases i <;> simp at member ⊢
    all_goals simp [serializationRoles,starred,pathed,leadered,dimensioned,empty]
  obtain ⟨serialTime,serialBound,serialRun⟩:=emitNetworkSerialization_word 87 serializationRoles starred B (first::rest)
    (by dsimp [B];omega)
    (by simp [serializationRoles,starred,pathed,leadered,dimensioned,N])
    (by simp [serializationRoles,starred,pathed,leadered,dimensioned])
    (by simp [serializationRoles,starred,pathed,pathCode])
    (by simp [serializationRoles,starred,starCode]) serializationEmpty
  let serialized:=Function.update starred 80 word.reverse
  have serialAs : Executes (emitNetworkSerialization 87 serializationRoles) starred serialTime serialized := by
    simpa [serializationRoles,starred,pathed,leadered,dimensioned,empty,serialized,word] using serialRun
  have finishing:=finishNetwork_executes serialized word (by simp [serialized])
    (by simp [serialized,starred,pathed,leadered,dimensioned,status])
  have combined:=dimensionsAs.sequence (leaderAs.sequence (pathAs.sequence (starAs.sequence (serialAs.sequence finishing))))
  refine ⟨_,?_,_,combined,by simp [word,B]⟩
  have l : leaderTime ≤ leaderRowCost ((Encoding.list Encoding.natural).encode (first::rest)).length N B rest.length := by
    simpa [leaderRoles,leaderPositions,dimensioned,source] using leaderBound
  have p : pathTime ≤ pathCost N leaderCode.length B rest.length := by
    simpa [pathRoles,leadered,dimensioned] using pathBound
  have s : starTime ≤ starCost N leaderCode.length := by
    simpa [starRoles,pathed,leadered,dimensioned] using starBound
  have r : serialTime ≤ serializationCost N B pathCode.length starCode.length := by
    simpa [serializationRoles,starred,pathed,leadered,dimensioned] using serialBound
  change _ ≤ HardnessNetworkDimensions.cost q rest.length+
    leaderRowCost ((Encoding.list Encoding.natural).encode (first::rest)).length N B rest.length+
    pathCost N leaderCode.length B rest.length+starCost N leaderCode.length+
    serializationCost N B pathCode.length starCode.length+2*word.length+9
  omega

end Counting.HardnessNetworkMachine
