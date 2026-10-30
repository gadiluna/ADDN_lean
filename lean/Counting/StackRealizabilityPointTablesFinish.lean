import Counting.StackRealizabilityPointLoop

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def pointTablesFinish : Routine 58 := sequence (ofProgram (ListPrograms.reverseProgram 58 46 48))
  (sequence (ofProgram (ListPrograms.reverseProgram 58 47 49)) (sequence (clear 36) (clear 42)))

theorem pointTablesFinish_executes (nodes : List Executable.Node) (values : List Nat) (target count : Nat)
    (status : List Bool) (data : Fin 18→List Bool) (index leaving deficit : List Bool)
    (e6 : data 6=[]) (e7 : data 7=[]) :
    ∃ time ≤ 2*leaving.length+2*deficit.length+count.size+index.length+7,
      Executes pointTablesFinish
        (pointLoopStore nodes values target count status data index leaving.reverse deficit.reverse []) time
        (pointLoopStore nodes values target 0 status
          (Function.update (Function.update data 6 leaving) 7 deficit) [] [] [] []) := by
  let start := pointLoopStore nodes values target count status data index leaving.reverse deficit.reverse []
  have first := reverse_executes 58 46 48 (by decide) start
  have at46 : start 46=leaving.reverse := by simp [start,pointLoopStore,pointFile,pointLoopData]
  have at48 : start 48=[] := by simp [start,pointLoopStore,pointFile,pointLoopData,e6]
  rw [at46,at48,List.reverse_reverse,List.append_nil,List.length_reverse] at first
  let left := Function.update (Function.update start 46 []) 48 leaving
  have second := reverse_executes 58 47 49 (by decide) left
  have at47 : left 47=deficit.reverse := by simp [left,start,pointLoopStore,pointFile,pointLoopData]
  have at49 : left 49=[] := by simp [left,start,pointLoopStore,pointFile,pointLoopData,e7]
  rw [at47,at49,List.reverse_reverse,List.append_nil,List.length_reverse] at second
  let both := Function.update (Function.update left 47 []) 49 deficit
  have query := clear_executes (36:Fin 60) both
  have at36 : both 36=count.bits := by simp [both,left,start,pointLoopStore,pointFile,massFile]
  rw [at36,Encoding.bits_length] at query
  let noQuery := Function.update both 36 []
  have clearing := clear_executes (42:Fin 60) noQuery
  have at42 : noQuery 42=index := by simp [noQuery,both,left,start,pointLoopStore,pointFile,pointLoopData]
  rw [at42] at clearing
  have final : Function.update noQuery 42 []=
      pointLoopStore nodes values target 0 status
        (Function.update (Function.update data 6 leaving) 7 deficit) [] [] [] [] := by
    funext r
    fin_cases r <;> simp [noQuery,both,left,start,pointLoopStore,pointFile,pointLoopData,massFile]
  rw [final] at clearing
  exact ⟨_,by omega,first.sequence (second.sequence (query.sequence clearing))⟩

end Counting.StackMachine.RealizabilityCheck
