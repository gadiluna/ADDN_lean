import Counting.StackAnchorMatrixBank

namespace Counting.StackMachine.AnchorMatrix
set_option maxHeartbeats 2000000
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev emitInput : Routine 48 := sequence (clear 34) (sequence (clear 40) (sequence (clear 41)
  (sequence (clear 45) (sequence (clear 49) (sequence (frameRoutine 47 42 38 39)
    (sequence (move 47 38 22 39) (move 47 22 1 39)))))))

def outputFile (output : List Bool) : Store 48 := fun r=>if r=1 then output else []

/-- Frame the computed unary width and erase every retained input buffer. -/
theorem emitInput_executes (matrix width anchor table previous count leaders : List Bool) :
    Executes emitInput
      (Function.update (bank (AnchorRow.file [] [] anchor matrix [] [] [] [] [])
        table previous [] count [] [] [] leaders) 42 width)
      (anchor.length+table.length+previous.length+count.length+leaders.length+
        17*width.length+6*(Encoding.frame width++matrix).length+30)
      (outputFile (Encoding.frame width++matrix)) := by
  let file (anchor table previous count leaders width matrix output framed : List Bool) : Store 48 :=
    fun r=>if r=34 then anchor else if r=40 then table else if r=41 then previous
      else if r=45 then count else if r=49 then leaders else if r=42 then width
      else if r=22 then matrix else if r=1 then output else if r=38 then framed else []
  let initial := file anchor table previous count leaders width matrix [] []
  have initialEq : initial=Function.update (bank (AnchorRow.file [] [] anchor matrix [] [] [] [] [])
      table previous [] count [] [] [] leaders) 42 width := by
    funext r;fin_cases r <;> simp [initial,file,bank,AnchorRow.file]
  rw [←initialEq]
  have a := clear_executes (34:Fin 50) initial
  let s1 := file [] table previous count leaders width matrix [] []
  have as' : Function.update initial 34 []=s1 := by funext r;fin_cases r <;> simp [initial,s1,file]
  rw [as'] at a
  change Executes _ initial (anchor.length+1) s1 at a
  have b := clear_executes (40:Fin 50) s1
  let s2 := file [] [] previous count leaders width matrix [] []
  have bs : Function.update s1 40 []=s2 := by funext r;fin_cases r <;> simp [s1,s2,file]
  rw [bs] at b
  change Executes _ s1 (table.length+1) s2 at b
  have c := clear_executes (41:Fin 50) s2
  let s3 := file [] [] [] count leaders width matrix [] []
  have cs : Function.update s2 41 []=s3 := by funext r;fin_cases r <;> simp [s2,s3,file]
  rw [cs] at c
  change Executes _ s2 (previous.length+1) s3 at c
  have d := clear_executes (45:Fin 50) s3
  let s4 := file [] [] [] [] leaders width matrix [] []
  have ds : Function.update s3 45 []=s4 := by funext r;fin_cases r <;> simp [s3,s4,file]
  rw [ds] at d
  change Executes _ s3 (count.length+1) s4 at d
  have e := clear_executes (49:Fin 50) s4
  let s5 := file [] [] [] [] [] width matrix [] []
  have es : Function.update s4 49 []=s5 := by funext r;fin_cases r <;> simp [s4,s5,file]
  rw [es] at e
  change Executes _ s4 (leaders.length+1) s5 at e
  have f := frame_executes_updates 47 (42:Fin 50) 38 39 (by decide) (by decide) (by decide) s5 rfl
  let s6 := file [] [] [] [] [] [] matrix [] (Encoding.frame width)
  have fs : Function.update (Function.update s5 42 []) 38 (Encoding.frame (s5 42)++s5 38)=s6 := by
    funext r;fin_cases r <;> simp [s5,s6,file]
  rw [fs] at f
  change Executes _ s5 (5*width.length+4) s6 at f
  have g := move_executes 47 (38:Fin 50) 22 39 (by decide) (by decide) (by decide) s6 rfl
  let s7 := file [] [] [] [] [] [] (Encoding.frame width++matrix) [] []
  have gs : Function.update (Function.update s6 22 (s6 38++s6 22)) 38 []=s7 := by
    funext r;fin_cases r <;> simp [s6,s7,file]
  rw [gs] at g
  change Executes _ s6 (6*(Encoding.frame width).length+4) s7 at g
  have h := move_executes 47 (22:Fin 50) 1 39 (by decide) (by decide) (by decide) s7 rfl
  have hs : Function.update (Function.update s7 1 (s7 22++s7 1)) 22 []=outputFile (Encoding.frame width++matrix) := by
    funext r;fin_cases r <;> simp [s7,file,outputFile]
  rw [hs] at h
  change Executes _ s7 (6*(Encoding.frame width++matrix).length+4) _ at h
  have composed := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence (g.sequence h))))))
  convert composed using 1
  rw [Encoding.frame_length]
  omega

end Counting.StackMachine.AnchorMatrix
