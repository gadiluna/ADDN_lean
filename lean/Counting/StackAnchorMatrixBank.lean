import Counting.StackAnchorRowBounds

namespace Counting.StackMachine.AnchorMatrix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The row machine owns cells 0..39. The matrix pass keeps its source,
previous anchor, saved tail, counts and output outside that workspace. -/
def bank (inner : Store 38) (table previous saved count matrix rows outer leaders : List Bool) : Store 48 :=
  fun r=>if h:r.val<40 then inner ⟨r.val,h⟩ else
    match r.val with
    | 40=>table | 41=>previous | 44=>saved | 45=>count
    | 46=>matrix | 47=>rows | 48=>outer | 49=>leaders | _=>[]

def rowRoles : Fin 40 ↪ Fin 50 :=
  ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,by intro a b h;exact Fin.ext (congrArg (fun r:Fin 50=>r.val) h)⟩

theorem lift_executes (routine : Routine 38) (before after : Store 38) (time : Nat)
    (table previous saved count matrix rows outer leaders : List Bool)
    (ran : Executes routine before time after) :
    Executes (relocate routine rowRoles) (bank before table previous saved count matrix rows outer leaders) time
      (bank after table previous saved count matrix rows outer leaders) := by
  apply relocate_executes_frame routine rowRoles _ _ _ _ time _ _ _ ran
  · funext r;simp [bank,rowRoles,r.isLt]
  · intro r;simp [bank,rowRoles,r.isLt]
  · intro r outside
    have above : ¬r.val<40 := by
      intro below
      exact outside ⟨r.val,below⟩ (Fin.ext rfl)
    simp [bank,above]

abbrev emit : Routine 48 := sequence (frameRoutine 47 22 38 39)
  (sequence (ofProgram (ListPrograms.reverseProgram 48 38 46)) (pushBit 47 true))
abbrev flow : Routine 48 := sequence (move 47 0 44 39)
  (sequence (ofProgram (ListPrograms.copyProgram 47 40 0 39))
    (sequence (ofProgram (ListPrograms.copyProgram 47 45 37 39))
      (sequence (relocate AnchorRow.row rowRoles)
        (sequence (clear 0) (sequence (move 47 44 0 39) emit)))))

theorem emit_executes (store : Store 48) (frameEmpty : store 38=[]) (scratchEmpty : store 39=[]) :
    Executes emit store (9*(store 22).length+10)
      (Function.update (Function.update (Function.update store 22 []) 46
        ((Encoding.frame (store 22)).reverse++store 46)) 47 (true::store 47)) := by
  have a := frame_executes_updates 47 (22:Fin 50) 38 39 (by decide) (by decide) (by decide) store scratchEmpty
  let framed := Function.update (Function.update store 22 []) 38 (Encoding.frame (store 22))
  have as' : Function.update (Function.update store 22 []) 38 (Encoding.frame (store 22)++store 38)=framed := by
    simp [framed,frameEmpty]
  rw [as'] at a
  have b := reverse_executes 48 (38:Fin 50) 46 (by decide) framed
  let reversed := Function.update (Function.update store 22 []) 46 ((Encoding.frame (store 22)).reverse++store 46)
  have bs : Function.update (Function.update framed 38 []) 46 ((framed 38).reverse++framed 46)=reversed := by
    funext r
    by_cases a : r=22
    · subst r;simp [framed,reversed]
    · by_cases b : r=46
      · subst r;simp [framed,reversed]
      · by_cases c : r=38
        · subst r;simp [framed,reversed,frameEmpty]
        · simp [framed,reversed,a,b,c]
  rw [bs] at b
  have c := pushBit_executes (47:Fin 50) true reversed
  change Executes _ _ 1 (Function.update reversed 47 (true::store 47)) at c
  have composed := a.sequence (b.sequence c)
  convert composed using 1
  simp only [framed,Function.update_self,Encoding.frame_length]
  omega

end Counting.StackMachine.AnchorMatrix
