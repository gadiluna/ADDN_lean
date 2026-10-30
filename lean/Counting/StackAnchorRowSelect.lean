import Counting.StackAnchorCoefficient
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.AnchorRow
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The coefficient bank occupies cells 0..33; the persistent row data
are the anchor, reversed stream, selected count and node countdown. -/
def file (input query anchor result level reversed width counter flag : List Bool) : Store 38 :=
  ![input,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],query,result,level,
    [],[],[],[],[],[],[],[],flag,[],anchor,reversed,width,counter,[],[]]

def coefficientRoles : Fin 34 ↪ Fin 40 :=
  ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,by intro a b h;exact Fin.ext (congrArg (fun r:Fin 40=>r.val) h)⟩
def equalityRoles : Fin 6 ↪ Fin 40 := ⟨![23,34,32,1,2,3],by decide⟩

abbrev calculate : Routine 38 := relocate AnchorCoefficient.routine coefficientRoles
abbrev emit : Routine 38 := sequence (frameRoutine 37 22 38 39)
  (sequence (ofProgram (ListPrograms.reverseProgram 38 38 35)) (pushBit 36 true))
abbrev select : Routine 38 := sequence (Compare.preservingEquality 34 equalityRoles)
  (branchRoutine 32 emit (clear 22))
abbrev item : Routine 38 := sequence calculate (sequence select (clear 23))

theorem emit_executes (store : Store 38) (frameEmpty : store 38=[]) (scratchEmpty : store 39=[]) :
    Executes emit store (9*(store 22).length+10)
      (Function.update (Function.update (Function.update store 22 []) 35
        ((Encoding.frame (store 22)).reverse++store 35)) 36 (true::store 36)) := by
  have a := frame_executes_updates 37 (22:Fin 40) 38 39 (by decide) (by decide) (by decide) store scratchEmpty
  let framed := Function.update (Function.update store 22 []) 38 (Encoding.frame (store 22))
  have as' : Function.update (Function.update store 22 []) 38 (Encoding.frame (store 22)++store 38)=framed := by
    simp [framed,frameEmpty]
  rw [as'] at a
  have b := reverse_executes 38 (38:Fin 40) 35 (by decide) framed
  let reversed := Function.update (Function.update store 22 []) 35 ((Encoding.frame (store 22)).reverse++store 35)
  have bs : Function.update (Function.update framed 38 []) 35 ((framed 38).reverse++framed 35)=reversed := by
    funext r
    by_cases a : r=22
    · subst r;simp [framed,reversed]
    · by_cases b : r=35
      · subst r;simp [framed,reversed]
      · by_cases c : r=38
        · subst r;simp [framed,reversed,frameEmpty]
        · simp [framed,reversed,a,b,c]
  rw [bs] at b
  have c := pushBit_executes (36:Fin 40) true reversed
  change Executes _ _ 1 (Function.update reversed 36 (true::store 36)) at c
  have combined := a.sequence (b.sequence c)
  convert combined using 1
  simp only [framed,Function.update_self,Encoding.frame_length]
  omega

theorem select_executes (store : Store 38) (one : store 1=[]) (two : store 2=[])
    (three : store 3=[]) (flag : store 32=[]) (frameEmpty : store 38=[]) (scratchEmpty : store 39=[]) :
    ∃ time ≤ 6*((store 23).length+(store 34).length)+9*(store 22).length+30,
      Executes select store time
        (if store 23=store 34 then
          Function.update (Function.update (Function.update store 22 []) 35
            ((Encoding.frame (store 22)).reverse++store 35)) 36 (true::store 36)
        else Function.update store 22 []) := by
  have compared := Compare.preservingEquality_executes 34 equalityRoles store one two three
  have bounded := Compare.preservingCost_le (store 23) (store 34)
  change Executes _ _ (Compare.preservingCost (store 23) (store 34))
    (Function.update store 32 (decide (store 23=store 34)::store 32)) at compared
  rw [flag] at compared
  have reset (bit : Bool) : Function.update (Function.update store 32 [bit]) 32 []=store := by
    simp only [Function.update_idem,←flag,Function.update_eq_self]
  by_cases equal : store 23=store 34
  · have truth : decide (store 23=store 34)=true := by simp [equal]
    rw [truth] at compared
    have emitted := emit_executes store frameEmpty scratchEmpty
    have branch := branch_executes_true (32:Fin 40) emit (clear 22)
      (Function.update store 32 [true]) _ [] _ (by simp) (by rw [reset];exact emitted)
    have composed := compared.sequence branch
    refine ⟨Compare.preservingCost (store 23) (store 34)+1+(1+(9*(store 22).length+10)),by omega,?_⟩
    simpa only [select,if_pos equal] using composed
  · have falsity : decide (store 23=store 34)=false := by simp [equal]
    rw [falsity] at compared
    have cleared := clear_executes (22:Fin 40) store
    have branch := branch_executes_false (32:Fin 40) emit (clear 22)
      (Function.update store 32 [false]) _ [] _ (by simp) (by rw [reset];exact cleared)
    have composed := compared.sequence branch
    refine ⟨Compare.preservingCost (store 23) (store 34)+1+(1+((store 22).length+1)),by omega,?_⟩
    simpa only [select,if_neg equal] using composed

end Counting.StackMachine.AnchorRow
