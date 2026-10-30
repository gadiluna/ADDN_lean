import Counting.StackRealizabilityBitLookup
import Counting.StackRealizabilityGraphExpr

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def arcReadRoles0 : Fin 7 ↪ Fin 32:=⟨![0,8,12,25,26,27,28],by decide⟩
def arcReadRoles1 : Fin 7 ↪ Fin 32:=⟨![1,8,13,25,26,27,28],by decide⟩
def arcReadRoles2 : Fin 7 ↪ Fin 32:=⟨![2,8,14,25,26,27,28],by decide⟩
def arcReadRoles3 : Fin 7 ↪ Fin 32:=⟨![0,9,15,25,26,27,28],by decide⟩
def arcReadRoles4 : Fin 7 ↪ Fin 32:=⟨![1,9,16,25,26,27,28],by decide⟩
def arcReadRoles5 : Fin 7 ↪ Fin 32:=⟨![2,9,17,25,26,27,28],by decide⟩
def arcReadRoles6 : Fin 7 ↪ Fin 32:=⟨![3,8,18,25,26,27,28],by decide⟩
def arcReadRoles7 : Fin 7 ↪ Fin 32:=⟨![4,8,19,25,26,27,28],by decide⟩
def arcReadRoles8 : Fin 7 ↪ Fin 32:=⟨![4,9,20,25,26,27,28],by decide⟩
def arcReadRoles9 : Fin 7 ↪ Fin 32:=⟨![5,8,21,25,26,27,28],by decide⟩
def arcReadRoles10 : Fin 7 ↪ Fin 32:=⟨![6,10,22,25,26,27,28],by decide⟩
def arcReadRoles11 : Fin 7 ↪ Fin 32:=⟨![7,11,23,25,26,27,28],by decide⟩

def arcReadValues (store : Store 30) : Fin 12 → Bool:=![
  RealizabilityVerifier.BitGraph.bitAt (store 0) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 1) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 2) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 0) (store 9).length,
  RealizabilityVerifier.BitGraph.bitAt (store 1) (store 9).length,
  RealizabilityVerifier.BitGraph.bitAt (store 2) (store 9).length,
  RealizabilityVerifier.BitGraph.bitAt (store 3) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 4) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 4) (store 9).length,
  RealizabilityVerifier.BitGraph.bitAt (store 5) (store 8).length,
  RealizabilityVerifier.BitGraph.bitAt (store 6) (store 10).length,
  RealizabilityVerifier.BitGraph.bitAt (store 7) (store 11).length]

def arcReadSize (store : Store 30) : Nat:=
  (store 0).length+(store 1).length+(store 2).length+(store 3).length+(store 4).length+(store 5).length+(store 6).length+(store 7).length+(store 8).length+(store 9).length+(store 10).length+(store 11).length+1

def arcReadPart0 : Routine 30:=sequence (bitLookup 25 arcReadRoles0)
  (sequence (bitLookup 25 arcReadRoles1) (bitLookup 25 arcReadRoles2))
def arcReadPartStore0 (store : Store 30) : Store 30:=
  let p1:=Function.update store 12 (arcReadValues store 0::store 12)
  let p2:=Function.update p1 13 (arcReadValues store 1::store 13)
  let p3:=Function.update p2 14 (arcReadValues store 2::store 14)
  p3

theorem arcReadPart0_executes (store : Store 30)
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 100*arcReadSize store, Executes arcReadPart0 store time (arcReadPartStore0 store):=by
  obtain ⟨t0,b0,run0⟩:=bitLookup_executes 25 arcReadRoles0 store
    (by simp [arcReadRoles0,e26]) (by simp [arcReadRoles0,e27])
    (by simp [arcReadRoles0,e28])
  change t0 ≤ 6*(store 0).length+7*(store 8).length+16 at b0
  change Executes (bitLookup 25 arcReadRoles0) store t0
    (Function.update store 12 (RealizabilityVerifier.BitGraph.bitAt (store 0) (store 8).length::store 12)) at run0
  let s1:=Function.update store 12 (RealizabilityVerifier.BitGraph.bitAt (store 0) (store 8).length::store 12)
  obtain ⟨t1,b1,run1⟩:=bitLookup_executes 25 arcReadRoles1 s1
    (by simp [s1,arcReadRoles1,e26]) (by simp [s1,arcReadRoles1,e27])
    (by simp [s1,arcReadRoles1,e28])
  change t1 ≤ 6*(s1 1).length+7*(s1 8).length+16 at b1
  change Executes (bitLookup 25 arcReadRoles1) s1 t1
    (Function.update s1 13 (RealizabilityVerifier.BitGraph.bitAt (s1 1) (s1 8).length::s1 13)) at run1
  have source1 : s1 1=store 1:=by simp [s1]
  have index1 : s1 8=store 8:=by simp [s1]
  have tail1 : s1 13=store 13:=by simp [s1]
  rw [source1,index1] at b1
  rw [source1,index1,tail1] at run1
  let s2:=Function.update s1 13 (RealizabilityVerifier.BitGraph.bitAt (store 1) (store 8).length::store 13)
  obtain ⟨t2,b2,run2⟩:=bitLookup_executes 25 arcReadRoles2 s2
    (by simp [s2,s1,arcReadRoles2,e26]) (by simp [s2,s1,arcReadRoles2,e27])
    (by simp [s2,s1,arcReadRoles2,e28])
  change t2 ≤ 6*(s2 2).length+7*(s2 8).length+16 at b2
  change Executes (bitLookup 25 arcReadRoles2) s2 t2
    (Function.update s2 14 (RealizabilityVerifier.BitGraph.bitAt (s2 2) (s2 8).length::s2 14)) at run2
  have source2 : s2 2=store 2:=by simp [s2,s1]
  have index2 : s2 8=store 8:=by simp [s2,s1]
  have tail2 : s2 14=store 14:=by simp [s2,s1]
  rw [source2,index2] at b2
  rw [source2,index2,tail2] at run2
  let s3:=Function.update s2 14 (RealizabilityVerifier.BitGraph.bitAt (store 2) (store 8).length::store 14)
  have execution : Executes arcReadPart0 store (t0+1+(t1+1+t2)) s3:=run0.sequence (run1.sequence run2)
  exact ⟨_,by dsimp only [arcReadSize];omega,execution⟩

def arcReadPart1 : Routine 30:=sequence (bitLookup 25 arcReadRoles3)
  (sequence (bitLookup 25 arcReadRoles4) (bitLookup 25 arcReadRoles5))
def arcReadPartStore1 (store : Store 30) : Store 30:=
  let p1:=Function.update store 15 (arcReadValues store 3::store 15)
  let p2:=Function.update p1 16 (arcReadValues store 4::store 16)
  let p3:=Function.update p2 17 (arcReadValues store 5::store 17)
  p3

theorem arcReadPart1_executes (store : Store 30)
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 100*arcReadSize store, Executes arcReadPart1 store time (arcReadPartStore1 store):=by
  obtain ⟨t0,b0,run0⟩:=bitLookup_executes 25 arcReadRoles3 store
    (by simp [arcReadRoles3,e26]) (by simp [arcReadRoles3,e27])
    (by simp [arcReadRoles3,e28])
  change t0 ≤ 6*(store 0).length+7*(store 9).length+16 at b0
  change Executes (bitLookup 25 arcReadRoles3) store t0
    (Function.update store 15 (RealizabilityVerifier.BitGraph.bitAt (store 0) (store 9).length::store 15)) at run0
  let s1:=Function.update store 15 (RealizabilityVerifier.BitGraph.bitAt (store 0) (store 9).length::store 15)
  obtain ⟨t1,b1,run1⟩:=bitLookup_executes 25 arcReadRoles4 s1
    (by simp [s1,arcReadRoles4,e26]) (by simp [s1,arcReadRoles4,e27])
    (by simp [s1,arcReadRoles4,e28])
  change t1 ≤ 6*(s1 1).length+7*(s1 9).length+16 at b1
  change Executes (bitLookup 25 arcReadRoles4) s1 t1
    (Function.update s1 16 (RealizabilityVerifier.BitGraph.bitAt (s1 1) (s1 9).length::s1 16)) at run1
  have source1 : s1 1=store 1:=by simp [s1]
  have index1 : s1 9=store 9:=by simp [s1]
  have tail1 : s1 16=store 16:=by simp [s1]
  rw [source1,index1] at b1
  rw [source1,index1,tail1] at run1
  let s2:=Function.update s1 16 (RealizabilityVerifier.BitGraph.bitAt (store 1) (store 9).length::store 16)
  obtain ⟨t2,b2,run2⟩:=bitLookup_executes 25 arcReadRoles5 s2
    (by simp [s2,s1,arcReadRoles5,e26]) (by simp [s2,s1,arcReadRoles5,e27])
    (by simp [s2,s1,arcReadRoles5,e28])
  change t2 ≤ 6*(s2 2).length+7*(s2 9).length+16 at b2
  change Executes (bitLookup 25 arcReadRoles5) s2 t2
    (Function.update s2 17 (RealizabilityVerifier.BitGraph.bitAt (s2 2) (s2 9).length::s2 17)) at run2
  have source2 : s2 2=store 2:=by simp [s2,s1]
  have index2 : s2 9=store 9:=by simp [s2,s1]
  have tail2 : s2 17=store 17:=by simp [s2,s1]
  rw [source2,index2] at b2
  rw [source2,index2,tail2] at run2
  let s3:=Function.update s2 17 (RealizabilityVerifier.BitGraph.bitAt (store 2) (store 9).length::store 17)
  have execution : Executes arcReadPart1 store (t0+1+(t1+1+t2)) s3:=run0.sequence (run1.sequence run2)
  exact ⟨_,by dsimp only [arcReadSize];omega,execution⟩

def arcReadPart2 : Routine 30:=sequence (bitLookup 25 arcReadRoles6)
  (sequence (bitLookup 25 arcReadRoles7) (bitLookup 25 arcReadRoles8))
def arcReadPartStore2 (store : Store 30) : Store 30:=
  let p1:=Function.update store 18 (arcReadValues store 6::store 18)
  let p2:=Function.update p1 19 (arcReadValues store 7::store 19)
  let p3:=Function.update p2 20 (arcReadValues store 8::store 20)
  p3

theorem arcReadPart2_executes (store : Store 30)
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 100*arcReadSize store, Executes arcReadPart2 store time (arcReadPartStore2 store):=by
  obtain ⟨t0,b0,run0⟩:=bitLookup_executes 25 arcReadRoles6 store
    (by simp [arcReadRoles6,e26]) (by simp [arcReadRoles6,e27])
    (by simp [arcReadRoles6,e28])
  change t0 ≤ 6*(store 3).length+7*(store 8).length+16 at b0
  change Executes (bitLookup 25 arcReadRoles6) store t0
    (Function.update store 18 (RealizabilityVerifier.BitGraph.bitAt (store 3) (store 8).length::store 18)) at run0
  let s1:=Function.update store 18 (RealizabilityVerifier.BitGraph.bitAt (store 3) (store 8).length::store 18)
  obtain ⟨t1,b1,run1⟩:=bitLookup_executes 25 arcReadRoles7 s1
    (by simp [s1,arcReadRoles7,e26]) (by simp [s1,arcReadRoles7,e27])
    (by simp [s1,arcReadRoles7,e28])
  change t1 ≤ 6*(s1 4).length+7*(s1 8).length+16 at b1
  change Executes (bitLookup 25 arcReadRoles7) s1 t1
    (Function.update s1 19 (RealizabilityVerifier.BitGraph.bitAt (s1 4) (s1 8).length::s1 19)) at run1
  have source1 : s1 4=store 4:=by simp [s1]
  have index1 : s1 8=store 8:=by simp [s1]
  have tail1 : s1 19=store 19:=by simp [s1]
  rw [source1,index1] at b1
  rw [source1,index1,tail1] at run1
  let s2:=Function.update s1 19 (RealizabilityVerifier.BitGraph.bitAt (store 4) (store 8).length::store 19)
  obtain ⟨t2,b2,run2⟩:=bitLookup_executes 25 arcReadRoles8 s2
    (by simp [s2,s1,arcReadRoles8,e26]) (by simp [s2,s1,arcReadRoles8,e27])
    (by simp [s2,s1,arcReadRoles8,e28])
  change t2 ≤ 6*(s2 4).length+7*(s2 9).length+16 at b2
  change Executes (bitLookup 25 arcReadRoles8) s2 t2
    (Function.update s2 20 (RealizabilityVerifier.BitGraph.bitAt (s2 4) (s2 9).length::s2 20)) at run2
  have source2 : s2 4=store 4:=by simp [s2,s1]
  have index2 : s2 9=store 9:=by simp [s2,s1]
  have tail2 : s2 20=store 20:=by simp [s2,s1]
  rw [source2,index2] at b2
  rw [source2,index2,tail2] at run2
  let s3:=Function.update s2 20 (RealizabilityVerifier.BitGraph.bitAt (store 4) (store 9).length::store 20)
  have execution : Executes arcReadPart2 store (t0+1+(t1+1+t2)) s3:=run0.sequence (run1.sequence run2)
  exact ⟨_,by dsimp only [arcReadSize];omega,execution⟩

def arcReadPart3 : Routine 30:=sequence (bitLookup 25 arcReadRoles9)
  (sequence (bitLookup 25 arcReadRoles10) (bitLookup 25 arcReadRoles11))
def arcReadPartStore3 (store : Store 30) : Store 30:=
  let p1:=Function.update store 21 (arcReadValues store 9::store 21)
  let p2:=Function.update p1 22 (arcReadValues store 10::store 22)
  let p3:=Function.update p2 23 (arcReadValues store 11::store 23)
  p3

theorem arcReadPart3_executes (store : Store 30)
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 100*arcReadSize store, Executes arcReadPart3 store time (arcReadPartStore3 store):=by
  obtain ⟨t0,b0,run0⟩:=bitLookup_executes 25 arcReadRoles9 store
    (by simp [arcReadRoles9,e26]) (by simp [arcReadRoles9,e27])
    (by simp [arcReadRoles9,e28])
  change t0 ≤ 6*(store 5).length+7*(store 8).length+16 at b0
  change Executes (bitLookup 25 arcReadRoles9) store t0
    (Function.update store 21 (RealizabilityVerifier.BitGraph.bitAt (store 5) (store 8).length::store 21)) at run0
  let s1:=Function.update store 21 (RealizabilityVerifier.BitGraph.bitAt (store 5) (store 8).length::store 21)
  obtain ⟨t1,b1,run1⟩:=bitLookup_executes 25 arcReadRoles10 s1
    (by simp [s1,arcReadRoles10,e26]) (by simp [s1,arcReadRoles10,e27])
    (by simp [s1,arcReadRoles10,e28])
  change t1 ≤ 6*(s1 6).length+7*(s1 10).length+16 at b1
  change Executes (bitLookup 25 arcReadRoles10) s1 t1
    (Function.update s1 22 (RealizabilityVerifier.BitGraph.bitAt (s1 6) (s1 10).length::s1 22)) at run1
  have source1 : s1 6=store 6:=by simp [s1]
  have index1 : s1 10=store 10:=by simp [s1]
  have tail1 : s1 22=store 22:=by simp [s1]
  rw [source1,index1] at b1
  rw [source1,index1,tail1] at run1
  let s2:=Function.update s1 22 (RealizabilityVerifier.BitGraph.bitAt (store 6) (store 10).length::store 22)
  obtain ⟨t2,b2,run2⟩:=bitLookup_executes 25 arcReadRoles11 s2
    (by simp [s2,s1,arcReadRoles11,e26]) (by simp [s2,s1,arcReadRoles11,e27])
    (by simp [s2,s1,arcReadRoles11,e28])
  change t2 ≤ 6*(s2 7).length+7*(s2 11).length+16 at b2
  change Executes (bitLookup 25 arcReadRoles11) s2 t2
    (Function.update s2 23 (RealizabilityVerifier.BitGraph.bitAt (s2 7) (s2 11).length::s2 23)) at run2
  have source2 : s2 7=store 7:=by simp [s2,s1]
  have index2 : s2 11=store 11:=by simp [s2,s1]
  have tail2 : s2 23=store 23:=by simp [s2,s1]
  rw [source2,index2] at b2
  rw [source2,index2,tail2] at run2
  let s3:=Function.update s2 23 (RealizabilityVerifier.BitGraph.bitAt (store 7) (store 11).length::store 23)
  have execution : Executes arcReadPart3 store (t0+1+(t1+1+t2)) s3:=run0.sequence (run1.sequence run2)
  exact ⟨_,by dsimp only [arcReadSize];omega,execution⟩

/-- Twelve actual reads are grouped into fixed finite blocks. -/
def arcRead : Routine 30:=sequence arcReadPart0
  (sequence arcReadPart1 (sequence arcReadPart2 arcReadPart3))

def arcReadStore (store : Store 30) : Store 30:=
  fun r=>if h : 12≤r.val ∧ r.val<24 then
    arcReadValues store ⟨r.val-12,by omega⟩::store r else store r

theorem arcRead_executes (store : Store 30)
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 500*arcReadSize store, Executes arcRead store time (arcReadStore store):=by
  obtain ⟨t0,b0,run0⟩:=arcReadPart0_executes store
    (by simp [e26]) (by simp [e27]) (by simp [e28])
  let s1:=arcReadPartStore0 store
  obtain ⟨t1,b1,run1⟩:=arcReadPart1_executes s1
    (by simp [s1,arcReadPartStore0,e26]) (by simp [s1,arcReadPartStore0,e27]) (by simp [s1,arcReadPartStore0,e28])
  have bound1 : arcReadSize s1=arcReadSize store:=by simp [s1,arcReadPartStore0,arcReadSize]
  rw [bound1] at b1
  let s2:=arcReadPartStore1 s1
  obtain ⟨t2,b2,run2⟩:=arcReadPart2_executes s2
    (by simp [s2,s1,arcReadPartStore0,arcReadPartStore1,e26]) (by simp [s2,s1,arcReadPartStore0,arcReadPartStore1,e27]) (by simp [s2,s1,arcReadPartStore0,arcReadPartStore1,e28])
  have bound2 : arcReadSize s2=arcReadSize store:=by simp [s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadSize]
  rw [bound2] at b2
  let s3:=arcReadPartStore2 s2
  obtain ⟨t3,b3,run3⟩:=arcReadPart3_executes s3
    (by simp [s3,s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadPartStore2,e26]) (by simp [s3,s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadPartStore2,e27]) (by simp [s3,s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadPartStore2,e28])
  have bound3 : arcReadSize s3=arcReadSize store:=by simp [s3,s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadPartStore2,arcReadSize]
  rw [bound3] at b3
  let s4:=arcReadPartStore3 s3
  have final : s4=arcReadStore store:=by
    funext r
    fin_cases r <;> simp [s4,s3,s2,s1,arcReadPartStore0,arcReadPartStore1,arcReadPartStore2,arcReadPartStore3,arcReadStore,arcReadValues]
  have execution : Executes arcRead store (t0+1+(t1+1+(t2+1+t3))) s4:=run0.sequence (run1.sequence (run2.sequence run3))
  rw [final] at execution
  have positive : 1≤arcReadSize store:=by unfold arcReadSize;omega
  exact ⟨_,by omega,execution⟩

theorem arcReadStore_flags (store : Store 30) (i : Fin 12) :
    arcReadStore store ⟨12+i.val,by omega⟩=arcReadValues store i::store ⟨12+i.val,by omega⟩:=by
  simp [arcReadStore,show 12+i.val<24 by omega]

end Counting.StackMachine.RealizabilityCheck
