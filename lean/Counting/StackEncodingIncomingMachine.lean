import Counting.StackEncodingIncomingPrefix
import Counting.StackCompare
import Counting.StackCompilerComplete

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def incomingBoundCanonical : Fin 4 ↪ Fin 20 :=
  ⟨fun i=>![18,1,2,8] i,by decide⟩

def incomingRecognitionRoutine : Routine 18 :=
  sequence (pushBit 1 true)
    (sequence (ofProgram (flaggedProgram 16 0 18 8 1))
      (sequence (ofProgram (combineFlagsProgram 18 1))
        (sequence (canonicalGuard 16 incomingBoundCanonical)
          (sequence (pushBit 19 true)
            (sequence (incomingPrefix 0 (Function.Embedding.refl _))
              (sequence (ofProgram (Compare.equalityProgram 18 0 8 1))
                (ofProgram (combineFlagsProgram 18 1))))))))

def incomingRecognitionProgram : Program := incomingRecognitionRoutine.program

def incomingEncodedCheck (input : List Bool) : Bool :=
  let result:=incomingPrefixResult (unframePayload input) (unframeSuffix input) [] true (itemAccepted input)
  result.accepted && decide (result.suffix=[])

/-- The actual finite program consumes a canonical bound followed by the
canonical list of incoming edges. Every rejection path is time-bounded. -/
theorem incoming_computes : ComputesIn incomingRecognitionProgram
    (fun input=>[incomingEncodedCheck input]) (Complexity.polynomial 2700 3) := by
  intro input
  let base:Store 18:=fun r=>if r=0 then input else []
  let payload:=unframePayload input
  let suffix:=unframeSuffix input
  let ok:=(Encoding.unframe input).isSome
  let s1:=Function.update base 1 [true]
  have r1:=pushBit_executes (registers:=18) 1 true base
  have start1 : Function.update base 1 (true::base 1)=s1 := by simp [s1,base]
  rw [start1] at r1
  obtain ⟨t2,b2,r2⟩:=flagged_executes 16 0 18 8 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s1 (by simp [s1,base])
  rw [flagged_result_updates 16 0 18 8 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s1 (by simp [s1,base])] at r2
  let s2:=Function.update (Function.update (Function.update s1 0 suffix) 18 payload) 1 [ok,true]
  have run2 : Executes (ofProgram (flaggedProgram 16 0 18 8 1)) s1 t2 s2 := by
    simpa [s2,s1,base,suffix,payload,ok] using r2
  have r3:=combineFlags_executes 18 1 s2 true ok [] (by simp [s2])
  let s3:=Function.update s2 1 [ok]
  have run3 : Executes (ofProgram (combineFlagsProgram 18 1)) s2 3 s3 := by simpa only [Bool.true_and] using r3
  have r4:=canonicalGuard_executes 16 incomingBoundCanonical s3 ok [] (by simp [incomingBoundCanonical,s3])
    (by simp [incomingBoundCanonical,s3,s2,s1,base]) (by simp [incomingBoundCanonical,s3,s2,s1,base])
  let s4:=Function.update s3 1 [itemAccepted input]
  have run4 : Executes (canonicalGuard 16 incomingBoundCanonical) s3 (6*payload.length+9) s4 := by
    simpa [incomingBoundCanonical,s3,s2,s1,base,s4,itemAccepted,payload,ok] using r4
  have r5:=pushBit_executes (registers:=18) 19 true s4
  let s5:=Function.update s4 19 [true]
  have run5 : Executes (pushBit 19 true) s4 1 s5 := by simpa [s5,s4,s3,s2,s1,base] using r5
  obtain ⟨t6,b6,r6⟩:=incomingPrefix_executes 0 (Function.Embedding.refl _) s5 (itemAccepted input) true [] []
    (by simp [s5,s4]) (by simp [s5]) (by
      intro i low high
      have n0 : i≠0 := by intro h;subst i;norm_num at low
      have n1 : i≠1 := by intro h;subst i;norm_num at low
      have n18 : i≠18 := by intro h;subst i;norm_num at high
      have n19 : i≠19 := by intro h;subst i;norm_num at high
      simp [s5,s4,s3,s2,s1,base,n0,n1,n18,n19])
  let result:=incomingPrefixResult payload suffix [] true (itemAccepted input)
  let s6:=incomingScanStore 10 (incomingBodyRoles 0 (Function.Embedding.refl _)) s5 [] [] result
  have run6 : Executes (incomingPrefix 0 (Function.Embedding.refl _)) s5 t6 s6 := by
    simpa [s6,result,s5,s4,s3,s2,s1,base,payload,suffix] using r6
  have v0 : s6 0=result.suffix := by simp [s6,incomingScanStore,incomingBodyRoles]
  have v1 : s6 1=[result.accepted] := by simp [s6,incomingScanStore,incomingBodyRoles]
  have v8 : s6 8=[] := by simp [s6,incomingScanStore,incomingBodyRoles,s5,s4,s3,s2,s1,base]
  have r7:=Compare.equality_executes 18 0 8 1 (by decide) (by decide) (by decide) s6
  rw [v0,v1,v8] at r7
  let s7:=Function.update (Function.update (Function.update s6 0 []) 8 []) 1
    [decide (result.suffix=[]),result.accepted]
  have r8:=combineFlags_executes 18 1 s7 result.accepted (decide (result.suffix=[])) [] (by simp [s7])
  have composed:=r1.sequence (run2.sequence (run3.sequence (run4.sequence (run5.sequence (run6.sequence (r7.sequence r8))))))
  obtain ⟨finish,ran,halted,final⟩:=composed
  refine ⟨_,finish,?_,⟨ran,halted⟩,?_⟩
  · have parsed:=unframe_payload_length input
    have suffixBound:=unframe_suffix_length input
    have combinedLength : payload.length+suffix.length≤ input.length := by
      cases h : Encoding.unframe input with
      | none => simp [payload,suffix,unframePayload,unframeSuffix,h]
      | some pair =>
          rcases pair with ⟨p,s⟩
          have split:=Machine.unframe_sound input p s h
          simp only [payload,suffix,unframePayload,unframeSuffix,h,Option.map_some,Option.getD_some]
          rw [split,List.length_append,Encoding.frame_length]
          omega
    have suffixResult:result.suffix.length≤ suffix.length :=
      (scanIncoming_suffix_le payload (listCount suffix) (unframeSuffix suffix) [] true
        (itemAccepted input && listHeaderAccepted suffix)).trans (unframe_suffix_length suffix)
    have compareBound:=Compare.equalityCost_le result.suffix []
    simp only [List.length_nil,Nat.add_zero] at compareBound
    have bodyBound : t6≤2500*(suffix.length+payload.length+1)^3 := by
      simpa [s5,s4,s3,s2,s1,base,suffix,payload] using b6
    have cube : (suffix.length+payload.length+1)^3≤(input.length+1)^3 := Nat.pow_le_pow_left (by omega) 3
    have linear : input.length+1≤(input.length+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
    have parseBound:t2≤3*input.length+4 := by simpa [s1,base] using b2
    change _≤2700*(input.length+1)^3
    nlinarith
  · rw [final]
    rfl

 theorem incoming_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile incomingRecognitionProgram)
      (fun input=>[incomingEncodedCheck input]) (Complexity.polynomial (20*(2700+18+5)^2) 8) :=
  Compiler.computesCleanIn_polynomial 2700 3 incoming_computes

end Counting.StackMachine.EncodingPrograms
