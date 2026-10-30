import Counting.ExternalSATLiteralRead

namespace Counting.External.ParserGuard
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

variable {α : Type} {codec : Encoding.Codec α}
variable (parser : VerifiedParser 15 0 1 2 α codec)

def satRawParser (extra : Nat) (w : SATWorkspace extra) := parser.relabel (satParserRoles extra w)

def guardPrepare (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 28) (w 3)))
    (sequence (satRawParser parser extra w).routine
      (sequence (ofProgram (Compare.equalityProgram (extra+30) (w 0) (w 29) (w 1)))
        (sequence (ofProgram (combineFlagsProgram (extra+30) (w 1)))
          (sequence (clear (w 2))
            (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 28) (w 0) (w 3))) (clear (w 28)))))))

def guardCoefficient := 2*parser.coefficient+40

theorem guardPrepare_executes (exponentBound : parser.exponent ≤ 4) (extra : Nat) (w : SATWorkspace extra) (store : Fin (extra+32) → List Bool)
    (accepted : Bool) (tail : List Bool) (status : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 32,i≠0 → i≠1 → i≠17 → store (w i)=[]) :
    ∃ time ≤ guardCoefficient parser*((store (w 0)).length+1)^4,
      Executes (guardPrepare parser extra w) store time
        (Function.update store (w 1) ((accepted && parser.exactEffect (store (w 0)))::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let input := store (w 0)
  let effect := parser.effect input
  let copied := Function.update store (w 28) input
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 28) (w 3)))
      store (5*input.length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,copied,input,empty 28 (by decide) (by decide) (by decide),List.append_nil] using
      copy_executes (extra+29) (w 0) (w 28) (w 3) (ne 0 28 (by decide)) (ne 0 3 (by decide))
        (ne 28 3 (by decide)) store (empty 3 (by decide) (by decide) (by decide))
  have workEmpty (r : Fin (extra+32)) (member : r∈(satRawParser parser extra w).work) : copied r=[] := by
    change r ∈ parser.work.map (satParserRoles extra w) at member
    obtain ⟨i,hi,hr⟩ := Finset.mem_map.mp member
    subst r
    obtain ⟨isource,iflag,ioutput⟩ := parser.separate i hi
    have castNe0 : (Fin.castLE (by omega) i : Fin 32)≠0 := by intro same;apply isource;exact Fin.ext (congrArg (fun x:Fin 32=>x.val) same)
    have castNe1 : (Fin.castLE (by omega) i : Fin 32)≠1 := by intro same;apply iflag;exact Fin.ext (congrArg (fun x:Fin 32=>x.val) same)
    have castNe17 : (Fin.castLE (by omega) i : Fin 32)≠17 := by intro same;have e:=congrArg (fun x:Fin 32=>x.val) same;have h:=i.isLt;dsimp at e;omega
    have castNe28 : (Fin.castLE (by omega) i : Fin 32)≠28 := by intro same;have e:=congrArg (fun x:Fin 32=>x.val) same;have h:=i.isLt;dsimp at e;omega
    simpa only [copied,satParserRoles,Function.Embedding.coeFn_mk,Function.update_of_ne (ne _ 28 castNe28)] using
      empty (Fin.castLE (by omega) i) castNe0 castNe1 castNe17
  obtain ⟨parseTime,parseBound,parseRun⟩ := (satRawParser parser extra w).executes copied accepted tail
    (by change copied (w 1)=accepted::tail; simp [copied,w.injective.eq_iff,status]) workEmpty
  have copiedInput : copied ((satParserRoles extra w) 0)=input := by simp [copied,satParserRoles,w.injective.eq_iff,input]
  rw [copiedInput] at parseBound parseRun
  let parsed := parseStore (w 0) (w 1) (w 2) copied accepted tail effect
  change Executes (satRawParser parser extra w).routine copied parseTime parsed at parseRun
  have parsedSource : parsed (w 0)=effect.suffix := by simp [parsed,parseStore]
  have parsedFlag : parsed (w 1)=(accepted && effect.accepted)::tail := by simp [parsed,parseStore,w.injective.eq_iff]
  have parsedEmpty : parsed (w 29)=[] := by simp [parsed,parseStore,copied,w.injective.eq_iff,empty]
  have comparing := Compare.equality_executes (extra+30) (w 0) (w 29) (w 1)
    (ne 0 29 (by decide)) (ne 0 1 (by decide)) (ne 29 1 (by decide)) parsed
  rw [parsedSource,parsedEmpty,parsedFlag] at comparing
  let compared := Function.update (Function.update (Function.update parsed (w 0) []) (w 29) [])
    (w 1) (decide (effect.suffix=[])::(accepted && effect.accepted)::tail)
  let joined := Function.update compared (w 1) (((accepted && effect.accepted) && decide (effect.suffix=[]))::tail)
  have combining := combineFlags_executes (extra+30) (w 1) compared (accepted && effect.accepted)
    (decide (effect.suffix=[])) tail (by simp [compared])
  have clearingCode := clear_executes (w 2) joined
  have parsedCode : joined (w 2)=effect.code.reverse := by
    simp [joined,compared,parsed,parseStore,copied,w.injective.eq_iff,empty]
  rw [parsedCode,List.length_reverse] at clearingCode
  let cleared := Function.update joined (w 2) []
  have restoring := copy_executes (extra+29) (w 28) (w 0) (w 3)
    (ne 28 0 (by decide)) (ne 28 3 (by decide)) (ne 0 3 (by decide)) cleared
    (by simp [cleared,joined,compared,parsed,parseStore,copied,w.injective.eq_iff,empty])
  have saved : cleared (w 28)=input := by simp [cleared,joined,compared,parsed,parseStore,copied,w.injective.eq_iff]
  have clearSource : cleared (w 0)=[] := by simp [cleared,joined,compared,w.injective.eq_iff]
  rw [saved,clearSource,List.append_nil] at restoring
  let restored := Function.update cleared (w 0) input
  have clearingInput := clear_executes (w 28) restored
  have savedAgain : restored (w 28)=input := by simp only [restored,Function.update_of_ne (ne 28 0 (by decide)),saved]
  rw [savedAgain] at clearingInput
  have finalStore : Function.update restored (w 28) []=
      Function.update store (w 1) ((accepted && parser.exactEffect input)::tail) := by
    funext r
    by_cases a : r=w 28
    · subst r;simp [w.injective.eq_iff,empty]
    · by_cases b : r=w 0
      · subst r;simp [restored,w.injective.eq_iff,input]
      · by_cases c : r=w 2
        · subst r;simp [restored,cleared,w.injective.eq_iff,empty]
        · by_cases d : r=w 29
          · subst r;simp [restored,cleared,joined,compared,w.injective.eq_iff,empty]
          · by_cases e : r=w 1
            · subst r;simp [restored,cleared,joined,w.injective.eq_iff,VerifiedParser.exactEffect,effect,Bool.and_assoc]
            · simp [restored,cleared,joined,compared,parsed,parseStore,copied,a,b,c,d,e]
  rw [finalStore] at clearingInput
  have combined := copying.sequence (parseRun.sequence (comparing.sequence (combining.sequence
    (clearingCode.sequence (restoring.sequence clearingInput)))))
  refine ⟨5*input.length+2+1+(parseTime+1+(Compare.equalityCost effect.suffix []+1+(3+1+
    (effect.code.length+1+1+(5*input.length+2+1+(input.length+1)))))),?_,combined⟩
  have codeBound := parser.code_le input
  have suffixBound := parser.suffix_le input
  have compareBound := Compare.equalityCost_le effect.suffix []
  have powered : (input.length+1)^parser.exponent ≤ (input.length+1)^4 :=
    Nat.pow_le_pow_right (by omega) exponentBound
  change parseTime≤parser.coefficient*(input.length+1)^parser.exponent at parseBound
  change effect.code.length≤parser.coefficient*(input.length+1)^parser.exponent at codeBound
  have parseLarge := parseBound.trans (Nat.mul_le_mul_left parser.coefficient powered)
  have codeLarge := codeBound.trans (Nat.mul_le_mul_left parser.coefficient powered)
  change effect.suffix.length ≤ input.length at suffixBound
  have linear : input.length+1≤(input.length+1)^4 := Nat.le_self_pow (by decide) _
  simp only [List.length_nil] at compareBound
  change _≤guardCoefficient parser*(input.length+1)^4
  unfold guardCoefficient
  nlinarith

end Counting.External.ParserGuard
