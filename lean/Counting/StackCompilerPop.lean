import Counting.StackCompilerPush

namespace Counting.StackMachine.Compiler
open Machine

theorem pop_empty_run {program : StackMachine.Program} (config : StackMachine.Config program)
    (register : Register program) (empty zero one : StackMachine.Control program)
    (instruction : program.code config.control = .pop register empty zero one)
    (contents : config.store register = []) :
    run (transition program) ((before config.store register).length+1 +
      (1+((before config.store register).length+2))) (atEntry config) =
      some (paddedEntry ({config with control := empty}) 0) := by
  let initialPart := before config.store register
  let suffix := after config.store register
  have scanned := to_register config register (by simp only [code,entry,instruction])
  have launch : transition program (atRegister config register) =
      some ⟨returning empty, ⟨initialPart.reverse++[.mark],.separator,suffix⟩⟩ := by
    simp only [transition, FiniteControl.step, atRegister, contents, block, List.map_nil, List.nil_append,
      List.singleton_append, List.headD_cons, List.tail_cons, code, scan, oneCounter,
      StackScan.scanProgram, Nat.le_refl, if_pos, instruction, Option.map_some, Tape.write]
    rfl
  have noMark : ∀ symbol ∈ initialPart.reverse, symbol ≠ .mark := by
    simpa only [List.mem_reverse, initialPart, before] using blocks_ne_mark ((stores config.store).take register.val)
  have returned := return_finish program empty initialPart.reverse .separator suffix noMark (by decide)
  simp only [List.length_reverse, List.reverse_reverse] at returned
  have final : (⟨entry empty,⟨[],.mark,initialPart++ .separator::suffix⟩⟩ : Configuration program) =
      paddedEntry ({config with control := empty}) 0 := by
    have same : ({config with control := empty} : StackMachine.Config program).encoded = config.encoded := rfl
    simp only [paddedEntry, same, encoded_split config register, contents, block, List.map_nil,
      List.nil_append, List.tail_cons, List.replicate_zero, List.append_nil]
    simp only [initialPart, suffix, List.append_assoc, List.singleton_append]
  rw [run_add, scanned, Option.bind_some, Nat.one_add, run, launch, Option.bind_some, returned, final]

theorem pop_bit_run {program : StackMachine.Program} (config : StackMachine.Config program)
    (register : Register program) (empty zero one : StackMachine.Control program)
    (bit : Bool) (rest : List Bool)
    (instruction : program.code config.control = .pop register empty zero one)
    (contents : config.store register = bit::rest) :
    let initialPart := before config.store register
    let suffix := block rest++after config.store register
    let content := initialPart++suffix
    run (transition program)
      (initialPart.length+1 + (1 + (4*(suffix.length+1) + (1+((content++[Symbol.blank]).length+2)))))
      (atEntry config) =
      some (paddedEntry (⟨if bit then one else zero, Function.update config.store register rest⟩ : StackMachine.Config program) 2) := by
  dsimp only
  let initialPart := before config.store register
  let suffix := block rest++after config.store register
  let content := initialPart++suffix
  let next := if bit then one else zero
  change run (transition program) (initialPart.length+1 +
    (1 + (4*(suffix.length+1) + (1+((content++[Symbol.blank]).length+2))))) (atEntry config) = _
  have scanned := to_register config register (by simp only [code,entry,instruction])
  have launch : transition program (atRegister config register) =
      some ⟨delete next 0,⟨initialPart.reverse++[.mark],bitSymbol bit,suffix⟩⟩ := by
    cases bit <;>
      simp [transition, FiniteControl.step, atRegister, contents, block, code, scan, oneCounter,
        StackScan.scanProgram, instruction, bitSymbol, Tape.write, next, initialPart, suffix]
  have nonblank : ∀ symbol ∈ suffix, symbol ≠ Symbol.blank := by
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · exact block_ne_blank _ symbol member
    · exact blocks_ne_blank _ symbol member
  have deleted := FiniteControl.embed_run (code program) StackShift.deletionProgram
    (delete next) (fun phase symbol target action => delete_instruction program next phase target symbol action)
    _ (StackShift.deletion_run (bitSymbol bit) (initialPart.reverse++[.mark]) suffix nonblank)
  dsimp only [StackShift.deletionStart, StackShift.deletionEnd] at deleted
  have deleted' : run (transition program) (4*(suffix.length+1))
      (⟨delete next 0,⟨initialPart.reverse++[.mark],bitSymbol bit,suffix⟩⟩ : Configuration program) =
      some ⟨delete next 9,⟨Symbol.blank::(suffix.reverse++(initialPart.reverse++[.mark])),Symbol.blank,[]⟩⟩ := deleted
  have rewind : transition program
      ⟨delete next 9, ⟨Symbol.blank::(suffix.reverse++(initialPart.reverse++[.mark])),Symbol.blank,[]⟩⟩ =
      some ⟨returning next, ⟨(content++[Symbol.blank]).reverse++[.mark],Symbol.blank,[]⟩⟩ := by
    change some (⟨returning next,
      ⟨Symbol.blank::(suffix.reverse++(initialPart.reverse++[.mark])),Symbol.blank,[]⟩⟩ : Configuration program) = _
    congr 3
    simp [content, List.reverse_append, List.append_assoc]
  have noMark : ∀ symbol ∈ content++[Symbol.blank], symbol ≠ .mark := by
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact blocks_ne_mark _ symbol member
      · rcases List.mem_append.mp member with member | member
        · exact block_ne_mark _ symbol member
        · exact blocks_ne_mark _ symbol member
    · have equal := List.mem_singleton.mp member
      subst symbol
      decide
  have returned := return_content_finish program next (content++[Symbol.blank]) noMark
  have final : (⟨entry next, ⟨[],.mark,(content++[Symbol.blank])++[Symbol.blank]⟩⟩ : Configuration program) =
      paddedEntry (⟨next, Function.update config.store register rest⟩ : StackMachine.Config program) 2 := by
    simp only [paddedEntry, encoded_update, List.tail_cons, List.replicate_succ, List.replicate_zero]
    simp only [content, initialPart, suffix, List.append_assoc, List.singleton_append]
  rw [run_add, scanned, Option.bind_some, Nat.one_add, run, launch, Option.bind_some,
    run_add, deleted', Option.bind_some, Nat.one_add, run]
  change (transition program ⟨delete next 9,
    ⟨Symbol.blank::(suffix.reverse++(initialPart.reverse++[.mark])),Symbol.blank,[]⟩⟩).bind _ = _
  rw [rewind, Option.bind_some, returned, final]

end Counting.StackMachine.Compiler
