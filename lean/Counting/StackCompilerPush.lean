import Counting.StackCompilerScan

namespace Counting.StackMachine.Compiler
open Machine

def paddedEntry {program : StackMachine.Program} (config : StackMachine.Config program) (padding : Nat) :
    Configuration program :=
  ⟨entry config.control, ⟨[], .mark, config.encoded.tail ++ List.replicate padding .blank⟩⟩

theorem paddedEntry_tape {program : StackMachine.Program} (config : StackMachine.Config program)
    (padding : Nat) : (paddedEntry config padding).tape.denotes = (atEntry config).tape.denotes := by
  have same : Turing.ListBlank.mk (config.encoded.tail ++ List.replicate padding .blank) =
      Turing.ListBlank.mk config.encoded.tail := by
    symm
    apply Quotient.sound
    exact Or.inl ⟨padding,rfl⟩
  simp only [paddedEntry, atEntry, StackMachine.Config.encoded, Tape.ofWord, List.headD_cons,
    List.tail_cons, Tape.denotes] at same ⊢
  rw [same]

theorem push_run {program : StackMachine.Program} (config : StackMachine.Config program)
    (register : Register program) (bit : Bool) (next : StackMachine.Control program)
    (instruction : program.code config.control = .push register bit next) :
    let initialPart := before config.store register
    let suffix := block (config.store register)++after config.store register
    let content := initialPart++bitSymbol bit::suffix
    run (transition program)
      (initialPart.length+1 + (1 + (2*(suffix.length+1) + (1+(content.length+2)))))
      (atEntry config) =
      some (paddedEntry (⟨next, Function.update config.store register (bit::config.store register)⟩ : StackMachine.Config program) 1) := by
  dsimp only
  let initialPart := before config.store register
  let suffix := block (config.store register)++after config.store register
  let content := initialPart++bitSymbol bit::suffix
  change run (transition program) (initialPart.length+1 + (1 + (2*(suffix.length+1) + (1+(content.length+2)))))
    (atEntry config) = _
  have scanned := to_register config register (by simp only [code,entry,instruction])
  have launch : transition program (atRegister config register) =
      some ⟨insert next (StackShift.carryState (bitSymbol bit)),
        (StackShift.insertionStart (bitSymbol bit) (initialPart.reverse++[.mark]) suffix).tape⟩ := by
    simp only [transition, FiniteControl.step, atRegister, code, scan, oneCounter,
      StackScan.scanProgram, Nat.le_refl, if_pos, instruction, Option.map_some]
    rfl
  dsimp only [StackShift.insertionStart] at launch
  have nonblank : ∀ symbol ∈ suffix, symbol ≠ .blank := by
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · exact block_ne_blank _ symbol member
    · exact blocks_ne_blank _ symbol member
  have inserted := FiniteControl.embed_run (code program) StackShift.insertionProgram
    (insert next) (fun phase symbol target action => insert_instruction program next phase target symbol action)
    _ (StackShift.insert_bit_run bit (initialPart.reverse++[.mark]) suffix nonblank)
  dsimp only [StackShift.insertionStart, StackShift.insertionEnd] at inserted
  have rewind : transition program
      ⟨insert next 0, ⟨suffix.reverse++bitSymbol bit::(initialPart.reverse++[.mark]),.blank,[]⟩⟩ =
      some ⟨returning next, ⟨content.reverse++[.mark],.blank,[]⟩⟩ := by
    change some (⟨returning next,
      ⟨suffix.reverse++bitSymbol bit::(initialPart.reverse++[.mark]),.blank,[]⟩⟩ : Configuration program) = _
    congr 3
    simp [content, List.reverse_append, List.append_assoc]
  have noMark : ∀ symbol ∈ content, symbol ≠ .mark := by
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · exact blocks_ne_mark _ symbol member
    · rcases List.mem_cons.mp member with rfl | member
      · cases bit <;> decide
      · rcases List.mem_append.mp member with member | member
        · exact block_ne_mark _ symbol member
        · exact blocks_ne_mark _ symbol member
  have returned := return_content_finish program next content noMark
  have final : (⟨entry next, ⟨[],.mark,content++[.blank]⟩⟩ : Configuration program) =
      paddedEntry (⟨next,Function.update config.store register (bit::config.store register)⟩ : StackMachine.Config program) 1 := by
    simp only [paddedEntry, encoded_update, block, List.map_cons, List.cons_append, List.tail_cons,
      List.replicate_succ, List.replicate_zero]
    simp only [content, initialPart, suffix, block, List.append_assoc, List.cons_append]
  rw [run_add, scanned, Option.bind_some, Nat.one_add, run, launch, Option.bind_some,
    run_add, inserted, Option.bind_some, Nat.one_add, run]
  change (transition program ⟨insert next 0,
    ⟨suffix.reverse++bitSymbol bit::(initialPart.reverse++[.mark]),.blank,[]⟩⟩).bind _ = _
  rw [rewind, Option.bind_some, returned, final]

end Counting.StackMachine.Compiler
