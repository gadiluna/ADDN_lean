import Counting.StackEncodingParserProduct

namespace Counting.StackMachine.EncodingPrograms.VerifiedParser

/-- A bijective change of value representation leaves the concrete parser
unchanged. Both inverse laws are required to preserve the canonical language. -/
def transport {registers : Nat} {source status output : Fin (registers+2)}
    {α β : Type} {codec : Encoding.Codec α}
    (parser : VerifiedParser registers source status output α codec)
    (encode : β → α) (decode : α → β)
    (left : ∀ value,decode (encode value)=value) (right : ∀ value,encode (decode value)=value) :
    VerifiedParser registers source status output β (Encoding.transport codec encode decode left) where
  work := parser.work
  separate := parser.separate
  routine := parser.routine
  effect := parser.effect
  coefficient := parser.coefficient
  exponent := parser.exponent
  suffix_le := parser.suffix_le
  code_le := parser.code_le
  sound input accepted := by
    obtain ⟨value,split,code⟩:=parser.sound input accepted
    refine ⟨decode value,?_,?_⟩ <;> simpa only [Encoding.transport,right] using (by first | exact split | exact code)
  roundtrip value suffix := parser.roundtrip (encode value) suffix
  executes := parser.executes

end Counting.StackMachine.EncodingPrograms.VerifiedParser
