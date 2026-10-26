import BeaconcryptCore.Refinement.RatchetEffectRefinement
import BeaconcryptCore.PanicFreedom.Bytes

/-! A fixed pure KDF interpreter determines the chain and material functions used by the existing ideal ratchet. Every response is decoded by the extracted byte partition, whose unconditional totality supplies the chosen value. The supplied AEAD operations and correctness law are preserved. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

/-- A pure fixed-length response oracle, applied only to the core-owned request. -/
abbrev KdfInterpreter := SymmetricRatchetKdfRequest → RatchetKdfResponse

/-- The request always contains the current chain bytes and the production ratchet label. -/
def interpretedResponse (execute : KdfInterpreter) (chain : RatchetChain) : RatchetKdfResponse :=
  execute { input := chain.bytes, info := SYM_RATCHET_INFO }

/-- Decode the interpreter's response using the extracted, unconditionally total parser. -/
noncomputable def interpretedStep (execute : KdfInterpreter) (chain : RatchetChain) :
    refined.RatchetStep RatchetChain RatchetMaterial :=
  (BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok (interpretedResponse execute chain)).choose

theorem interpretedStep_spec (execute : KdfInterpreter) (chain : RatchetChain) :
    ratchet_step_from_response (interpretedResponse execute chain) = ok (interpretedStep execute chain) :=
  (BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok (interpretedResponse execute chain)).choose_spec

/-- Instantiate the existing model's KDF fields with one fixed interpreter, retaining its AEAD fields. -/
noncomputable def withInterpreter {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter) :
    Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT :=
  { cr with
    kdfChain := fun chain => (interpretedStep execute chain).chain
    kdfMsg := fun chain => (interpretedStep execute chain).material }

/-- Primitive-response refinement follows from decoding, without an assumed successful execution equation. -/
theorem interpretedResponse_refines {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (chain : RatchetChain) :
    ResponseRefines (withInterpreter cr execute) chain (interpretedResponse execute chain) :=
  interpretedStep_spec execute chain

/-- Request-field invariants suffice to apply the same fixed interpreter to an extracted phase. -/
theorem interpreter_request_refines {AD PT CT : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT) (execute : KdfInterpreter)
    (chain : RatchetChain) (request : SymmetricRatchetKdfRequest)
    (hinput : request.input = chain.bytes) (hinfo : request.info = SYM_RATCHET_INFO) :
    ResponseRefines (withInterpreter cr execute) chain (execute request) := by
  simpa only [interpretedResponse, ← hinput, ← hinfo] using interpretedResponse_refines cr execute chain

end beaconcrypt_core.ratchet.concrete
