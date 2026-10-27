import BeaconcryptCore.Computational.PqxdhInitialSourceInitialSecrecy

/-!
One preparation distribution precedes the shared64-byte initializer response and every evolving-chain stage. Completed branches retain their original decision. Pending branches retain the full original source input, directional selection and publication/freshness event. The response is sampled once and supplied consistently to both directions and every repeated initializer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceSampled
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

noncomputable def observe (context : Context extra M P I D K X Response A N S B)
    (response : PqxdhInitialRootLabelService.Response) (stage : Nat) : ProbComp Bool :=
  match context with
  | .inl decision => pure decision
  | .inr input => sourceGame source writer sender route decode input (List.Vector.replicate 32 0) response stage

noncomputable def game (prior : ProbComp (Context extra M P I D K X Response A N S B)) (stage : Nat) : ProbComp Bool := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  observe source writer sender route decode context (RawCtxSelectedInitialConstructor.response64 output) stage

/-- The first evolving-chain endpoint is definitionally the same full source initializer experiment used by the preceding Extract/HMAC reduction. -/
theorem initial (prior : ProbComp (Context extra M P I D K X Response A N S B)) :
    game source writer sender route decode prior 0 =
      PqxdhInitialSourceInitialSecrecy.random source writer sender route decode prior := rfl

end BeaconcryptCore.Computational.PqxdhInitialSourceSampled

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceSampled.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceSampled.initial
