-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundGate

/-! A concrete key-schedule hybrid for the actual native Server completion: current-pin/application/allocation gate, real initial64 and ongoing76 callbacks, bound-AD raw sealing, shared commitment, response hash, actual optional ML signing, width admission and dynamic native publication. The complete later experiment is inside each explicit primitive reduction. The selected PRK is uniform after the related-root hop; this theorem does not itself replace the global related-root/KEM game or assign adaptive root-family slots. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyBound
open PqxdhSecretInputKdf PqxdhServerAuthKeySchedule
variable {Encoded Auxiliary : Type}

/-- Side information is sampled before the selected PRK, including the complete actual entry cache and earlier signing receipts. -/
structure Context (Auxiliary : Type) where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  availability : pqxdh.KeyIdAvailability
  agreement : RegistrationBoundGate.PublicAgreement
  application : Slice U8
  auxiliary : Auxiliary
  primitive : RegistrationSigningShared.State

/-- The real optional ML reply and actual encoder run on the reached native hash capability; all earlier native failures remain failures. -/
noncomputable def publish
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) :
    StateT RegistrationSigningShared.State ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded)) :=
  match record with
  | .ok (.Ok pending) => simulateQ (RegistrationSigningShared.implementation sign)
      (RegistrationWorldServerPublication.program encode pending)
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Actual source completion, with both KDF calls still present, followed by the actual shared-cache response publication. -/
noncomputable def native (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (context : Context Auxiliary) (root : RootOutput) :
    ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) := do
  let record ← (RegistrationServerRecordExecutor.execute source writer context.control context.pin
    context.availability (RegistrationBoundGate.atRoot context.agreement root) context.application).run context.primitive
  (publish sign encode record.1).run record.2

/-- The same native admission and publication at a supplied complete output; the descriptor contains no selected root chain. -/
noncomputable def factored (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (context : Context Auxiliary) (output : Output) :
    ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) := do
  let record ← (simulateQ (RegistrationRecordPrimitives.implementation source writer)
    (RegistrationBoundGate.factored context.control context.pin context.availability context.agreement context.application output)).run
      context.primitive
  (publish sign encode record.1).run record.2

/-- This source-program equality is derived from the actual native gates and real64/76 callbacks, without a supplied simulation or successful-publication premise. -/
theorem native_factored (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (context : Context Auxiliary) (root : RootOutput) :
    native source writer sign encode context root = factored source writer sign encode context (fromRoot source root) := by
  simp only [native, factored, RegistrationBoundGate.source_execute]

/-- Any complete concrete later experiment is included in the constructed reductions. -/
noncomputable def trial (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (post : Context Auxiliary → (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) → ProbComp Bool)
    (context : Context Auxiliary) : Distinguisher := fun output => do
  let completed ← factored source writer sign encode context output
  post context completed

noncomputable def realGame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (sample : ProbComp (Context Auxiliary))
    (post : Context Auxiliary → (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) → ProbComp Bool) :
    ProbComp Bool := do
  let context ← sample
  let prk ← $ᵗ HmacBlock
  let completed ← native source writer sign encode context (expandRoot hmac prk)
  post context completed

noncomputable def idealGame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (sample : ProbComp (Context Auxiliary))
    (post : Context Auxiliary → (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) → ProbComp Bool) :
    ProbComp Bool := do
  let context ← sample
  let material ← $ᵗ PqxdhDeploymentHiddenLayout.Material
  let seed ← $ᵗ PqxdhRecordLiftSeed.Seed
  trial source writer sign encode post context (PqxdhDeploymentHiddenLayout.joinOutput material seed)

/-- The complete actual native Server post-root source, including all pin/allocator/signature/encoder failures and its real shared cache, has the existing five explicit key-schedule losses to independent position-one material and generated seed. -/
theorem key_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (sample : ProbComp (Context Auxiliary))
    (post : Context Auxiliary → (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationSigningShared.State) → ProbComp Bool) :
    (realGame source hmac writer sign encode sample post).boolDistance
      (idealGame source writer sign encode sample post) ≤
      RegistrationBoundKeySchedule.keyLoss source hmac
        (withContext sample (trial source writer sign encode post)) := by
  have uniform : 𝒟[do let context ← sample
                       let output ← $ᵗ Output
                       trial source writer sign encode post context output] =
      𝒟[idealGame source writer sign encode sample post] := by
    apply evalDist_bind_congr
    intro context
    exact (PqxdhDeploymentHiddenLayout.uniform_split (trial source writer sign encode post context)).evalDist_eq
  have real : realGame source hmac writer sign encode sample post =
      (do let context ← sample
          let prk ← $ᵗ HmacBlock
          trial source writer sign encode post context (keySchedule source hmac prk)) := by
    simp only [realGame, native_factored, trial, keySchedule]
  rw [real, ← advantage_congr rfl uniform]
  exact keySchedule_bound_context source hmac correct sample (trial source writer sign encode post)

end BeaconcryptCore.Computational.RegistrationNativeKeyBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBound.native_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBound.native_factored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyBound.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyBound.key_bound
