-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationCompiler
import BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext
import BeaconcryptCore.Computational.RegistrationNativeResponseIdentity

/-! Actual successful response publication replays the same hash and signing replies in the unchanged Core publisher using a locally proved successful encoding representation. The result is a public data-provenance receipt, not equality of source states or removal of failed writer outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationSupport
variable {I S A B Encoded : Type} {base : OracleSpec I}
abbrev M (S : Type) (base : OracleSpec I) := StateT S (OracleComp base)
def Possible (work : M S base A) (value : A) : Prop := ∃ before after, (value,after) ∈ support (work.run before)
private theorem pure_possible (value actual : A) (possible : Possible (pure value : M S base A) actual) : value=actual := by
  obtain ⟨before,after,supported⟩ := possible
  simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at supported
  exact supported.1.symm
private theorem bind_possible (work : M S base A) (next : A → M S base B) (value : B)
    (possible : Possible (work >>= next) value) : ∃ middle, Possible work middle ∧ Possible (next middle) value := by
  obtain ⟨before,after,supported⟩ := possible
  simp only [StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact ⟨middle.1,⟨before,middle.2,called⟩,⟨middle.2,after,continued⟩⟩
private theorem with_replay {Input : Type} (action : RustM Input)
    (next : Input → M S base (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (old : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (published : registration.PublishedServerResponse Encoded)
    (replay : ∀ value, Possible (next value) (.ok (.Ok published)) → .ok (.Ok published) ∈ support (old value))
    (possible : Possible (RegistrationNativePlatformServerPublication.continueWith action next) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationWorldServerPublication.continueWith action old) := by
  cases action with
  | fail error | div => cases pure_possible _ _ possible
  | ok value => exact replay value possible
private theorem result_replay {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → M S base (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (old : Input → OracleComp RegistrationSigningShared.Spec (RustM (RegistrationWorldServerPublication.Result Encoded)))
    (published : registration.PublishedServerResponse Encoded)
    (replay : ∀ value, Possible (next value) (.ok (.Ok published)) → .ok (.Ok published) ∈ support (old value))
    (possible : Possible (RegistrationNativePlatformServerPublication.continueResult action next) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationWorldServerPublication.continueResult action old) := by
  cases action with
  | fail error | div => cases pure_possible _ _ possible
  | ok reply => cases reply with
    | Err previous => cases pure_possible _ _ possible
    | Ok value => exact replay value possible
variable (impl : QueryImpl RegistrationSigningShared.Spec (M S base))
    (encode : registration.SignedResponseView → M S base (RustM (core.option.Option Encoded)))
    (pureEncode : registration.SignedResponseView → core.option.Option Encoded)
    (encoding : ∀ view bytes, Possible (encode view) (.ok (.Some bytes)) → pureEncode view = .Some bytes)
include encoding
private theorem ready (pending : registration.ServerResponseReady) (published : registration.PublishedServerResponse Encoded)
    (possible : Possible (RegistrationNativePlatformServerPublication.ready encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationWorldServerPublication.ready pureEncode pending) := by
  unfold RegistrationNativePlatformServerPublication.ready RegistrationWorldServerPublication.ready at *
  apply with_replay _ _ _ published _ possible
  intro view called
  obtain ⟨encoded,written,returned⟩ := bind_possible _ _ _ called
  have equal := pure_possible _ _ returned
  cases encoded with
  | fail error | div => cases equal
  | ok optional => cases optional with
    | none =>
      change pending.publish core.option.Option.None = .ok (.Ok published) at equal
      rw [BeaconcryptCore.Refinement.RegistrationPublication.server_publication_refines] at equal
      cases equal
    | some bytes =>
      have output := encoding view bytes written
      rw [output,mem_support_pure_iff]
      exact equal.symm
private theorem signing (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) (published : registration.PublishedServerResponse Encoded)
    (possible : Possible (RegistrationNativePlatformServerPublication.signing impl encode payload digest pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationWorldServerPublication.signing pureEncode payload digest pending) := by
  unfold RegistrationNativePlatformServerPublication.signing RegistrationWorldServerPublication.signing at *
  apply with_replay _ _ _ published _ possible
  intro request called
  obtain ⟨signature,_signed,continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨signature,mem_support_query _ _,?_⟩
  exact result_replay _ _ _ published (fun next supported => ready encode pureEncode encoding next published supported) continued
/-- Every actual successful effectful response publication has its same Core response support using the locally proved encoding representation. Actual failure and common poststate behavior are not identified with the pure controller. -/
theorem program (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (possible : Possible (RegistrationNativePlatformServerPublication.program impl encode pending) (.ok (.Ok published))) :
    .ok (.Ok published) ∈ support (RegistrationWorldServerPublication.program pureEncode pending) := by
  unfold RegistrationNativePlatformServerPublication.program RegistrationWorldServerPublication.program at *
  apply with_replay _ _ _ published _ possible
  intro request called
  obtain ⟨digest,_hashed,continued⟩ := bind_possible _ _ _ called
  rw [mem_support_bind_iff]
  refine ⟨digest,mem_support_query _ _,?_⟩
  exact result_replay _ _ _ published (fun next supported => signing impl encode pureEncode encoding _ digest next published supported) continued
end BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationSupport.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponsePublicationSupport.program
