-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentSource

/-! Actual raw parsing of a native environment command introduces no ongoing record request. Both ML and Ed creation pins, invalid parsing, moved build cancellation and failed response parsing remain in the literal frontend AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRaw
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenEnvironmentCaps (IsRecord typed_zero)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationNativePublicFrontend.handler

noncomputable def frontend (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeInterface.Spec (RegistrationNativePublicFrontend.M n KemSK source) :=
  (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) ∘ₛ
    RegistrationNativeRawAdapter.adapter wire

/-- Every actual raw environment command is structurally closed under the restricted thin backend. -/
theorem raw_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : RegistrationNativePublicFrontend.State source) :
    ((frontend (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey (.inr query.val)).run before).IsQueryBoundP IsRecord 0 := by
  rcases query with ⟨command, environment⟩
  cases command with
  | create edPin mlPin keyId =>
      simp only [frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases edParsed : PqxdhDeploymentInterface.parsePin edPin <;>
        cases mlParsed : RegistrationNativeWire.parseMldsaPin mlPin
      all_goals simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure, simulateQ_map,
        simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
      apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey
      trivial
  | accept raw =>
      simp only [frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter]
      cases parsed : RegistrationNativeWire.readInit wire raw
      · simp only [simulateQ_pure, StateT.run_pure, isQueryBoundP_pure]
      · simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
        apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey
        trivial
  | bundle owner | build handle application | finish owner raw | hmac key bytes =>
      simp only [frontend, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, isQueryBoundP_map_iff]
      apply typed_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey
      trivial
  | hash bytes | serverSend keyId bytes | serverRaw raw | beaconSend owner bytes | beaconRaw owner raw =>
      exact environment.elim

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRaw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRaw.raw_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRaw.raw_zero
