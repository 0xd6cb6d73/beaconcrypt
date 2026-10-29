-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServiceBounds
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend
import BeaconcryptCore.Computational.RegistrationNativePublicInterpreter

/-! The concrete thin native registration client uses the actual shared World effects and original record commands. Its separate state contains only descriptor flags, allocated material44, an opaque KEM pool/provider and the existing auxiliary receipt frame. Hidden record seeds, source kernels and the World/cache state remain outside that state. The actual frontend's CommonCompiler still updates the current chronological environment receipts before resuming. The arbitrary World AST below is the target for the explicit seed-delay, alias and entropy-preamble proofs; defining it does not assert their game equalities. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Provider (KemSK ProviderState : Type) := QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
  (StateT (PqxdhLiveKemBirth.Pool KemSK × ProviderState) ProbComp)

structure State (n : Nat) (KemSK ProviderState : Type) where
  keys : RegistrationNativeHiddenService.State n
  pool : PqxdhLiveKemBirth.Pool KemSK
  provider : ProviderState
  receipts : List RegistrationSigningShared.Receipt

def initial (provider : ProviderState) : State n KemSK ProviderState :=
  ⟨RegistrationNativeHiddenService.initial, PqxdhLiveKemBirth.empty, provider, []⟩

abbrev M (n : Nat) (KemSK ProviderState Value : Type) := StateT (State n KemSK ProviderState) (OracleComp (WorldSpec n)) Value

def onKeys (work : StateT (RegistrationNativeHiddenService.State n) (OracleComp (EnvEffects n)) Value) :
    M n KemSK ProviderState Value := fun before =>
  (fun result => (result.1, { before with keys := result.2 })) <$> simulateQ effectLift (work.run before.keys)

def effect (query : (EnvEffects n).Domain) : M n KemSK ProviderState ((EnvEffects n).Range query) :=
  StateT.lift (effectLift query)

def routed (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    M n KemSK ProviderState ((RegistrationNativePublicFrontend.RoutedKem KemSK).Range query) := fun before =>
  (fun result => (result.1, { before with pool := result.2.1, provider := result.2.2 })) <$>
    simulateQ PqxdhRecordLiftInterface.coinLift ((provider query).run (before.pool, before.provider))

noncomputable def publication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) : M n KemSK ProviderState (RegistrationBoundPublication.Spec.Range query) := fun before =>
  (fun result => (result.1, { before with receipts := result.2 })) <$>
    simulateQ effectLift ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run before.receipts)

noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (M n KemSK ProviderState)
  | .inl (.inl message) => onKeys (RegistrationNativeHiddenService.prepare
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message)
  | .inl (.inr (.inl (.inl message))) => onKeys (RegistrationNativeHiddenService.demand setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) message)
  | .inl (.inr (.inl (.inr (.inl query)))) => publication setup wire sign query
  | .inl (.inr (.inl (.inr (.inr query)))) => effect query
  | .inl (.inr (.inr query)) => routed provider query
  | .inr query => StateT.lift ((WorldSpec n).query (.inr (.inr query)))

/-- Every ordinary effect reaches the one shared World directly; no second cache or synthetic installation reply is used. -/
theorem effect_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (EnvEffects n).Domain)
    (before : State n KemSK ProviderState) :
    (handler setup wire sign seed scalar provider (.inl (.inr (.inl (.inr (.inr query)))))).run before =
      (fun value => (value, before)) <$> effectLift query := by
  simp only [handler, effect, StateT.run_lift, bind_pure_comp]
  rfl

/-- All ongoing record requests use the actual World record surface and retain the thin service/KEM state. -/
theorem record_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State n KemSK ProviderState) :
    (handler setup wire sign seed scalar provider (.inr query)).run before =
      (fun value => (value, before)) <$> ((WorldSpec n).query (.inr (.inr query)) : OracleComp (WorldSpec n) _) := by
  simp only [handler, StateT.run_lift, bind_pure_comp]
  rfl

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState) :=
  (simulateQ (handler setup wire (RegistrationNativeMldsa.owned source credential) seed scalar provider)
    (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) serverKeyId bounds mode work frontend)).run before

end BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter.effect_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter.effect_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter.record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenInterpreter.record_query
