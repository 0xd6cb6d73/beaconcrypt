-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveMaterialCaps

/-! Actual Beacon material completion demands only its successful preparation's returned descriptor. Ordinary-owner preparation translation leaves that descriptor untouched at demand. All actual raw opening, terminal abort, owner-phase update and installation callbacks remain present, and flag extension supplies preparation safety at every reached prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec liftLocal paired)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
open RegistrationNativeSecretWordLiveCaps (Bad BadLocal BadPublic)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

private theorem common_free (flags : Message → Bool) (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work).IsQueryBoundP (BadPublic flags) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeSecretWordServerMaterial.commonLift, BadPublic, isQueryBoundP_query_iff]

private theorem admitted_free (flags : Message → Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (reference : Message)
    (prepared : flags reference = true) :
    (RegistrationNativeSecretWordBeaconMaterial.admitted (n := n) source owner sender descriptor reference).IsQueryBoundP (BadPublic flags) 0 := by
  unfold RegistrationNativeSecretWordBeaconMaterial.admitted
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · left
    simp only [BadPublic, prepared, Bool.true_eq_false, not_false_eq_true]
  · intro chosen
    cases chosen with
    | none => trivial
    | some choice =>
        simpa only [BadPublic, prepared, Bool.true_eq_false, ite_false] using common_free flags
          (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice)

private theorem abort_free (flags : Message → Bool) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (env : EnvState Auxiliary) :
    (((RegistrationNativeSecretWordBeaconMaterial.abort (n := n) owner).run current).run env).IsQueryBoundP (BadPublic flags) 0 := by
  simp [RegistrationNativeSecretWordBeaconMaterial.abort, RegistrationNativeSecretWordBeaconMaterial.effect,
    StateT.run_lift, bind_pure_comp, BadPublic,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem complete_free (flags : Message → Bool) (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {source : RegistrationNativeMldsa.Source} (owner current : SelectedOwner source) (ready : BeaconReady)
    (env : EnvState Auxiliary) (prepared : flags ready.reference = true) :
    (((RegistrationNativeSecretWordBeaconMaterial.complete (n := n) hkdf owner ready).run current).run env).IsQueryBoundP (BadPublic flags) 0 := by
  simp only [RegistrationNativeSecretWordBeaconMaterial.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply isQueryBoundP_bind (n := 0) (m := 0)
    (admitted_free flags hkdf owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference prepared)
  intro completed _
  cases completed with
  | fail error => simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
      StateT.run_map, map_pure, bind_pure_comp, isQueryBoundP_map_iff] using abort_free flags owner current env
  | div => simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
      StateT.run_map, map_pure, bind_pure_comp, isQueryBoundP_map_iff] using abort_free flags owner current env
  | ok reply => cases reply with
    | Err previous => simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure,
        StateT.run_map, map_pure, bind_pure_comp, isQueryBoundP_map_iff] using abort_free flags owner current env
    | Ok completed => trivial

private theorem paired_bound (flags : Message → Bool)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (bounded : work.IsQueryBoundP (BadPublic flags) 0) :
    (simulateQ (paired (KemSK := KemSK)) work).IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  cases query with
  | inl message =>
      cases flag : flags message <;> simp [paired, BadLocal, BadPublic, flag, isQueryBoundP_query_iff]
  | inr query => simp [paired, BadLocal, BadPublic, isQueryBoundP_query_iff]

/-- Ordinary translation affects only preparation; it preserves the exact demanded name and its zero-unprepared-demand bill. -/
theorem ordinary_bound (flags : Message → Bool) (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (bounded : work.IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  rcases query with message | (message | common) | kem
  · simp only [RegistrationNativeSecretWordOwners.ordinary, BadLocal, ite_false]
    cases translated : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message <;>
      simp [isQueryBoundP_query_iff, BadLocal]
  · cases flag : flags message <;> simp [RegistrationNativeSecretWordOwners.ordinary, BadLocal, flag, isQueryBoundP_query_iff]
  · simp [RegistrationNativeSecretWordOwners.ordinary, BadLocal, isQueryBoundP_query_iff]
  · simp [RegistrationNativeSecretWordOwners.ordinary, BadLocal, isQueryBoundP_query_iff]

/-- The actual admitted Beacon stage uses only its prepared returned name and literal common work under the full global route. -/
theorem admitted (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (reference : Message)
    (before : State n KemSK) (valid : Valid input before) (prepared : before.flags reference = true) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (liftLocal false) (simulateQ paired
        (RegistrationNativeSecretWordBeaconMaterial.admitted setup.source owner sender descriptor reference))) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply RegistrationNativeSecretWordLiveCaps.local_bound before.flags false
  exact paired_bound before.flags _ (admitted_free before.flags setup.source owner sender descriptor reference prepared)

/-- Every actual selected or ordinary Beacon completion preserves preparation safety, all terminal paths, the full owner and current environment. -/
theorem complete (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (localScalar : Option PqxdhJointGapDh.ScalarBytes) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (ready : BeaconReady) (env : EnvState Auxiliary)
    (before : State n KemSK) (valid : Valid input before) (prepared : before.flags ready.reference = true) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (liftLocal false) (match localScalar with
        | none => (((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready).run current).run env)
        | some scalar => simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar)
            (((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready).run current).run env))) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply RegistrationNativeSecretWordLiveCaps.local_bound before.flags false
  have bounded := paired_bound (n := n) (KemSK := KemSK) before.flags _ (complete_free (n := n) before.flags setup.source owner current ready env prepared)
  cases localScalar with
  | none => exact bounded
  | some scalar => exact ordinary_bound before.flags setup scalar _ bounded

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.ordinary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.ordinary_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps.complete
