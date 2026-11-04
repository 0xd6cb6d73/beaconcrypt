-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishTree
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
import BeaconcryptCore.Computational.RegistrationNativeRecordJournal
/-! The complete active extracted SDK Beacon finish is now one raw Trusted free request tree. Actual authentication, NoEntropy agreement and first-record leaves are derived double lifts; the concrete source decoder and complete returned Self remain in the theorem dependency chain. source_joint preserves the exact returned source object and both frontend states, and source_realized retains any mutable primitive state and its full joint distribution under an arbitrary stateful trusted implementation. No Id interpretation, codec premise, aggregate controller law, or successful primitive premise is used. Native ghost journals and terminal lifecycle are the next composition step. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner Trusted)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
open RegistrationNativeAgreementJournal (lift_run)

theorem lift_pure (value : A) : RegistrationNativeAgreementJournal.lift (pure value : OracleComp (Trusted n KemSK) A) = (pure value : M n KemSK source Auxiliary A) := by
  funext owners env
  change (((RegistrationNativeAgreementJournal.lift (pure value) : M n KemSK source Auxiliary A).run owners).run env) = (((pure value : M n KemSK source Auxiliary A).run owners).run env)
  simp only [lift_run, StateT.run_pure, map_pure]

theorem lift_bind (work : OracleComp (Trusted n KemSK) A) (next : A → OracleComp (Trusted n KemSK) B) :
    RegistrationNativeAgreementJournal.lift (work >>= next) = (RegistrationNativeAgreementJournal.lift work >>= fun value => RegistrationNativeAgreementJournal.lift (next value) : M n KemSK source Auxiliary B) := by
  funext owners env
  change (((RegistrationNativeAgreementJournal.lift (work >>= next) : M n KemSK source Auxiliary B).run owners).run env) = (((RegistrationNativeAgreementJournal.lift work >>= fun value => RegistrationNativeAgreementJournal.lift (next value) : M n KemSK source Auxiliary B).run owners).run env)
  simp only [lift_run, StateT.run_bind, bind_map_left, map_bind]

theorem lift_map (work : OracleComp (Trusted n KemSK) A) (observe : A → B) :
    RegistrationNativeAgreementJournal.lift (observe <$> work) = (observe <$> RegistrationNativeAgreementJournal.lift work : M n KemSK source Auxiliary B) := by
  funext owners env
  change (((RegistrationNativeAgreementJournal.lift (observe <$> work) : M n KemSK source Auxiliary B).run owners).run env) =
    (((observe <$> RegistrationNativeAgreementJournal.lift work : M n KemSK source Auxiliary B).run owners).run env)
  simp only [lift_run, StateT.run_map, Functor.map_map]


noncomputable def authentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (OracleComp (Trusted n KemSK))
  | .hash request => do
      let digest ← (Trusted n KemSK).query (.inl (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa source.verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 setup.source.crypto request)

theorem authentication_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query = RegistrationNativeAgreementJournal.lift (authentication (source := source) setup query) := by
  cases query with
  | hash request =>
      funext owners env
      change (((RegistrationNativeBeaconFrontend.authentication setup source (.hash request) : M n KemSK source Auxiliary _).run owners).run env) =
        (((RegistrationNativeAgreementJournal.lift (authentication (source := source) setup (.hash request)) : M n KemSK source Auxiliary _).run owners).run env)
      simp only [RegistrationNativeBeaconFrontend.authentication, RegistrationNativeBeaconFrontend.hash,
        RegistrationNativeBeaconFrontend.effect, authentication, RegistrationNativeAgreementJournal.lift,
        StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
      rfl
  | mldsa request | ed25519 request => exact (lift_pure _).symm

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]

noncomputable def recordSuffix (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) : OracleComp (Trusted n KemSK) (RustM AdapterPublicFinishBody.Result) :=
  match effect with
  | .Rejected (.Some control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .BeaconComplete agreed => (fun result => AdapterPublicFinishRecord.wrap self (AdapterPublicFinishRecord.result self.identity_key_kid result)) <$>
      simulateQ (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin agreed)
  | _ => pure (.ok (.None, self))

theorem record_suffix_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) :
    AdapterPublicFinishTree.recordSuffix (n := n) (source := source) (Auxiliary := Auxiliary) setup wire self effect = RegistrationNativeAgreementJournal.lift (recordSuffix setup wire self effect) := by
  cases effect with
  | Rejected optional => cases optional <;> exact (lift_pure _).symm
  | BeaconComplete agreed =>
      have leaves : RegistrationNativeRecordJournal.unlogged (n := n) (source := source) (Auxiliary := Auxiliary) setup wire =
          fun query => RegistrationNativeAgreementJournal.lift (RegistrationNativeRecordJournal.core setup wire query) :=
        funext (RegistrationNativeRecordJournal.core_lift setup wire)
      simp only [AdapterPublicFinishTree.recordSuffix, recordSuffix, leaves,
        RegistrationNativeAgreementJournal.simulate_lift, ← lift_map]
  | _ => exact (lift_pure _).symm

noncomputable def accepted (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) : OracleComp (Trusted n KemSK) (RustM AdapterPublicFinishBody.Result) := do
  let result ← simulateQ (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated)
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok phase => recordSuffix setup wire self phase

theorem accepted_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) :
    AdapterPublicFinishTree.accepted (n := n) (Auxiliary := Auxiliary) setup wire self owner scalar authenticated = RegistrationNativeAgreementJournal.lift (accepted setup wire self owner scalar authenticated) := by
  have leaves : RegistrationNativeBeaconFrontend.agreementCore (n := n) (Auxiliary := Auxiliary) setup owner scalar =
      fun query => RegistrationNativeAgreementJournal.lift (RegistrationNativeAgreementJournal.core setup owner scalar query) :=
    funext (RegistrationNativeAgreementJournal.core_lift setup owner scalar)
  unfold AdapterPublicFinishTree.accepted accepted
  rw [leaves, RegistrationNativeAgreementJournal.simulate_lift, lift_bind]
  apply bind_congr
  intro agreed
  cases agreed with
  | fail error | div => exact (lift_pure _).symm
  | ok phase => exact record_suffix_lift setup wire self phase

noncomputable def afterAuthentication (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) : OracleComp (Trusted n KemSK) (RustM AdapterPublicFinishBody.Result) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .ok (.Ok authenticated) => accepted setup wire self owner scalar authenticated

theorem after_lift (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    AdapterPublicFinishTree.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire self owner scalar reply =
      RegistrationNativeAgreementJournal.lift (afterAuthentication setup wire self owner scalar reply) := by
  cases reply with
  | fail error | div => exact (lift_pure _).symm
  | ok outcome => cases outcome with
    | Err control => exact (lift_pure _).symm
    | Ok authenticated => exact accepted_lift setup wire self owner scalar authenticated

noncomputable def program (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending) (input : Slice U8)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) : OracleComp (Trusted n KemSK) (RustM AdapterPublicFinishBody.Result) := do
  let reply ← simulateQ (authentication (source := source) setup)
    (RegistrationResponseExecutor.begin pending (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
  afterAuthentication setup wire {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} owner scalar reply

variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary))]
variable {E : Type}

theorem source_tree (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (parseEd : Slice U8 → M n KemSK source Auxiliary (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source Auxiliary (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) self input).run =
        RegistrationNativeAgreementJournal.lift (program setup wire self pending input owner scalar) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicFinishTree.source_active setup wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap]
  unfold program
  have leaves : RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source =
      fun query => RegistrationNativeAgreementJournal.lift (authentication (source := source) setup query) :=
    funext (authentication_lift setup)
  rw [leaves, RegistrationNativeAgreementJournal.simulate_lift, lift_bind]
  apply bind_congr
  intro reply
  exact after_lift setup wire _ owner scalar reply

theorem source_joint (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (parseEd : Slice U8 → M n KemSK source Auxiliary (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source Auxiliary (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys)
    (owners : List (Owner source)) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
    ((((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) self input).run).run owners).run env) =
        (fun result => ((result, owners), env)) <$> program setup wire self pending input owner scalar := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
  rw [source_tree setup wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap]
  exact lift_run _ owners env

theorem source_realized {PrimitiveState : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source Auxiliary))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (parseEd : Slice U8 → M n KemSK source Auxiliary (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source Auxiliary (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys)
    (owners : List (Owner source)) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (implementation : QueryImpl (Trusted n KemSK) (StateT PrimitiveState ProbComp)) (before : PrimitiveState) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
    ((simulateQ implementation
      ((((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
        (m := AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) self input).run).run owners).run env)).run before) =
      (fun result => (((result.1, owners), env), result.2)) <$>
        (simulateQ implementation (program setup wire self pending input owner scalar)).run before := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source Auxiliary)) := AdapterPublicConcreteCodecs.codecs
  rw [source_joint setup wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap owners env]
  simp only [simulateQ_map, StateT.run_map]

end BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.lift_map

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.authentication_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.authentication_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.record_suffix_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.record_suffix_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.accepted_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.accepted_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.after_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.after_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_tree

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_joint

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishFreeTree.source_realized
