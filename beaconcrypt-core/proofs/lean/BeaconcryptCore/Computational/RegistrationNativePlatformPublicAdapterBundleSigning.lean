-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthentication
import BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives
/-! Source Bundle signing retains every primitive draw and shared-cache effect while erasing only the private ML receipt and Ed history instrumentation. The physical source interpreter uses explicit signing credentials and complete source requests; it does not inspect the owner roster or a private hash journal. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend backendLeaf LeafSpec)
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

private theorem beacon_effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    RegistrationNativeExperiment.beacon (n:=n) (mlSource:=source) setup checks representation created
      (RegistrationNativeBeaconFrontend.effect (KemSK:=KemSK) (Auxiliary:=RegistrationServerRoleBackend.State) query)=
      RegistrationNativeExperiment.trusted setup checks representation created source (.inl query) := by
  apply StateT.ext
  intro before
  rw [RegistrationNativeLocalStatePatch.beacon_run]
  simp only [RegistrationNativeBeaconFrontend.effect,StateT.run_lift,StateT.run_map,bind_pure_comp,simulateQ_map,simulateQ_spec_query,Functor.map_map]
  unfold RegistrationNativeExperiment.trusted
  simp only [RegistrationNativeExperiment.world,RegistrationNativeExperiment.server,StateT.run,Functor.map_map]
  rfl

private theorem beacon_sample (work : ProbComp A) :
    RegistrationNativeExperiment.beacon (n:=n) (mlSource:=source) setup checks representation created
      (RegistrationNativeBeaconFrontend.sample (KemSK:=KemSK) (Auxiliary:=RegistrationServerRoleBackend.State) work)=
      simulateQ (fun query=>RegistrationNativePlatformSdkReification.leaf (n:=n) (source:=source) setup checks representation created (.inl query)) work := by
  unfold RegistrationNativeBeaconFrontend.sample
  rw [RegistrationNativeLocalStatePatch.beacon_simulate (n:=n) (source:=source) setup checks representation created
    (fun query : unifSpec.Domain=>RegistrationNativeBeaconFrontend.effect (n:=n) (KemSK:=KemSK)
      (mldsaSource:=source) (Auxiliary:=RegistrationServerRoleBackend.State) (.inl query))
    (fun query=>RegistrationNativeLocalStatePatch.effect_work (.inl query)) work]
  apply congrArg (fun handler=>simulateQ handler work)
  funext query
  exact beacon_effect setup checks representation created (.inl query)

noncomputable def sample (work : ProbComp A) : StateT (Backend n KemSK) (StateT P ProbComp) A :=fun before=>
  simulateQ coins ((simulateQ (fun query=>backendLeaf setup checks representation created (.inl query)) work).run before)

theorem sample_source (work : ProbComp A) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.sample (Auxiliary:=RegistrationServerRoleBackend.State) work))).run before=
      (sample coins setup checks representation created work).run (backend before) := by
  rw [beacon_sample setup checks representation created]
  have same:=RegistrationNativePlatformSdkReification.program_backend setup checks representation created
    (simulateQ (fun query=>(LeafSpec KemSK).query (.inl query)) work) before
  simp only [←QueryImpl.simulateQ_compose] at same
  have interpreted:=congrArg (simulateQ coins) same
  simp only [simulateQ_map] at interpreted
  exact interpreted

private theorem receipt_source (receipt : RegistrationSigningShared.Receipt) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.updateEnv (n:=n) (KemSK:=KemSK) (mldsaSource:=source)
          (fun env=>{env with receipts:=env.receipts++[receipt]}))).run before=pure ((),backend before) := by
  rw [RegistrationNativeLocalStatePatch.beacon_run]
  simp only [RegistrationNativeBeaconFrontend.updateEnv,StateT.run_lift,bind_pure_comp]
  rfl

private theorem ed_history_source (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.logEd (n:=n) (KemSK:=KemSK) (Auxiliary:=RegistrationServerRoleBackend.State) index message signature)).run before=
      pure ((),backend before) := by
  rw [RegistrationNativeLocalStatePatch.beacon_run]
  simp only [RegistrationNativeBeaconFrontend.logEd,StateT.run_modify,StateT.run_pure,simulateQ_pure,map_pure]
  rfl

private theorem receipts_return (receipt : RegistrationSigningShared.Receipt) (value : A) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeExperiment.beacon setup checks representation created (do
        RegistrationNativeBeaconFrontend.updateEnv (n:=n) (KemSK:=KemSK) (mldsaSource:=source)
          (fun env=>{env with receipts:=env.receipts++[receipt]})
        pure value)).run before=pure (value,backend before) := by
  rw [RegistrationNativeLocalStatePatch.beacon_bind setup checks representation created _ _
    (fun _=>RegistrationNativeLocalStatePatch.pure_work value)]
  simp only [RegistrationNativeLocalStatePatch.beacon_pure,bind_pure_comp]
  have same:=congrArg (fun work=>(fun result=>(value,result.2)) <$>work)
    (receipt_source setup checks representation created receipt before)
  simp only [map_pure,Functor.map_map] at same
  exact same

noncomputable def rawOutgoing (credential : RegistrationNativeMldsa.Credential source)
    (identity : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Backend n KemSK) ProbComp)
  | .inl (.hash request)=>RegistrationNativePlatformPublicAdapterAuthentication.hash setup checks representation created
      (RegistrationInputs.hashBytes request)
  | .inl (.sign request _payload _digest)=>simulateQ
      (fun query=>backendLeaf setup checks representation created (.inl query))
      (RegistrationNativeMldsa.owned source credential request)
  | .inr request=>by
    classical
    exact if request.public_key=PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys identity).ed25519 then
      let message:=TranscriptAuthParts.absSlice request.message
      let signature:=setup.joint.sign identity message
      pure (RegistrationAuthenticationShared.openedBytes (some (signature.toList++message)))
    else pure .None

theorem outgoing_source (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)).run before=
      (rawOutgoing setup checks representation created owner.mldsa owner.identitySeed query).run (backend before) := by
  cases query with
  | inl query=>cases query with
    | hash request=>
      rw [RegistrationNativeBeaconFrontend.outgoing,RegistrationNativeBeaconFrontend.hash,beacon_effect]
      exact RegistrationNativePlatformSdkReification.hash_backend setup checks representation created (RegistrationInputs.hashBytes request) before
    | sign request payload digest=>
      let receipt (reply : RegistrationSigningShared.SignReply) : RegistrationSigningShared.Receipt:=
        ⟨⟨request.public_key,payload,RegistrationSigningTrace.replyBytes reply⟩,digest⟩
      let later (reply : RegistrationSigningShared.SignReply) :
          RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State RegistrationSigningShared.SignReply :=do
        RegistrationNativeBeaconFrontend.updateEnv (fun env=>{env with receipts:=env.receipts++[receipt reply]})
        pure reply
      have step:=RegistrationNativeLocalStatePatch.beacon_bind (n:=n) (source:=source) setup checks representation created
        (RegistrationNativeBeaconFrontend.sample (RegistrationNativeMldsa.owned source owner.mldsa request)) later
        (fun reply=>RegistrationNativeLocalStatePatch.bind_work _ _ (RegistrationNativeLocalStatePatch.env_work _)
          (fun _=>RegistrationNativeLocalStatePatch.pure_work reply))
      change Prod.map id backend <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.sample (RegistrationNativeMldsa.owned source owner.mldsa request) >>=later)).run before=_
      rw [step,beacon_sample]
      simp only [StateT.run_bind,map_bind]
      have sampleLaw : Prod.map id backend <$>
          (simulateQ (fun query=>RegistrationNativePlatformSdkReification.leaf (n:=n) (source:=source) setup checks representation created (.inl query))
            (RegistrationNativeMldsa.owned source owner.mldsa request)).run before=
          (simulateQ (fun query=>backendLeaf setup checks representation created (.inl query))
            (RegistrationNativeMldsa.owned source owner.mldsa request)).run (backend before) := by
        apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
        intro query state
        exact RegistrationNativePlatformSdkReification.coin_backend setup checks representation created query state
      simp only [rawOutgoing]
      rw [←sampleLaw]
      conv_rhs=>rw [←bind_pure_comp]
      apply bind_congr
      rintro ⟨reply,current⟩
      exact receipts_return setup checks representation created _ reply current
  | inr request=>
    classical
    simp only [RegistrationNativeBeaconFrontend.outgoing,rawOutgoing]
    split
    · rw [RegistrationNativeLocalStatePatch.beacon_bind setup checks representation created _ _
        (fun _=>RegistrationNativeLocalStatePatch.pure_work _)]
      simp only [RegistrationNativeLocalStatePatch.beacon_pure,StateT.run_pure,bind_pure_comp]
      have same:=congrArg (fun work=>(fun result=>(RegistrationAuthenticationShared.openedBytes
          (some ((setup.joint.sign owner.identitySeed (TranscriptAuthParts.absSlice request.message)).toList++TranscriptAuthParts.absSlice request.message)),result.2)) <$>work)
        (ed_history_source setup checks representation created index (TranscriptAuthParts.absSlice request.message)
          (setup.joint.sign owner.identitySeed (TranscriptAuthParts.absSlice request.message)) before)
      simp only [map_pure,Functor.map_map] at same
      exact same
    · rw [RegistrationNativeLocalStatePatch.beacon_pure,StateT.run_pure,map_pure]
      rfl

noncomputable def outgoing (credential : RegistrationNativeMldsa.Credential source)
    (identity : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (Backend n KemSK) (StateT P ProbComp)) :=
  fun query before=>simulateQ coins ((rawOutgoing setup checks representation created credential identity query).run before)

theorem outgoing_platform (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner query).run before=
      (outgoing coins setup checks representation created owner.mldsa owner.identitySeed query).run (backend before) := by
  unfold RegistrationNativeBundleInterpretation.outgoing
  rw [RegistrationNativeBundleInterpretation.legacy]
  have same:=congrArg (simulateQ coins) (outgoing_source setup checks representation created index owner query before)
  rw [simulateQ_map] at same
  exact same

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
noncomputable def sourceOutgoing (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) :=
  outgoing (n:=n) coins setup checks representation created (view.mldsa self.authentication.identity)
    (view.edSecret self.identity_key.secret_key)

theorem source_operands (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before : Native)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Prod.map id backend <$>
      (RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner query).run before=
      (sourceOutgoing coins setup checks representation created view self query).run (backend before) := by
  unfold sourceOutgoing
  rw [related.mldsa,related.identitySecret]
  exact outgoing_platform coins setup checks representation created writer index owner query before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.sample_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.sample_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.source_operands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning.source_operands
