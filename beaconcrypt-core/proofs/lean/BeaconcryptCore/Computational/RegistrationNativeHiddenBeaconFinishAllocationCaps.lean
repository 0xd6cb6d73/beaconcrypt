-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild
import BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-! Every actual selected or ordinary Beacon finish keeps physical owner allocation unchanged. Authentication and key agreement use hashes, coins and indexed KEM callbacks; terminal lifecycle and record installation use advanceOwner/installBeacon only. Ordinary root-address materialization preserves this structural footprint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeHiddenServerAllocationCaps (EffectAllowed LocalAllowed)
open RegistrationNativeHiddenServerAllocationCapsBuild (CommonAllowed PublicAllowed)
open RegistrationNativeHiddenAllocationCore (simulation mapped)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
local notation "Safe" => LocalAllowed (n := n) (KemSK := KemSK)

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem run_safe {Index S : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT S (OracleComp (Spec n KemSK))))
    (step : ∀ query before, AllQueriesSatisfy ((impl query).run before) Safe)
    (work : OracleComp spec Value) (before : S) :
    AllQueriesSatisfy ((simulateQ impl work).run before) Safe := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (step query before) (fun result => ih result.1 result.2)

private theorem effect_safe (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ (effect (KemSK := KemSK)) work) Safe :=
  simulation effect EffectAllowed Safe (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) work safe

private theorem sample_safe (work : ProbComp Value) :
    AllQueriesSatisfy (sample (n := n) (KemSK := KemSK) work) Safe := by
  unfold sample
  apply simulation (fun query => effect (n := n) (KemSK := KemSK) (.inl query)) (fun _ => True) Safe _ work (every work)
  intro query _
  simp only [effect, allQueriesSatisfy_query_iff, LocalAllowed, EffectAllowed,
    RegistrationNativeHiddenAllocationProtocol.effectDelta]

private theorem primitive_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    AllQueriesSatisfy (primitive (n := n) setup owner oneTime query) Safe := by
  unfold primitive
  apply simulation _ (fun _ => True) Safe _ _ (every _)
  intro query _
  cases query with
  | inl query => exact sample_safe _
  | inr query => exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem backend_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((backend (n := n) setup owner oneTime query).run before) Safe := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp]
  apply mapped
  cases query <;> first | exact primitive_safe setup owner oneTime _ | trivial

private theorem prefix_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before) Safe := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first | exact run_safe _ (backend_safe setup owner oneTime) _ before | trivial

private theorem collect_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((collect (n := n) setup owner oneTime authenticated).run before) Safe := by
  unfold collect
  exact run_safe _ (prefix_safe setup owner oneTime authenticated) _ before

private theorem prepare_safe (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    AllQueriesSatisfy (simulateQ (prepare (n := n) (KemSK := KemSK)) work) Safe :=
  simulation prepare (fun _ => True) Safe
    (fun _query _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem agreement_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((agreement (n := n) setup owner oneTime authenticated).run before) Safe := by
  simp only [agreement, StateT.run_bind]
  apply allQueriesSatisfy_bind (collect_safe setup owner oneTime authenticated before)
  intro result
  cases result.1 with
  | none => trivial
  | some pending =>
      simp only [StateT.run_lift, bind_pure_comp]
      exact mapped _ _ Safe (prepare_safe (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending))

private theorem authentication_safe (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationAuthenticationCompiler.callbacks (n := n) crypto verify) work) EffectAllowed := by
  apply simulation _ (fun _ => True) EffectAllowed _ work (every work)
  intro query _
  cases query with
  | hash request => exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)
  | mldsa request => trivial
  | ed25519 request => trivial

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Actual response authentication and selected-prekey collection cannot allocate a physical owner. -/
theorem preparation_safe (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    AllQueriesSatisfy (((finishPreparation (n := n) setup source packet).run owner).run before) Safe := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply allQueriesSatisfy_bind (effect_safe _ (authentication_safe setup.source.crypto source.verify _))
          intro accepted
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simp only [StateT.run_lift, StateT.run_map, bind_pure_comp]
                exact mapped _ _ Safe (agreement_safe setup owner oneTime authenticated before)

private theorem installed (owner : Nat) (sender : U64)
    (select : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.after owner sender select result) EffectAllowed := by
  cases result with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err aborted => trivial
    | Ok completed => exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)

private theorem raw (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationNativePairedBeaconService.rawLift (n := n)) work) CommonAllowed :=
  simulation RegistrationNativePairedBeaconService.rawLift (fun _ => True) CommonAllowed
    (fun _query _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem effects (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ RegistrationHiddenInstall.effectLift work) CommonAllowed :=
  simulation RegistrationHiddenInstall.effectLift EffectAllowed CommonAllowed
    (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) work safe

private theorem branch (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) :
    AllQueriesSatisfy (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice) CommonAllowed := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.knownStage]
      exact allQueriesSatisfy_bind (raw _) (fun result => effects _ (installed owner sender _ result))
  | hidden reference =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.hiddenStage,
        RegistrationNativePairedBeaconService.privateHiddenStage]
      exact allQueriesSatisfy_bind (raw _) (fun result => effects _ (installed owner sender _ result))

private theorem admitted (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (message : RegistrationNativeRelatedFamily.Message) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.admitted (n := n) source owner sender descriptor message)) Safe := by
  apply simulation RegistrationBeaconReferenceFinish.service PublicAllowed Safe _ _ ?_
  · intro query allowed
    apply (allQueriesSatisfy_query_iff _ _).mpr
    rcases query with message | (publication | effect)
    · trivial
    · trivial
    · exact allowed
  · unfold RegistrationNativePairedBeaconService.admitted
    apply allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    intro choice
    cases choice with
    | none => trivial
    | some choice =>
        exact simulation RegistrationNativePairedServerService.publicCommon CommonAllowed PublicAllowed
          (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) _ (branch source owner sender descriptor choice)

private theorem abort_safe {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (before : EnvState Auxiliary) (value : Value) :
    AllQueriesSatisfy (((RegistrationBeaconReferenceFinish.abort owner *> pure value :
      RegistrationBeaconReferenceFinish.OwnerM n KemSK Auxiliary source Value).run current).run before) Safe := by
  simp only [RegistrationBeaconReferenceFinish.abort, seqRight_eq_bind, StateT.run_map,
    StateT.run_lift, bind_pure_comp]
  exact mapped _ _ Safe ((allQueriesSatisfy_query_iff _ _).mpr rfl)

private theorem complete_safe (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : EnvState Auxiliary) :
    AllQueriesSatisfy (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before) Safe := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift, bind_map_left, bind_pure_comp]
  apply allQueriesSatisfy_bind (admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference)
  intro completed
  cases completed with
  | fail error => exact abort_safe owner current before _
  | div => exact abort_safe owner current before _
  | ok completed => cases completed with
    | Err aborted => exact abort_safe owner current before _
    | Ok completed => trivial

/-- The complete selected-owner finish uses terminal advance/install callbacks, without a new owner append. -/
theorem finish_safe (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    AllQueriesSatisfy (((RegistrationBeaconReferenceFinish.finish (n := n) (KemSK := KemSK) setup source packet).run owner).run before) Safe := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind]
          apply allQueriesSatisfy_bind (preparation_safe setup source packet owner before)
          intro result
          rcases result with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error => exact abort_safe owner current env _
          | div => exact abort_safe owner current env _
          | ok prepared => cases prepared with
            | none => exact abort_safe owner current env _
            | some ready => exact complete_safe setup.source owner current ready env

/-- Ordinary local-scalar materialization changes only preparation addresses, so every roster finish is allocation-free too. -/
theorem owners_safe (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (before : EnvState Auxiliary) :
    AllQueriesSatisfy (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run before) Safe := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
      apply mapped
      cases owner.scalar with
      | none => exact finish_safe setup source packet owner.view before
      | some scalar =>
          apply simulation _ Safe Safe _ _ (finish_safe setup source packet owner.view before)
          intro query allowed
          cases query with
          | inl message =>
              simp only [RegistrationNativePublicOwners.ordinary]
              split
              · trivial
              · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
          | inr query => exact (allQueriesSatisfy_query_iff _ _).mpr allowed

/-- Both actual roster branches remain allocation-free after their literal public frontend embedding. -/
theorem frontend_safe (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativePublicFrontend.State source) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.beacon
      (RegistrationNativePublicOwners.finish (n := n) setup source index packet)).run before)
      RegistrationNativeHiddenAllocationCore.Allowed := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run]
  apply mapped
  apply simulation (RegistrationNativePublicFrontend.liftLocal false) Safe RegistrationNativeHiddenAllocationCore.Allowed
    _ _ (owners_safe setup source index packet before.beacons before.environment)
  intro query allowed
  rcases query with message | (query | query)
  · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · apply (allQueriesSatisfy_query_iff _ _).mpr
    rcases query with message | (publication | effect)
    · trivial
    · trivial
    · exact allowed
  · apply simulation RegistrationNativePublicFrontend.liftRoutedKem (fun _ => True)
      RegistrationNativeHiddenAllocationCore.Allowed _ _ (every _)
    intro routed _
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

end BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.preparation_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.preparation_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.finish_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.finish_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.owners_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.owners_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.frontend_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps.frontend_safe
