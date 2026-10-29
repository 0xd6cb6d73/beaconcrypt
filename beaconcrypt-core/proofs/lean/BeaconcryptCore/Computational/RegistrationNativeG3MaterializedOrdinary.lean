-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! Ordinary typed commands do not demand key material or install hidden record kernels. Materialization therefore leaves their exact open callback AST unchanged, including all constructor, publication, authentication, parsed-counter and record outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationServerOpenReferenceCompiler
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private def EffectAllowed : (PqxdhRecordLiftInterface.EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ _) | .inr (.installBeacon _ _ _) => False
  | _ => True
private def LocalAllowed : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain → Prop
  | .inr (.inl (.inl _)) => False
  | .inr (.inl (.inr (.inr effect))) => EffectAllowed effect
  | _ => True

local notation "LocalSafe" => LocalAllowed (n := n) (KemSK := KemSK)

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem run_safe {Index State : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT State (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK))))
    (step : ∀ query before, AllQueriesSatisfy ((impl query).run before) LocalSafe)
    (work : OracleComp spec Value) (before : State) :
    AllQueriesSatisfy ((simulateQ impl work).run before) LocalSafe := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (step query before) (fun result => ih result.1 result.2)

private theorem effect_safe (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work) LocalSafe := by
  apply simulation _ EffectAllowed LocalSafe _ work safe
  intro query allowed
  exact (allQueriesSatisfy_query_iff _ _).mpr allowed

private theorem coins_safe (work : ProbComp Value) :
    AllQueriesSatisfy (simulateQ (RegistrationWorldCoinCompiler.envCoin (n := n)) work) EffectAllowed := by
  apply simulation _ (fun _ => True) EffectAllowed _ work (every work)
  intro query _
  simp [RegistrationWorldCoinCompiler.envCoin,
    EffectAllowed, allQueriesSatisfy_query_iff]

private theorem ordinary_backend_safe (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    AllQueriesSatisfy (simulateQ (RegistrationNativeKemReferenceCompiler.lift (KemSK := KemSK))
      ((RegistrationServerReferenceCompiler.backend (n := n) setup checks query).run before)) LocalSafe := by
  simp only [RegistrationServerReferenceCompiler.backend, RegistrationServerReferenceCompiler.liftEnvironment,
    RegistrationWorldAgreementCompiler.compiler, StateT.run, simulateQ_map]
  apply mapped
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  apply simulation _ (fun _ => True) LocalSafe _ _ (every _)
  intro query _
  simp [QueryImpl.compose, RegistrationWorldCoinCompiler.envCoin,
    RegistrationServerReferenceCompiler.effect, RegistrationNativeKemReferenceCompiler.lift,
    LocalAllowed, EffectAllowed, allQueriesSatisfy_query_iff]

private theorem backend_safe (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Environment) :
    AllQueriesSatisfy ((RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks query).run before) LocalSafe := by
  cases query with
  | encapsulate key =>
      simp only [RegistrationNativeKemReferenceCompiler.backend, StateT.run]
      apply mapped
      apply simulation _ (fun _ => True) LocalSafe _ _ (every _)
      intro query _
      simp [RegistrationBeaconReferenceCompiler.indexed, LocalAllowed, allQueriesSatisfy_query_iff]
  | _ => exact ordinary_backend_safe setup checks _ before

private theorem prefix_safe (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Environment) :
    AllQueriesSatisfy ((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
      RegistrationNativeKemReferenceCompiler.visit query).run before) LocalSafe := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact run_safe _ (backend_safe setup checks) _ before
    | trivial

/-- The actual selected-KEM/root collector emits no Beacon allocation on any failure or success branch. -/
private theorem collect_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    AllQueriesSatisfy ((RegistrationNativeKemReferenceCompiler.collect (n := n) setup checks packet authenticated).run before)
      (LocalAllowed (KemSK := KemSK)) := by
  unfold RegistrationNativeKemReferenceCompiler.collect
  exact run_safe _ (prefix_safe setup checks) _ before

private theorem root_safe (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationBeaconReferenceCompiler.prepare (n := n) (KemSK := KemSK)) work) LocalSafe := by
  exact simulation _ (fun _ => True) LocalAllowed (fun query _ => by
    simp [RegistrationBeaconReferenceCompiler.prepare, LocalAllowed, allQueriesSatisfy_query_iff]) work (every work)

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem agreement_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((agreement (n := n) setup checks packet authenticated).run before).run env) LocalSafe := by
  simp only [agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply allQueriesSatisfy_bind (collect_safe setup checks packet authenticated env)
  intro result
  cases result.1 with
  | none => trivial
  | some input =>
      simpa only [StateT.run, StateT.lift, bind_pure_comp, map_state_apply, Functor.map_map] using
        mapped _ _ LocalAllowed (root_safe (n := n) (KemSK := KemSK)
          (RegistrationServerReferenceRoot.client authenticated.binding input))

private theorem bind_safe {X Y : Type} (work : M n KemSK X) (next : X → M n KemSK Y)
    (first : ∀ before env, AllQueriesSatisfy ((work.run before).run env) LocalSafe)
    (later : ∀ value before env, AllQueriesSatisfy (((next value).run before).run env) LocalSafe)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((work >>= next).run before).run env) LocalSafe := by
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before env) (fun result => later result.1.1 result.1.2 result.2)

private theorem retain_safe (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((retain (n := n) (KemSK := KemSK) ready).run before).run env) LocalSafe := by
  simp only [retain, StateT.run]
  cases RegistrationServerMaterialFrontend.retain ready before <;> trivial

private theorem after_safe (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env) LocalSafe := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · split
    · apply bind_safe _ _ (agreement_safe setup checks packet authenticated)
      intro value current state
      cases value with
      | fail error => trivial
      | div => trivial
      | ok value => cases value with
        | none => trivial
        | some ready => exact retain_safe ready current state
    · trivial

attribute [local irreducible] RegistrationAuthenticationExecutor.begin

/-- Every actual incoming verifier callback is a native hash or pure verification; none allocates a Beacon owner. -/
private theorem authentication_safe (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    AllQueriesSatisfy (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet) EffectAllowed := by
  unfold RegistrationAuthenticationCompiler.program
  apply simulation _ (fun _ => True) EffectAllowed _ _ (every _)
  intro query _
  cases query with
  | hash request =>
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => trivial)
  | mldsa request => trivial
  | ed25519 request => trivial

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- The whole actual SDK accept, including mandatory authentication, replay and reservation failures, is allocation-free. -/
private theorem accept_safe (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    AllQueriesSatisfy (((accept (n := n) setup checks verify packet).run before).run env) (LocalAllowed (KemSK := KemSK)) := by
  simp only [accept, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]
  apply allQueriesSatisfy_bind (effect_safe _ (authentication_safe setup.source.crypto verify before.pin packet))
  intro checked
  cases checked with
  | fail error => trivial
  | div => trivial
  | ok result =>
      rcases result with ⟨events, reply⟩
      cases reply <;> first
        | exact after_safe setup checks packet _ before env
        | trivial


namespace Beacon
open RegistrationNativeBeaconFrontend
variable {Auxiliary Next : Type} {source : RegistrationNativeMldsa.Source}

private def Allowed : (Trusted n KemSK).Domain → Prop
  | .inl effect => EffectAllowed effect
  | .inr _ => True

private def Safe (work : M n KemSK source Auxiliary Value) : Prop :=
  ∀ owners env, AllQueriesSatisfy ((work.run owners).run env) (Allowed (KemSK := KemSK))

private theorem pure_safe (value : Value) : Safe (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env
  simp only [StateT.run_pure]
  trivial

private theorem bind_safe (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Safe work) (later : ∀ value, Safe (next value)) : Safe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun reply => later reply.1.1 reply.1.2 reply.2)

private theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (safe : EffectAllowed query) :
    Safe (effect query : M n KemSK source Auxiliary _) := by
  intro owners env
  simp only [effect, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr safe)

private theorem sample_safe (work : ProbComp Value) : Safe (sample work : M n KemSK source Auxiliary Value) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [sample, simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (effect_safe _ trivial) ih

private theorem modify_safe (change : State source → State source) :
    Safe (modify change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [StateT.run_modify, StateT.run_pure]
  trivial

private theorem update_safe (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Safe (updateEnv change : M n KemSK source Auxiliary Unit) := by
  intro owners env
  simp only [updateEnv, StateT.run_lift]
  trivial

private theorem program_safe {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (step : ∀ query, Safe (implementation query)) (work : OracleComp spec Value) : Safe (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (step query) ih

/-- Actual preparation uses ordinary draws and the shared pin hash before any indexed birth or physical allocation. -/
private theorem prepare_safe (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Safe (prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
  unfold prepare
  apply bind_safe _ _ (sample_safe _)
  intro generated
  cases generated with
  | none => exact pure_safe _
  | some credentials =>
      dsimp only
      cases begun : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
      | fail error | div => exact pure_safe _
      | ok pending =>
          simp only
          cases requested : pending.request with
          | fail error | div => exact pure_safe _
          | ok request =>
              simp only
              apply bind_safe _ _ (effect_safe (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) trivial)
              intro digest
              cases resumed : pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
              | fail error | div => exact pure_safe _
              | ok result => cases result with
                | none => exact pure_safe _
                | some pin => exact bind_safe _ _ (sample_safe _) (fun _ => bind_safe _ _ (sample_safe _) (fun _ => pure_safe _))

private theorem outgoing_safe (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Safe (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_safe _ trivial
    | sign request payload digest => exact bind_safe _ _ (sample_safe _) (fun _ => bind_safe _ _ (update_safe _) (fun _ => pure_safe _))
  | inr request =>
      simp only [outgoing]
      split
      · exact bind_safe _ _ (modify_safe _) (fun _ => pure_safe _)
      · exact pure_safe _

/-- Full native Ed3/fingerprint/ML publication and lifecycle update contain no physical owner allocation. -/
private theorem bundle_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat) :
    Safe (bundle (n := n) (Auxiliary := Auxiliary) setup source wire index) := by
  intro owners env
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind]
  cases found : owners[index]? with
  | none => simp only [StateT.run_pure]; trivial
  | some owner =>
      simp only
      cases phase : owner.phase with
      | initSent pending oneTime | established completed | aborted control =>
          simp only [StateT.run_pure]
          trivial
      | fresh | freshWithCoins oneTime =>
          dsimp only
          have later (oneTime : PqxdhJointGapDh.ScalarBytes) : Safe (do
              let published ← simulateQ (outgoing setup source index owner)
                (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
                  ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey)
              match published with
              | .fail error => pure (.fail error)
              | .div => pure .div
              | .ok (.Err _) => pure (.ok none)
              | .ok (.Ok finished) => do
                  updatePhase index (.initSent finished.pending oneTime)
                  let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
                  pure (.ok (some finished.encoded)) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes))) := by
            apply bind_safe _ _ (program_safe _ (outgoing_safe setup index owner) _)
            intro published
            cases published with
            | fail error | div => exact pure_safe _
            | ok result => cases result with
              | Err error => exact pure_safe _
              | Ok finished => exact bind_safe _ _ (modify_safe _) (fun _ => bind_safe _ _ (effect_safe _ trivial) (fun _ => pure_safe _))
          all_goals first
            | exact bind_safe _ _ (sample_safe _) later owners env
            | exact later _ owners env


private theorem get_safe : Safe (get : M n KemSK source Auxiliary (State source)) := by
  intro owners env
  simp only [StateT.run_get, StateT.run_pure]
  trivial

private theorem set_safe (owners : State source) : Safe (set owners : M n KemSK source Auxiliary Unit) := by
  intro initial env
  simp only [StateT.run_set, StateT.run_pure]
  trivial

private theorem kem_safe (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Safe (kem query : M n KemSK source Auxiliary _) := by
  intro owners env
  simp only [kem, StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map]
  exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)

private theorem append_safe (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (keyId : U64)
    (pin : session.ServerAuthenticationPin) (credentials : RegistrationNativeMldsa.Credential source)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey : PqxdhJointGapDh.ScalarBytes) :
    Safe (appendBorn (n := n) (Auxiliary := Auxiliary) setup source edPin keyId pin credentials identity prekey) := by
  unfold appendBorn
  apply bind_safe _ _ (kem_safe _)
  intro born
  apply bind_safe _ _ (effect_safe (.inr (.appendOwner keyId edPin .fresh)) trivial)
  intro worldOwner
  apply bind_safe _ _ get_safe
  intro owners
  exact bind_safe _ _ (set_safe _) (fun _ => pure_safe _)

private theorem create_safe (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Safe (create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
  unfold create
  apply bind_safe _ _ (prepare_safe edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_safe _
  | ok prepared => cases prepared with
    | none => exact pure_safe _
    | some prepared => exact append_safe setup edPin keyId prepared.pin prepared.credentials prepared.identity prepared.prekey

end Beacon

private def PublicAllowed : (RegistrationNativePublicFrontend.Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inl _))) => False
  | .inl (.inr (.inl (.inr (.inr effect)))) => EffectAllowed effect
  | _ => True

private theorem local_safe (selected : Bool) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain)
    (safe : LocalSafe query) :
    AllQueriesSatisfy (RegistrationNativePublicFrontend.liftLocal (n := n) selected query)
      (PublicAllowed (KemSK := KemSK)) := by
  rcases query with message | (query | query)
  · simp [RegistrationNativePublicFrontend.liftLocal, PublicAllowed, allQueriesSatisfy_query_iff]
  · rcases query with message | (publication | effect)
    · exact safe.elim
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · exact (allQueriesSatisfy_query_iff _ _).mpr safe
  · apply simulation _ (fun _ => True) PublicAllowed _ _ (every _)
    intro routed _
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem server_safe {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : RegistrationNativePublicFrontend.State source)
    (safe : AllQueriesSatisfy ((work.run before.server).run before.environment) LocalSafe) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.serverOpen selected work).run before)
      (PublicAllowed (KemSK := KemSK)) := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run]
  exact mapped _ _ PublicAllowed (simulation _ LocalSafe PublicAllowed (local_safe selected) _ safe)

private theorem trusted_safe (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : Beacon.Allowed query) :
    AllQueriesSatisfy (RegistrationBeaconReferenceCompiler.trustedLift query) LocalSafe := by
  cases query with
  | inl effect =>
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect]
      exact (allQueriesSatisfy_query_iff _ _).mpr safe
  | inr query =>
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed]
      exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem beacon_safe {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativePublicFrontend.State source) (safe : Beacon.Safe work) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.beacon
      (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)).run before)
      (PublicAllowed (KemSK := KemSK)) := by
  simp only [RegistrationNativePublicFrontend.beacon, RegistrationNativePublicOwners.executeLocal,
    StateT.run, simulateQ_map]
  apply mapped
  apply mapped
  apply simulation _ LocalSafe PublicAllowed (local_safe false)
  exact simulation _ Beacon.Allowed LocalSafe trusted_safe _ (safe _ _)

private theorem record_safe {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : RegistrationNativePublicFrontend.State source) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before)
      (PublicAllowed (KemSK := KemSK)) := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativePublicFrontend.record, StateT.run]
  all_goals try split
  all_goals first
    | trivial
    | exact mapped _ _ PublicAllowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)

/-- Only build and finish can demand material or interpret an installation of hidden record state. -/
def Ordinary : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.build _ _) | .inr (.finish _ _) => False
  | _ => True

private theorem handler_safe (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : RegistrationNativePublicFrontend.State source)
    (ordinary : Ordinary query) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before) (PublicAllowed (KemSK := KemSK)) := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp,
        RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal]
      exact mapped _ _ PublicAllowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon_safe selectedOwner publicPrekey _ before (Beacon.create_safe setup edPin mlPin keyId)
    | bundle index => exact beacon_safe selectedOwner publicPrekey _ before (Beacon.bundle_safe setup wire index)
    | accept packet =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
        exact server_safe _ _ _ (accept_safe setup checks source.verify packet _ _)
    | build handle application | finish owner packet => exact ordinary.elim
    | hmac key bytes => trivial
    | hash bytes =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp,
          RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal]
        exact mapped _ _ PublicAllowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | serverSend keyId plaintext => exact record_safe (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_safe (.inl (.inr raw)) before
    | beaconSend owner plaintext => exact record_safe (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw => exact record_safe (.inr (owner, .inr raw)) before

private theorem translate_query (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (safe : PublicAllowed query) :
    RegistrationNativeG3MaterializedLocal.translate full seeds query =
      (RegistrationNativePublicFrontend.Spec n KemSK).query query := by
  rcases query with (message | ((message | (publication | effect)) | kem)) | record
  · rfl
  · exact safe.elim
  · rfl
  · cases effect with
    | inl coin => rfl
    | inr capability => cases capability with
      | installServer keyId binding reference => cases reference <;> first | rfl | exact safe.elim
      | installBeacon owner shell reference => cases reference <;> first | rfl | exact safe.elim
      | _ => rfl
  · rfl
  · rfl

private theorem translate_program (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (safe : AllQueriesSatisfy work (PublicAllowed (KemSK := KemSK))) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds) work = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, translate_query full seeds query allowed]
      congr 1
      funext answer
      exact ih answer (later answer)

/-- Actual ordinary typed commands retain their exact open callback AST, with every failure, parsed counter and reached roster field unchanged. -/
theorem handler_source (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (frontend : RegistrationNativePublicFrontend.State source)
    (ordinary : Ordinary query) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend) =
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend) :=
  translate_program full seeds _ (handler_safe setup checks wire source sign selectedOwner selectedAccept publicPrekey query frontend ordinary)

private theorem observed_translate_program (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (safe : AllQueriesSatisfy work (PublicAllowed (KemSK := KemSK))) (trace : RegistrationNativeG2Trace.State) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      ((simulateQ RegistrationNativeG2Trace.handler work).run trace) =
      ((simulateQ RegistrationNativeG2Trace.handler work).run trace) := by
  induction work using OracleComp.inductionOn generalizing trace with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      simp only [RegistrationNativeG2Trace.handler, StateT.run, bind_map_left, simulateQ_map,
        simulateQ_spec_query, translate_query full seeds query allowed]
      apply bind_congr
      intro reply
      exact ih reply (later reply) (RegistrationNativeG2Trace.finish query reply (RegistrationNativeG2Trace.begin query trace))

/-- Ordinary typed commands retain their complete original chronological G2 observer under literal materialization. -/
theorem observed_handler_source (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (frontend : RegistrationNativePublicFrontend.State source)
    (ordinary : Ordinary query) (trace : RegistrationNativeG2Trace.State) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend)).run trace) =
      ((simulateQ RegistrationNativeG2Trace.handler
        ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run frontend)).run trace) :=
  observed_translate_program full seeds _
    (handler_safe setup checks wire source sign selectedOwner selectedAccept publicPrekey query frontend ordinary) trace

/-- The actual native birth/outgoing interface counts every installation, including concrete known kernels. -/
def TrustedInstall (role : PqxdhRecordLiftInterface.Role) : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain → Prop
  | .inl (.inr (.installServer _ _ _)) => role = .server
  | .inl (.inr (.installBeacon _ _ _)) => role = .beacon
  | _ => False
instance (role : PqxdhRecordLiftInterface.Role) : DecidablePred (TrustedInstall (n := n) (KemSK := KemSK) role) := fun query => by
  cases query with
  | inl effect => cases effect with
    | inl coin => exact isFalse id
    | inr capability => cases capability <;> dsimp only [TrustedInstall] <;> infer_instance
  | inr query => exact isFalse id

private theorem allowed_not_install (role : PqxdhRecordLiftInterface.Role)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) (safe : Beacon.Allowed query) :
    ¬TrustedInstall role query := by
  cases query with
  | inl effect => cases effect with
    | inl coin => exact id
    | inr capability => cases capability <;> simp_all only [Beacon.Allowed, EffectAllowed, TrustedInstall, not_false_eq_true]
  | inr query => exact id

private theorem safe_zero (role : PqxdhRecordLiftInterface.Role)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (safe : AllQueriesSatisfy work (Beacon.Allowed (KemSK := KemSK))) : work.IsQueryBoundP (TrustedInstall (KemSK := KemSK) role) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      have notInstall := allowed_not_install role query allowed
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl notInstall, ?_⟩
      intro reply
      simpa only [notInstall, ite_false] using ih reply (later reply)

/-- Actual constructor preflights and its total birth suffix never attempt a Server or Beacon installation. -/
theorem native_create_free {Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
    (role : PqxdhRecordLiftInterface.Role) (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env).IsQueryBoundP
      (TrustedInstall (KemSK := KemSK) role) 0 :=
  safe_zero role _ (Beacon.create_safe setup edPin mlPin keyId owners env)

/-- Actual native outgoing publication, including all failure and signing paths, attempts no installation. -/
theorem native_bundle_free {Auxiliary : Type} {source : RegistrationNativeMldsa.Source}
    (role : PqxdhRecordLiftInterface.Role) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativeBeaconFrontend.bundle (n := n) setup source wire index).run owners).run env).IsQueryBoundP
      (TrustedInstall (KemSK := KemSK) role) 0 :=
  safe_zero role _ (Beacon.bundle_safe setup wire index owners env)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.native_create_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.native_create_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.native_bundle_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.native_bundle_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.observed_handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedOrdinary.observed_handler_source
