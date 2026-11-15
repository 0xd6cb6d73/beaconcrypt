-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialLocal
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformServerMaterialCaps
import BeaconcryptCore.Computational.RegistrationNativeMaterialBudget
/-! Literal material-demand bills for the corrected common-P public frontend. Only build and finish can demand paired material, at most once per callback. Adaptive typed and original raw-mode programs retain the sum of their build and finish allowances. Actual writer/allocation failures and all external coin branches are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativePlatformPublicMaterialLocal (IsLocalDemand)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι}
abbrev IsDemand := RegistrationNativePlatformPublicMaterialLocal.IsDemand (n := n) (KemSK := KemSK)
abbrev IsMaterial := RegistrationNativePublicCaps.IsMaterial

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl message =>
    simp only [RegistrationNativePublicOwners.ordinary, RegistrationBeaconReferenceCaps.IsDemand, ite_false]
    split <;> simp [RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  | inr query =>
    rcases query with (_ | _) | _ <;>
      simp [RegistrationNativePublicOwners.ordinary, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]

private theorem finish_local (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((finish (n := n) setup wire source index packet).run owners).run env).run before).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) 1 := by
  simp only [finish, StateT.run]
  cases found : owners[index]? with
  | none => trivial
  | some owner =>
    simp only [map_apply, isQueryBoundP_map_iff]
    apply RegistrationNativePlatformPublicMaterialLocal.local_handler_bound
    cases owner.scalar with
    | none => exact RegistrationNativePlatformBeaconMaterialCaps.finish_bound setup wire source packet owner.view env
    | some scalar => exact ordinary_bound setup scalar _ 1 (RegistrationNativePlatformBeaconMaterialCaps.finish_bound setup wire source packet owner.view env)

private theorem build_embedding (work : OracleComp (RegistrationNativePlatformServerFrontendCompiler.Spec n) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformServerMaterialCaps.IsDemand (n := n)) count) :
    (simulateQ (buildEmbedding (KemSK := KemSK)) work).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ _ bounded
  intro query
  rcases query with message | query | coin <;>
    simp [buildEmbedding, effect, localQuery, localCoin, IsLocalDemand, RegistrationNativePlatformServerMaterialCaps.IsDemand, isQueryBoundP_query_iff]

private theorem beacon_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State (Base n KemSK Platform) Value)
    (count : Nat) (bounded : ∀ owners env previous, (((work.run owners).run env).run previous).IsQueryBoundP (IsLocalDemand (KemSK := KemSK)) count)
    (before : State source Platform) :
    ((executeLocal (beacon work)).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) count := by
  apply RegistrationNativePlatformPublicMaterialLocal.embed_bound
  simp only [beacon, StateT.run, isQueryBoundP_map_iff]
  exact bounded _ _ _

private theorem coins_free (work : ProbComp Value) :
    (simulateQ (publicCoin (n := n) (KemSK := KemSK)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [publicCoin, IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, isQueryBoundP_query_iff]

private theorem gate_free {A : Type} (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (n := 0) (m := 0) (coins_free _)
    rintro ⟨result, after⟩ _
    cases result <;> trivial

private theorem effect_free {source : RegistrationNativeMldsa.Source}
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State source Platform) :
    ((executeLocal (StateT.lift (effect (KemSK := KemSK) query))).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  change (simulateQ embedLocal ((StateT.lift (effect query) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP _ 0
  simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
  simp [effect, localQuery, embedLocal, IsDemand,
    RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

private theorem record_free {source : RegistrationNativeMldsa.Source}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run, old]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, ite_false] using gate_free reserve _ output before.2
  · simp [record, StateT.run, old, isQueryBoundP_map_iff,
      IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · simp only [old]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, ite_false] using gate_free reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [old, isQueryBoundP_map_iff, IsDemand, RegistrationNativePlatformPublicMaterialLocal.IsDemand, RegistrationNativePublicCaps.IsDemand, isQueryBoundP_query_iff]

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/- The corrected OPEN accept selects the Server pin purely (no fingerprint hash query), so elaboration-time defeq checks
   on terms containing the concrete accept program would evaluate through `begin_server_pin`; keep it opaque here. -/
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept in
/-- Only the actual corrected build and finish callbacks may demand material, once each. -/
theorem handler_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation query).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (if IsMaterial query then 1 else 0) := by
  cases query with
  | inl coin => exact effect_free (.inl coin) before
  | inr query => cases query with
    | create edPin mlPin keyId =>
      exact beacon_bound _ 0 (RegistrationNativePlatformPublicMaterialLocal.create_zero setup source selectedOwner publicPrekey edPin mlPin keyId) before
    | bundle index =>
      change (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)).IsQueryBoundP _ 0
      apply RegistrationNativePlatformPublicMaterialLocal.embed_bound
      simp only [beacon, StateT.run, map_apply, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicMaterialLocal.bundle_zero setup source implementation selectedOwner publicPrekey index _ _ _
    | accept packet =>
      change (simulateQ embedLocal ((do
        let previous ← get
        modify fun current => ({current.1 with parsedAccepts := current.1.parsedAccepts + 1}, current.2)
        serverOpen (RegistrationNativePlatformServerOpenControl.accept
          (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) (decide (previous.1.parsedAccepts = selectedAccept)))
          (platform reserveRegistration) setup checks source.verify packet) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP _ 0
      apply RegistrationNativePlatformPublicMaterialLocal.embed_bound
      simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
      simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicMaterialLocal.accept_zero (n := n) (KemSK := KemSK)
        (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet
        before.1.server before.1.environment before.2
    | build handle application =>
      apply RegistrationNativePlatformPublicMaterialLocal.embed_bound
      simp only [build, StateT.run, isQueryBoundP_map_iff]
      apply build_embedding
      exact RegistrationNativePlatformServerMaterialCaps.build setup.source view failure allocation erased helper sign implementation reservePeer handle application _ _
    | finish index packet => exact beacon_bound _ 1 (finish_local setup wire source index packet) before
    | hmac key bytes => trivial
    | hash bytes => exact effect_free (.inr (.hash bytes)) before
    | serverSend keyId plaintext => exact record_free reserveFrame (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free reserveFrame (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_free reserveFrame (.inr (index, .inr raw)) before

/-- The complete typed adaptive public frontend preserves its material-command allowance, retaining the same mutable platform state on every branch. -/
theorem program_bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsMaterial count) (before : State source Platform) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation) work).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query current

/-- Original raw-mode execution consumes at most qBuild+qFinish material demands. Hidden tests and fresh bytes add no material query. -/
theorem run_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source Platform) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation serverKeyId bounds mode work before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  apply program_bound setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation _ _ _ before
  have bill := RegistrationNativeMaterialBudget.compile_bound setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work budget bounded
  rw [RegistrationNativeMaterialBudget.allowance_eq] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  cases query with
  | inl coin => exact counted.elim
  | inr query => cases query <;> simp_all [IsMaterial, RegistrationNativePublicCaps.IsMaterial,
      RegistrationNativeMaterialBudget.IsMaterial, RegistrationNativeRawAdapter.kind]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicMaterialCaps.run_bound
