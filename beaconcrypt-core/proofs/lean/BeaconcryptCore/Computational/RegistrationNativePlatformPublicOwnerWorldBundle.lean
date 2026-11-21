-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublication
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLifecycleOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativeBundlePhases
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerWorldBundle
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Phase Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordLifecycleOwnerPhase (NativeDone Done Terminal)
open RegistrationNativeBundlePhases (phases)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E I KemSK Auxiliary V W Encoded : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
private abbrev M (E : Type) (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK))
private def metadata (owner : RegistrationNativeBeaconFrontend.Owner source) : Nat := owner.worldOwner
def key (owner : RegistrationNativePublicOwners.Owner source) : Nat := owner.view.worldOwner
private theorem pack_keys (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) :
    (RegistrationNativePublicOwners.pack selected publicPrekey owners).map key = owners.map metadata := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, RegistrationNativePublicOwners.pack, List.getElem?_mapIdx]
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
      by_cases chosen : index = selected <;>
        simp only [Option.map_some, chosen, ite_true, ite_false, key, metadata,
          RegistrationBeaconReferenceCompiler.eraseOwner]
private theorem restore_keys (owners : RegistrationNativePublicOwners.State source) :
    (owners.map RegistrationNativePublicOwners.restore).map metadata = owners.map key := by
  simp only [List.map_map]
  rfl
variable (expected : List Nat)
private def Keeps (work : M E n KemSK Auxiliary source V) : Prop :=
  ∀ owners env result, owners.map metadata = expected → result ∈ support ((work.run owners).run env) → result.1.2.map metadata = expected
private theorem pure_keeps (value : V) : Keeps expected (pure value : M E n KemSK Auxiliary source V) := by
  intro owners env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : M E n KemSK Auxiliary source V) (next : V → M E n KemSK Auxiliary source W)
    (first : Keeps expected work) (later : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owners env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact later middle.1.1 middle.1.2 middle.2 result (first owners env middle valid reached) continued
private theorem lift_keeps (work : StateT (EnvState Auxiliary)
    (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK)) V) :
    Keeps expected (StateT.lift work : M E n KemSK Auxiliary source V) := by
  intro owners env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid
private theorem legacy_keeps (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary V)
    (law : ∀ owners env result, owners.map metadata = expected → result ∈ support ((work.run owners).run env) → result.1.2.map metadata = expected) :
    Keeps expected (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) work) := by
  intro owners env result valid supported
  exact law owners env result valid (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported)
private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps expected (next value)) : Keeps expected (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps expected _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.InitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps expected (encode view)) (pending : registration.BeaconInitReady) : Keeps expected (ready encode pending) := by
  unfold ready
  exact continue_keeps expected _ _ fun view => bind_keeps expected _ _ (law view) fun _ => pure_keeps expected _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.InitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps expected (impl query)) (encoding : ∀ view, Keeps expected (encode view))
    (pending : registration.BeaconInitHash) : Keeps expected (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps expected _ _
  intro request
  apply bind_keeps expected _ _ (queries _)
  intro digest
  apply continue_keeps expected _ _
  intro effect
  cases effect <;> first | exact pure_keeps expected _ | exact ready_keeps expected encode encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.InitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps expected (impl query)) (encoding : ∀ view, Keeps expected (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps expected (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps expected _ _
  intro request
  apply bind_keeps expected _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps expected _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps expected _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | HashRequested selected => exact hash_keeps expected impl encode queries encoding selected
    | _ => exact pure_keeps expected _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner addresses under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.InitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps expected (impl query)) (encoding : ∀ view, Keeps expected (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Keeps expected (begin impl encode control inputs coins pin) := by
  unfold begin
  apply continue_keeps expected _ _
  intro effect
  cases effect <;> first | exact pure_keeps expected _ | exact ed_keeps expected impl encode queries encoding _


private theorem legacy_lift (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) V) :
    Keeps expected (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) (StateT.lift work) : M E n KemSK Auxiliary source V) := by
  apply legacy_keeps expected _
  intro owners env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid
private theorem legacy_sample (draw : ProbComp V) :
    Keeps expected (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) draw)) := by
  induction draw using OracleComp.inductionOn with
  | pure value =>
      simpa only [RegistrationNativeBeaconFrontend.sample, simulateQ_pure,
        RegistrationNativePlatformGenericBundle.liftLegacy_pure] using pure_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected value
  | query_bind query next ih =>
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativePlatformGenericBundle.liftLegacy_bind]
      exact bind_keeps expected _ _ (legacy_lift expected _) ih
private theorem outgoing_keeps (setup : Setup base KemSK) (target : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps expected (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source target owner query)) := by
  apply legacy_keeps expected _
  intro owners env result valid supported
  have unchanged := RegistrationNativeOwnerFields.outgoing_metadata setup source target owner
    (RegistrationBeaconInitExecutor.Spec.query query : OracleComp RegistrationBeaconInitExecutor.Spec _)
    owners env result (by simpa only [simulateQ_spec_query] using supported)
  have projected := congrArg (List.map fun current => current.worldOwner) unchanged
  have keys : result.1.2.map metadata = owners.map metadata := by
    change result.1.2.map (fun current => current.worldOwner) = owners.map (fun current => current.worldOwner)
    simpa only [List.map_map, Function.comp_def, RegistrationNativeOwnerFields.metadata] using projected
  exact keys.trans valid
private theorem phase_keeps (target : Nat) (phase : Phase) :
    Keeps expected (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) target phase)) := by
  apply legacy_keeps expected _
  intro owners env result valid supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : owners[target]? with
  | none => simpa only [found] using valid
  | some owner =>
      have kept : (owners.set target {owner with phase}).map metadata = owners.map metadata := by
        rw [List.map_set]
        change (owners.map metadata).set target (metadata owner) = owners.map metadata
        have selected : (owners.map metadata)[target]? = some (metadata owner) := by
          simp only [List.getElem?_map, found, Option.map_some]
        obtain ⟨below, atIndex⟩ := List.getElem?_eq_some_iff.mp selected
        rw [← atIndex]
        exact List.set_getElem_self below
      simpa only [found] using kept.trans valid
private theorem encoder_keeps (view : registration.InitView) :
    Keeps expected (RegistrationNativePlatformGenericBundle.encoder (Auxiliary := Auxiliary) (source := source) (n := n) (KemSK := KemSK) E view) :=
  lift_keeps expected _
private theorem published_keeps (setup : Setup base KemSK) (target : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps expected (RegistrationNativePlatformBeaconPublication.begin
      (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.outgoing setup source target owner query))
      (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin :
      M E n KemSK Auxiliary source _) :=
  publication expected _ _ (outgoing_keeps expected setup target owner) (encoder_keeps expected) _ _ _ _
private theorem next_keeps (target : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    Keeps expected (match reply with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
          RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
            (RegistrationNativeBeaconFrontend.updatePhase target (.initSent finished.pending oneTime))
          let _ ← RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
            (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
          pure (.ok (some finished.encoded)) : M E n KemSK Auxiliary source (RustM (Option (alloc.vec.Vec U8)))) := by
  cases reply with
  | fail error | div => exact pure_keeps expected _
  | ok selected => cases selected with
    | Err error => exact pure_keeps expected _
    | Ok completed => exact bind_keeps expected _ _ (phase_keeps expected target _) (fun _ => bind_keeps expected _ _ (legacy_lift expected _) (fun _ => pure_keeps expected _))
attribute [local irreducible] RegistrationNativePlatformBeaconPublication.begin RegistrationNativeBeaconFrontend.sample
  RegistrationNativeBeaconFrontend.outgoing RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.encoder
/-- The actual free dynamic-writer bundle preserves every physical owner address. -/
private theorem program_keeps (setup : Setup base KemSK) (target : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (valid : owners.map metadata = expected) (supported : result ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) (KemSK := KemSK) E setup source target).run owners).run env)) :
    result.1.2.map metadata = expected := by
  simp only [RegistrationNativePlatformGenericBundle.program, RegistrationNativePlatformGenericBundle.bundle,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[target]? with
  | none => simp only [found, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact valid
  | some owner =>
      simp only [found] at supported
      cases phase : owner.phase with
      | initSent _ _ | established _ | aborted _ =>
          simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          exact valid
      | fresh =>
          simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨⟨oneTime, middleOwners⟩, middleEnv⟩, sampled, supported⟩ := supported
          have middleValid := legacy_sample (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected PqxdhJointGapDh.sampleScalar
            owners env ((oneTime, middleOwners), middleEnv) valid sampled
          obtain ⟨⟨⟨reply, afterOwners⟩, afterEnv⟩, published, continued⟩ := supported
          have afterValid := published_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected setup target owner oneTime
            middleOwners middleEnv ((reply, afterOwners), afterEnv) middleValid published
          have afterStep := next_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected target owner oneTime
          cases reply with
          | fail error => exact afterStep (.fail error) afterOwners afterEnv result afterValid continued
          | div => exact afterStep .div afterOwners afterEnv result afterValid continued
          | ok selected => cases selected with
            | Err error => exact afterStep (.ok (.Err error)) afterOwners afterEnv result afterValid continued
            | Ok finished => exact afterStep (.ok (.Ok finished)) afterOwners afterEnv result afterValid continued
      | freshWithCoins oneTime =>
          simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨⟨⟨reply, afterOwners⟩, afterEnv⟩, published, continued⟩ := supported
          have afterValid := published_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected setup target owner oneTime
            owners env ((reply, afterOwners), afterEnv) valid published
          have afterStep := next_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) expected target owner oneTime
          cases reply with
          | fail error => exact afterStep (.fail error) afterOwners afterEnv result afterValid continued
          | div => exact afterStep .div afterOwners afterEnv result afterValid continued
          | ok selected => cases selected with
            | Err error => exact afterStep (.ok (.Err error)) afterOwners afterEnv result afterValid continued
            | Ok finished => exact afterStep (.ok (.Ok finished)) afterOwners afterEnv result afterValid continued

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
variable {Q Platform : Type} {targetSpec : OracleSpec Q}
/-- Actual public bundle preserves every physical owner address through arbitrary stateful source writers and all failures. -/
theorem public_worlds (setup : Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Platform (OracleComp targetSpec)))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform (OracleComp targetSpec)))
    (selected target : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (supported : result ∈ support
      ((((RegistrationNativePlatformPublicOwners.bundle implementation writer setup source selected publicPrekey target).run owners).run env).run previous)) :
    result.1.1.2.map key = owners.map key := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  let dictionary : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Platform (OracleComp targetSpec)) :=
    fun query => match query with | .inl query => implementation query | .inr query => writer query
  have translated := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := Auxiliary) dictionary setup source target
  have original : middle.1 ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source target).run (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply OracleComp.support_simulateQ_run'_subset dictionary _ previous
    rw [StateT.run'_eq, support_map]
    refine ⟨middle, ?_, rfl⟩
    change middle ∈ support ((((RegistrationNativePlatformGenericBundle.evaluate dictionary
      (RegistrationNativePlatformGenericBundle.program (n := n) E setup source target)).run (owners.map RegistrationNativePublicOwners.restore)).run env).run previous)
    rw [translated]
    exact reached
  have kept := program_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source)
    ((owners.map RegistrationNativePublicOwners.restore).map metadata) setup target
    (owners.map RegistrationNativePublicOwners.restore) env middle.1 rfl original
  cases equal
  simp only [Prod.map_def, id_eq]
  rw [pack_keys, kept, restore_keys]
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerWorldBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerWorldBundle.public_worlds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwnerWorldBundle.public_worlds
