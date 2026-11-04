-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields

/-! Effectful actual source Init publication and bundle generation retain every immutable owner field for arbitrary writer replies and failed prefixes. Only phase and chronological Ed-signing history are omitted by the existing structural metadata projection; private identity, ML credential, scalar/public prekey, KEM handle/public key and pins remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
open RegistrationNativeBeaconFrontend (Owner Phase Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeOwnerFields (metadata)
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {κ ι KemSK Auxiliary V W Encoded : Type} {base : OracleSpec ι} {target : OracleSpec κ}
variable {source : RegistrationNativeMldsa.Source}

private abbrev M (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) (target : OracleSpec κ) (V : Type) :=
  RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp target) V
private def Keeps (work : M source Auxiliary target V) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2.map metadata = owners.map metadata
private def SourceKeeps (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary V) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2.map metadata = owners.map metadata

private theorem pure_keeps (value : V) : Keeps (pure value : M source Auxiliary target V) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_keeps (work : M source Auxiliary target V) (next : V → M source Auxiliary target W)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle called)
private theorem lift_keeps (work : StateT (EnvState Auxiliary) (OracleComp target) V) :
    Keeps (StateT.lift work : M source Auxiliary target V) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _called, same⟩ := supported
  cases same
  rfl
private theorem get_keeps : Keeps (get : M source Auxiliary target (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem simulate_support {Q : Type} {spec : OracleSpec Q} (implementation : QueryImpl spec (OracleComp target))
    (work : OracleComp spec V) (value : V) (supported : value ∈ support (simulateQ implementation work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure input =>
    simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported ⊢
    exact supported
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩
private theorem legacy_keeps (implementation : QueryImpl (Trusted n KemSK) (OracleComp target))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary V) (law : SourceKeeps work) :
    Keeps (RegistrationNativePlatformGenericBundle.liftLegacy implementation work) := by
  intro owners env result supported
  exact law owners env result (simulate_support implementation _ result supported)

private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → M source Auxiliary target (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (next value)) : Keeps (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (encode view)) (pending : registration.BeaconInitReady) : Keeps (ready encode pending) := by
  unfold ready
  exact continue_keeps _ _ fun view => bind_keeps _ _ (law view) fun _ => pure_keeps _
private theorem signing_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M source Auxiliary target))
    (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    Keeps (fromSigning impl encode payload digest pending) := by
  unfold fromSigning
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro signature
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ready_keeps encode encoding _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M source Auxiliary target))
    (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconInitHash) : Keeps (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact signing_keeps impl encode queries encoding _ _ _
private theorem fingerprint_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M source Auxiliary target))
    (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconFingerprint) : Keeps (fromFingerprint impl encode pending) := by
  unfold fromFingerprint
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro digest
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact hash_keeps impl encode queries encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M source Auxiliary target))
    (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps _ _
  intro request
  apply bind_keeps _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | FingerprintRequested selected => exact fingerprint_keeps impl encode queries encoding selected
    | _ => exact pure_keeps _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M source Auxiliary target))
    (encode : registration.SignedInitView → M source Auxiliary target (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ed_keeps impl encode queries encoding _

private theorem simulate_keeps {Q : Type} {spec : OracleSpec Q}
    (impl : QueryImpl spec (M source Auxiliary target)) (law : ∀ query, Keeps (impl query))
    (work : OracleComp spec V) : Keeps (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps value
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact bind_keeps _ _ (law query) ih
private theorem source_lift (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) V) :
    SourceKeeps (StateT.lift work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary V) :=
  lift_keeps work
private theorem source_sample (work : ProbComp V) :
    SourceKeeps (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  unfold RegistrationNativeBeaconFrontend.sample
  exact simulate_keeps (target := Trusted n KemSK) (spec := unifSpec)
    (fun query => RegistrationNativeBeaconFrontend.effect (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) (.inl query))
    (fun _ => lift_keeps _) work
private theorem source_phase (index : Nat) (phase : Phase) :
    SourceKeeps (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) := by
  intro owners env result supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => rfl
  | some owner =>
    simp only [List.map_set]
    have lookup : (owners.map metadata)[index]? = some (metadata owner) := by simp [found]
    obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp lookup
    change (owners.map metadata).set index (metadata owner) = owners.map metadata
    rw [← selected]
    exact List.set_getElem_self below

private theorem outgoing_keeps (implementation : QueryImpl (Trusted n KemSK) (OracleComp target))
    (setup : Setup base KemSK) (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (RegistrationNativePlatformGenericBundle.liftLegacy implementation (RegistrationNativeBeaconFrontend.outgoing (Auxiliary := Auxiliary) setup source index owner query)) := by
  apply legacy_keeps implementation
  intro owners env result supported
  have law := RegistrationNativeOwnerFields.outgoing_metadata (n := n) setup source index owner
    (RegistrationBeaconInitExecutor.Spec.query query) owners env result
  simp only [simulateQ_spec_query] at law
  exact law supported

/-- The complete free actual source bundle preserves all immutable owner metadata, independently of every typed writer outcome. -/
theorem program {E : Type} (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (index : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source index).run owners).run env)) :
    result.1.2.map metadata = owners.map metadata := by
  have law : Keeps (RegistrationNativePlatformGenericBundle.program (n := n) (Auxiliary := Auxiliary) E setup source index) := by
    unfold RegistrationNativePlatformGenericBundle.program RegistrationNativePlatformGenericBundle.bundle
    apply bind_keeps _ _ get_keeps
    intro current
    cases current[index]? with
    | none => exact pure_keeps _
    | some owner =>
      dsimp only
      cases owner.phase with
      | fresh | freshWithCoins _ =>
        apply bind_keeps _ _ ?_
        · intro oneTime
          apply bind_keeps _ _ (publication _ _
            (outgoing_keeps _ setup index owner) (fun _ => lift_keeps _) _ _ _ _ _)
          intro published
          cases published with
          | fail error | div => exact pure_keeps _
          | ok answer => cases answer with
            | Err previous => exact pure_keeps _
            | Ok completed =>
              apply bind_keeps _ _ (legacy_keeps _ _ (source_phase index _))
              intro ignored
              exact bind_keeps _ _ (legacy_keeps _ _ (source_lift _)) (fun _ => pure_keeps _)
        · first | exact pure_keeps _ | exact legacy_keeps _ _ (source_sample _)
      | _ => exact pure_keeps _
  exact law owners env result supported

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem interpreted_support {Q N P A : Type} {spec : OracleSpec Q}
    (implementation : QueryImpl spec (StateT N (StateT P ProbComp)))
    (work : OracleComp spec A) (value : A) (before after : N) (previous next : P)
    (supported : ((value, after), next) ∈ support (((simulateQ implementation work).run before).run previous)) : value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before after previous next with
  | pure input =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    rw [support_pure, Set.mem_singleton_iff]
    exact supported.1.1
  | query_bind query continuation ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨reply, middle⟩, platform⟩, _called, continued⟩ := supported
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply middle after platform next continued⟩

/-- Actual shared-state Platform bundle outcomes restore the same immutable owner metadata into the complete native envelope, for every allocator/writer failure or success. -/
theorem native_bundle {E Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    after.beacons.map metadata = before.beacons.map metadata := by
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨raw, platform⟩, called, same⟩ := supported
  have beacons : after.beacons = raw.1.1.2 := (congrArg (fun value => value.1.2.beacons) same).symm
  have original := interpreted_support (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (((RegistrationNativePlatformGenericBundle.program E setup source index).run before.beacons).run
      (RegistrationWorldAgreementCompiler.erase before.server.world)) raw.1 before raw.2 previous platform called
  rw [beacons]
  exact program setup source index before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) raw.1 original

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata.native_bundle
