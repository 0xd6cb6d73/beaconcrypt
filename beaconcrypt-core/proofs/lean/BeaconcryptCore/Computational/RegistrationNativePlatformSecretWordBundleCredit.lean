-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Phase Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordLifecycleOwnerPhase (NativeDone Done Terminal)
open RegistrationNativeBundlePhases (phases)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E I KemSK Auxiliary V W Encoded : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
private abbrev M (E : Type) (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformGenericBundle.M source Auxiliary (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK))
variable (index : Nat)
private def Keeps (work : M E n KemSK Auxiliary source V) : Prop :=
  ∀ owners env result, NativeDone index owners → result ∈ support ((work.run owners).run env) → NativeDone index result.1.2
private theorem pure_keeps (value : V) : Keeps index (pure value : M E n KemSK Auxiliary source V) := by
  intro owners env result valid supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact valid
private theorem bind_keeps (work : M E n KemSK Auxiliary source V) (next : V → M E n KemSK Auxiliary source W)
    (first : Keeps index work) (later : ∀ value, Keeps index (next value)) : Keeps index (work >>= next) := by
  intro owners env result valid supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact later middle.1.1 middle.1.2 middle.2 result (first owners env middle valid reached) continued
private theorem lift_keeps (work : StateT (EnvState Auxiliary)
    (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK)) V) :
    Keeps index (StateT.lift work : M E n KemSK Auxiliary source V) := by
  intro owners env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid
private theorem legacy_keeps (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary V)
    (law : ∀ owners env result, NativeDone index owners → result ∈ support ((work.run owners).run env) → NativeDone index result.1.2) :
    Keeps index (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) work) := by
  intro owners env result valid supported
  exact law owners env result valid (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported)
private theorem phases_done (before after : RegistrationNativeBeaconFrontend.State source)
    (equal : phases after = phases before) (valid : NativeDone index before) : NativeDone index after := by
  obtain ⟨owner, found, terminal⟩ := valid
  have selected : (phases after)[index]? = some owner.phase := by
    rw [equal]
    simp only [phases, List.getElem?_map, found, Option.map_some]
  simp only [phases, List.getElem?_map, Option.map_eq_some_iff] at selected
  obtain ⟨current, atIndex, samePhase⟩ := selected
  exact ⟨current, atIndex, samePhase ▸ terminal⟩
private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps index (next value)) : Keeps index (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps index _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps index (encode view)) (pending : registration.BeaconInitReady) : Keeps index (ready encode pending) := by
  unfold ready
  exact continue_keeps index _ _ fun view => bind_keeps index _ _ (law view) fun _ => pure_keeps index _
private theorem signing_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps index (impl query)) (encoding : ∀ view, Keeps index (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest) (pending : registration.BeaconMldsaSigning) :
    Keeps index (fromSigning impl encode payload digest pending) := by
  unfold fromSigning
  apply continue_keeps index _ _
  intro request
  apply bind_keeps index _ _ (queries _)
  intro signature
  apply continue_keeps index _ _
  intro effect
  cases effect <;> first | exact pure_keeps index _ | exact ready_keeps index encode encoding _
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps index (impl query)) (encoding : ∀ view, Keeps index (encode view))
    (pending : registration.BeaconInitHash) : Keeps index (fromHash impl encode pending) := by
  unfold fromHash
  apply continue_keeps index _ _
  intro request
  apply bind_keeps index _ _ (queries _)
  intro digest
  apply continue_keeps index _ _
  intro effect
  cases effect <;> first | exact pure_keeps index _ | exact signing_keeps index impl encode queries encoding _ _ _
private theorem fingerprint_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps index (impl query)) (encoding : ∀ view, Keeps index (encode view))
    (pending : registration.BeaconFingerprint) : Keeps index (fromFingerprint impl encode pending) := by
  unfold fromFingerprint
  apply continue_keeps index _ _
  intro request
  apply bind_keeps index _ _ (queries _)
  intro digest
  apply continue_keeps index _ _
  intro effect
  cases effect <;> first | exact pure_keeps index _ | exact hash_keeps index impl encode queries encoding _
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps index (impl query)) (encoding : ∀ view, Keeps index (encode view))
    (pending : registration.BeaconEd25519Signing) : Keeps index (fromEd impl encode pending) := by
  rw [fromEd.eq_def]
  apply continue_keeps index _ _
  intro request
  apply bind_keeps index _ _ (queries _)
  intro reply
  cases resumed : pending.resume reply with
  | fail error | div => exact pure_keeps index _
  | ok effect => cases effect with
    | Rejected previous => exact pure_keeps index _
    | Ed25519SigningRequested next => exact ed_keeps impl encode queries encoding next
    | FingerprintRequested selected => exact fingerprint_keeps index impl encode queries encoding selected
    | _ => exact pure_keeps index _
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

/-- Every actual source publication stage preserves owner metadata under arbitrary crypto/writer replies, including failure and recursive Ed-signing stages. -/
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary)))
    (encode : registration.SignedInitView → M (E := E) (n := n) (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps index (impl query)) (encoding : ∀ view, Keeps index (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps index (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps index _ _
  intro effect
  cases effect <;> first | exact pure_keeps index _ | exact ed_keeps index impl encode queries encoding _


private theorem legacy_lift (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) V) :
    Keeps index (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) (StateT.lift work) : M E n KemSK Auxiliary source V) := by
  apply legacy_keeps index _
  intro owners env result valid supported
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, support_map] at supported
  obtain ⟨returned, _reached, equal⟩ := supported
  cases equal
  exact valid
private theorem legacy_sample (draw : ProbComp V) :
    Keeps index (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) draw)) := by
  induction draw using OracleComp.inductionOn with
  | pure value =>
      simpa only [RegistrationNativeBeaconFrontend.sample, simulateQ_pure,
        RegistrationNativePlatformGenericBundle.liftLegacy_pure] using pure_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index value
  | query_bind query next ih =>
      simp only [RegistrationNativeBeaconFrontend.sample, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativePlatformGenericBundle.liftLegacy_bind]
      exact bind_keeps index _ _ (legacy_lift index _) ih
private theorem outgoing_keeps (setup : Setup base KemSK) (target : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps index (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := Auxiliary) setup source target owner query)) := by
  apply legacy_keeps index _
  intro owners env result valid supported
  apply phases_done index owners result.1.2 _ valid
  exact RegistrationNativeBundlePhases.outgoing_phases setup target owner
    (RegistrationBeaconInitExecutor.Spec.query query : OracleComp RegistrationBeaconInitExecutor.Spec _)
    owners env result (by simpa only [simulateQ_spec_query] using supported)
private theorem phase_foreign (target : Nat) (different : index ≠ target) (phase : Phase) :
    Keeps index (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E))
      (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) target phase)) := by
  apply legacy_keeps index _
  intro owners env result valid supported
  simp only [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  cases found : owners[target]? with
  | none => simpa only [found] using valid
  | some owner =>
      obtain ⟨earlier, atIndex, terminal⟩ := valid
      refine ⟨earlier, ?_, terminal⟩
      simpa only [found, List.getElem?_set_ne (Ne.symm different)] using atIndex
private theorem encoder_keeps (view : registration.SignedInitView) :
    Keeps index (RegistrationNativePlatformGenericBundle.encoder (Auxiliary := Auxiliary) (source := source) (n := n) (KemSK := KemSK) E view) :=
  lift_keeps index _
private theorem published_keeps (setup : Setup base KemSK) (target : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Keeps index (RegistrationNativePlatformBeaconPublication.begin
      (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.outgoing setup source target owner query))
      (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin owner.mldsa.publicKey :
      M E n KemSK Auxiliary source _) :=
  publication index _ _ (outgoing_keeps index setup target owner) (encoder_keeps index) _ _ _ _ _
private theorem next_keeps (target : Nat) (different : index ≠ target) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    Keeps index (match reply with
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
  | fail error | div => exact pure_keeps index _
  | ok selected => cases selected with
    | Err error => exact pure_keeps index _
    | Ok completed => exact bind_keeps index _ _ (phase_foreign index target different _) (fun _ => bind_keeps index _ _ (legacy_lift index _) (fun _ => pure_keeps index _))
attribute [local irreducible] RegistrationNativePlatformBeaconPublication.begin RegistrationNativeBeaconFrontend.sample
  RegistrationNativeBeaconFrontend.outgoing RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.encoder
/-- The actual free dynamic-writer bundle cannot revive any earlier terminal source owner. -/
theorem program_done (setup : Setup base KemSK) (target : Nat)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary)
    (result : (RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary)
    (valid : NativeDone index owners) (supported : result ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) (KemSK := KemSK) E setup source target).run owners).run env)) :
    NativeDone index result.1.2 := by
  simp only [RegistrationNativePlatformGenericBundle.program, RegistrationNativePlatformGenericBundle.bundle,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[target]? with
  | none => simp only [found, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; exact valid
  | some owner =>
      simp only [found] at supported
      by_cases same : index = target
      · subst target
        obtain ⟨earlier, atIndex, terminal⟩ := valid
        have equal := Option.some.inj (atIndex.symm.trans found)
        subst earlier
        cases phase : owner.phase <;> simp only [Terminal, phase] at terminal
        all_goals simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
        all_goals cases supported; exact ⟨owner, found, by simp only [Terminal, phase]⟩
      · cases phase : owner.phase with
        | initSent _ _ | established _ | aborted _ =>
            simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
            cases supported
            exact valid
        | fresh =>
            simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨⟨⟨oneTime, middleOwners⟩, middleEnv⟩, sampled, supported⟩ := supported
            have middleValid := legacy_sample (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index PqxdhJointGapDh.sampleScalar
              owners env ((oneTime, middleOwners), middleEnv) valid sampled
            obtain ⟨⟨⟨reply, afterOwners⟩, afterEnv⟩, published, continued⟩ := supported
            have afterValid := published_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index setup target owner oneTime
              middleOwners middleEnv ((reply, afterOwners), afterEnv) middleValid published
            have afterStep := next_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index target same owner oneTime
            cases reply with
            | fail error => exact afterStep (.fail error) afterOwners afterEnv result afterValid continued
            | div => exact afterStep .div afterOwners afterEnv result afterValid continued
            | ok selected => cases selected with
              | Err error => exact afterStep (.ok (.Err error)) afterOwners afterEnv result afterValid continued
              | Ok finished => exact afterStep (.ok (.Ok finished)) afterOwners afterEnv result afterValid continued
        | freshWithCoins oneTime =>
            simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨⟨⟨reply, afterOwners⟩, afterEnv⟩, published, continued⟩ := supported
            have afterValid := published_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index setup target owner oneTime
              owners env ((reply, afterOwners), afterEnv) valid published
            have afterStep := next_keeps (E := E) (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index target same owner oneTime
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
/-- Arbitrary stateful writer and primitive implementations retain the same terminal positions in the actual public bundle. -/
theorem bundle_done (setup : Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Platform (OracleComp targetSpec)))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform (OracleComp targetSpec)))
    (selected target : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (valid : Done index owners) (supported : result ∈ support
      ((((RegistrationNativePlatformPublicOwners.bundle implementation writer setup source selected publicPrekey target).run owners).run env).run previous)) :
    Done index result.1.1.2 := by
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
  have kept := program_done index setup target (owners.map RegistrationNativePublicOwners.restore) env middle.1
    (RegistrationNativeSecretWordLifecycleOwnerRoster.restore_done index owners valid) original
  have packed := RegistrationNativeSecretWordLifecycleOwnerRoster.pack_done index selected publicPrekey middle.1.1.2 kept
  cases equal
  exact packed
/-- The actual constructor append and every failed generation branch preserve prior consumed public owner positions. -/
theorem create_done (setup : Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Platform (OracleComp targetSpec)))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option Nat) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (valid : Done index owners) (supported : result ∈ support
      ((((RegistrationNativePlatformPublicOwners.create implementation setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous)) :
    Done index result.1.1.2 := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  have original : middle.1 ∈ support
      (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ previous
    rw [StateT.run'_eq, support_map]
    exact ⟨middle, by simpa only [RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run] using reached, rfl⟩
  have kept := RegistrationNativeSecretWordLifecycleOwnerPhase.create_done setup index edPin mlPin keyId
    (owners.map RegistrationNativePublicOwners.restore) env middle.1
    (RegistrationNativeSecretWordLifecycleOwnerRoster.restore_done index owners valid) original
  have packed := RegistrationNativeSecretWordLifecycleOwnerRoster.pack_done index selected publicPrekey middle.1.1.2 kept
  cases equal
  exact packed
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.program_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.program_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.bundle_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.bundle_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.create_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordBundleCredit.create_done
