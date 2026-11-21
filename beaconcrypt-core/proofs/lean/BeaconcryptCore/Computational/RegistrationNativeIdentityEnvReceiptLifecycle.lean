-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape
/-! Literal opaque-owner creation, corrected finishing and full effectful bundle control ignore only prior compact ML receipt payloads. Every other Env field, owner, primitive request, optional result and shared platform effect remains literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeIdentityFrontend (Owner M abort)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {I KemSK Auxiliary Platform A B E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private abbrev Nested (Owners Auxiliary : Type) (m : Type → Type) := StateT Owners (StateT (EnvState Auxiliary) m)
private def erase (env : EnvState Auxiliary) : EnvState Auxiliary := {env with receipts := []}
private def projection {Owners : Type} (before : Owners × EnvState Auxiliary) := (before.1, erase before.2)
private def pack {Owners A : Type} {m : Type → Type} [Monad m]
    (work : Nested Owners Auxiliary m A) : StateT (Owners × EnvState Auxiliary) m A := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (work.run before.1).run before.2
private def Stable {Owners A : Type} {m : Type → Type} [Monad m]
    (work : Nested Owners Auxiliary m A) : Prop := RegistrationNativePlatformViewStable.Stable projection (pack work)
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m] (value : X) (before : S) :
    (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (f : S → S) (before : S) :
    (modify f : StateT S m Unit) before = pure ((), f before) := rfl

private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) : (get : StateT S m S) before = pure (before, before) := rfl
private theorem set_apply {S : Type} {m : Type → Type} [Monad m] (value before : S) : (set value : StateT S m Unit) before = pure ((), value) := rfl

section Algebra
variable {Owners : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
private theorem pack_pure (value : A) : pack (pure value : Nested Owners Auxiliary m A) = pure value := by
  funext before
  simp only [pack, StateT.run, pure_apply, map_pure]
private theorem pack_bind (work : Nested Owners Auxiliary m A) (next : A → Nested Owners Auxiliary m B) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, bind_apply, map_bind, bind_map_left]
private theorem pure_stable (value : A) : Stable (pure value : Nested Owners Auxiliary m A) := by
  unfold Stable
  rw [pack_pure]
  exact RegistrationNativePlatformViewStable.pure_stable projection (fun _ => rfl) value
private theorem bind_stable (work : Nested Owners Auxiliary m A) (next : A → Nested Owners Auxiliary m B)
    (first : Stable work) (later : ∀ value, Stable (next value)) : Stable (work >>= next) := by
  unfold Stable at *
  rw [pack_bind]
  exact RegistrationNativePlatformViewStable.bind_stable projection _ _ first later
private theorem program_stable {J : Type} {queries : OracleSpec J} (handler : QueryImpl queries (Nested Owners Auxiliary m))
    (leaves : ∀ query, Stable (handler query)) (work : OracleComp queries A) : Stable (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable value
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable _ _ (leaves query) ih
private theorem lift_stable (work : m A) : Stable (StateT.lift (StateT.lift work) : Nested Owners Auxiliary m A) := by
  rintro ⟨owners, env⟩
  simp only [pack, StateT.run, lift_apply, map_apply, Functor.map_map, Prod.map_def, id_eq, projection, erase]
private theorem get_stable : Stable (get : Nested Owners Auxiliary m Owners) := by
  rintro ⟨owners, env⟩
  simp only [pack, StateT.run, get_apply, pure_apply, projection, erase, map_pure, Prod.map_def, id_eq]
private theorem modify_stable (f : Owners → Owners) : Stable (modify f : Nested Owners Auxiliary m Unit) := by
  rintro ⟨owners, env⟩
  simp only [pack, StateT.run, modify_apply, pure_apply, projection, erase, map_pure, Prod.map_def, id_eq]
private theorem set_stable (owners : Owners) : Stable (set owners : Nested Owners Auxiliary m Unit) := by
  rintro ⟨current, env⟩
  simp only [pack, StateT.run, set_apply, pure_apply, projection, erase, map_pure, Prod.map_def, id_eq]
private theorem update_stable (f : EnvState Auxiliary → EnvState Auxiliary) (law : ∀ env, erase (f env) = erase (f (erase env))) :
    Stable (StateT.lift (modify f) : Nested Owners Auxiliary m Unit) := by
  rintro ⟨owners, env⟩
  simp only [pack, StateT.run, lift_apply, map_apply, modify_apply, map_pure, Prod.map_def, id_eq, projection]
  rw [law env]
private theorem run_input (work : Nested Owners Auxiliary m A) (stable : Stable work) (owners : Owners) (env : EnvState Auxiliary) :
    Prod.map id erase <$> (work.run owners).run env = Prod.map id erase <$> (work.run owners).run (erase env) := by
  have actual := congrArg (fun action => (fun result => ((result.1, result.2.1), result.2.2)) <$> action) (stable (owners, env))
  simpa only [pack, StateT.run, Functor.map_map, Prod.map_def, id_eq, projection] using actual
end Algebra

private theorem effect_stable (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) := lift_stable _
private theorem kem_stable (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Stable (RegistrationNativeIdentityFrontend.kem (n := n) (Auxiliary := Auxiliary) (source := source) query) := lift_stable _
private theorem sample_stable (work : ProbComp A) :
    Stable (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  program_stable _ (fun query => effect_stable (.inl query)) work
private theorem old_effect_stable (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (mldsaSource := source) query) := lift_stable _
private theorem old_kem_stable (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Stable (RegistrationNativeBeaconFrontend.kem (n := n) (Auxiliary := Auxiliary) (mldsaSource := source) query) := lift_stable _
private theorem old_sample_stable (work : ProbComp A) :
    Stable (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (mldsaSource := source) work) :=
  program_stable _ (fun query => old_effect_stable (.inl query)) work
private theorem old_primitive_stable (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Stable (RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.primitive
  apply program_stable
  intro query
  cases query with
  | inl other => exact old_sample_stable _
  | inr other => exact old_kem_stable _
private theorem old_agreement_stable (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Stable (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply bind_stable _ _ (update_stable _ (fun _ => rfl))
  intro _
  cases query with
  | root request => exact pure_stable _
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | dh request => exact old_primitive_stable setup owner oneTime _
private theorem lift_old_stable (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A) (law : Stable work) :
    Stable (RegistrationNativeIdentityFrontend.liftOld work) := by
  rintro ⟨owners, env⟩
  have actual := congrArg (fun action => (fun result => (result.1.1, (owners, result.2))) <$>
    simulateQ RegistrationNativeIdentityFrontend.ambientLift action) (run_input work law [] env)
  simpa only [pack, RegistrationNativeIdentityFrontend.liftOld, StateT.run, lift_apply, map_apply,
    simulateQ_map, Functor.map_map, Prod.map_def, id_eq, projection] using actual

private theorem authentication_stable (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Stable (RegistrationNativeIdentityFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_stable _ _ (effect_stable _) (fun _ => pure_stable _)
  | mldsa request | ed25519 request => exact pure_stable _
private theorem agreement_stable (setup : Setup base KemSK) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    Stable (RegistrationNativeIdentityFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  by_cases ordinary : RegistrationNativeIdentityAgreementShape.Other query
  · rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary]
    exact lift_old_stable _ (old_agreement_stable setup _ oneTime query)
  · cases query with
    | convertSecret role =>
      have same : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
      subst role
      exact bind_stable _ _ (update_stable _ (fun _ => rfl)) (fun _ => pure_stable true)
    | dh request =>
      rcases request with ⟨role, peer⟩
      have same : role = .LocalIdentity := by simpa only [RegistrationNativeIdentityAgreementShape.Other, not_not] using ordinary
      subst role
      exact bind_stable _ _ (update_stable _ (fun _ => rfl)) (fun _ => lift_stable _)
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request => exact False.elim (ordinary trivial)
private theorem record_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (query : RegistrationRecordPrimitives.Request) :
    Stable (RegistrationNativeIdentityFrontend.record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire query) := by
  apply lift_old_stable
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_stable _ _ (update_stable _ (fun _ => rfl))
  intro _
  cases query with
  | adHash request =>
    change Stable (do
      let digest ← RegistrationNativeBeaconFrontend.hash request
      pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)))
    exact bind_stable _ _ (old_effect_stable _) (fun _ => pure_stable _)
  | hash transcript =>
    change Stable (do
      let digest ← RegistrationNativeBeaconFrontend.hash (.Single (Std.Array.to_slice transcript.bytes))
      pure (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest)))
    exact bind_stable _ _ (old_effect_stable _) (fun _ => pure_stable _)
  | rootKdf request | initialKdf request | ratchetKdf request | «seal» request | write request | openAead request => exact old_sample_stable _

private theorem prepare_stable (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Stable (RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
  unfold RegistrationNativeIdentityFrontend.prepare
  cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => exact pure_stable _
  | ok pin =>
      apply bind_stable _ _ (lift_stable _)
      intro identity
      cases identity with
      | none => exact pure_stable _
      | some identity => exact bind_stable _ _ (sample_stable _) (fun _ => pure_stable _)

/-- Literal constructor preparation/birth ignores prior compact receipt payloads and retains every actual generation, failure and owner/Env effect. -/
theorem create (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    RegistrationNativeIdentityEnvReceiptView.Stable
      (RegistrationNativeIdentityFrontend.create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
  unfold RegistrationNativeIdentityFrontend.create
  apply bind_stable _ _ (prepare_stable edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_stable _
  | ok result => cases result with
    | none => exact pure_stable _
    | some prepared =>
      exact bind_stable _ _ (kem_stable _) (fun _ => bind_stable _ _ (effect_stable _) (fun _ =>
        bind_stable _ _ get_stable (fun _ => bind_stable _ _ (set_stable _) (fun _ => pure_stable _))))

private theorem abort_stable (owner : Owner source) (value : A) :
    Stable (abort owner *> pure value : M n KemSK Auxiliary source A) := by
  simp only [abort, seqRight_eq_bind, bind_assoc, pure_bind]
  exact bind_stable _ _ (effect_stable _) (fun _ => pure_stable _)

private theorem record_after_stable (index : Nat) (owner : Owner source) (reply : RustM RegistrationBeaconRecordExecutor.Result) :
    Stable (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner reply) := by
  cases reply with
  | fail error | div => exact abort_stable owner _
  | ok result => cases result with
    | Err error => exact abort_stable owner _
    | Ok established =>
        change Stable (RegistrationNativePlatformIdentityFinishRecord.install index owner established)
        rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
        apply bind_stable _ _ (effect_stable _)
        intro installed
        cases installed with
        | false => exact abort_stable owner _
        | true => exact bind_stable _ _ (modify_stable _) (fun _ => pure_stable _)

private theorem agreement_after_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (reply : RustM agreement.AgreementEffect) :
    Stable (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index owner reply) := by
  cases reply with
  | fail error | div => exact abort_stable owner _
  | ok effect => cases effect with
    | Rejected previous | ConvertPublic pending | ConvertSecret pending | GenerateEphemeral pending | Encapsulate pending
      | Decapsulate pending | Dh pending | RootKdf pending | ServerComplete completed => exact abort_stable owner _
    | BeaconComplete completed =>
        exact bind_stable _ _ (program_stable _ (record_stable setup wire) _) (record_after_stable index owner)

private theorem authentication_after_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) :
    Stable (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact abort_stable owner _
  | ok result => cases result with
    | Err previous => exact abort_stable owner _
    | Ok accepted =>
        exact bind_stable _ _ (program_stable _ (agreement_stable setup owner oneTime) _)
          (agreement_after_stable setup wire index owner)

private theorem finish_begin_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (packet : Option registration.ResponsePacket) :
    Stable (RegistrationNativePlatformIdentityFinishSteps.begin (n := n) (Auxiliary := Auxiliary) setup wire index owner pending oneTime packet) := by
  cases moved : pending.aborted_state with
  | fail error | div =>
      simpa only [RegistrationNativePlatformIdentityFinishSteps.begin, moved] using
        (pure_stable (Owners := RegistrationNativeIdentityFrontend.State source) (Auxiliary := Auxiliary) (m := OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)) _)
  | ok aborted =>
      simp only [RegistrationNativePlatformIdentityFinishSteps.begin, moved]
      exact bind_stable _ _ (modify_stable _) (fun _ => bind_stable _ _
        (program_stable _ (authentication_stable setup) _) (authentication_after_stable setup wire index owner oneTime))

private theorem finish_start_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owner : Owner source) (packet : Option registration.ResponsePacket) :
    Stable (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index owner packet) := by
  cases phase : owner.phase with
  | initSent pending scalar =>
    simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using finish_begin_stable setup wire index owner pending scalar packet
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformIdentityFinishRun.start, phase]
    exact pure_stable _

/-- Every corrected actual finish branch preserves complete owner/auxiliary/request/record state after clearing only compact receipt payloads. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    RegistrationNativeIdentityEnvReceiptView.Stable
      (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  unfold RegistrationNativePlatformIdentityFinishRun.finish
  apply bind_stable _ _ get_stable
  intro owners
  cases owners[index]? with
  | none => exact pure_stable _
  | some owner => exact finish_start_stable setup wire index owner packet

private theorem platform_pack_pure (value : A) :
    RegistrationNativePlatformIdentityHistoryView.pack
      (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source A) = pure value := by
  funext before
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, StateT.run, pure_apply, map_pure]
private theorem platform_pack_bind (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source A)
    (next : A → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source B) :
    RegistrationNativePlatformIdentityHistoryView.pack (work >>= next) =
      (RegistrationNativePlatformIdentityHistoryView.pack work >>= fun value => RegistrationNativePlatformIdentityHistoryView.pack (next value)) := by
  funext before
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, StateT.run, bind_apply, map_bind, bind_map_left]

open RegistrationNativeIdentityEnvReceiptView (PlatformStable platformView platform_native platform_external)
private theorem platform_pure (value : A) :
    PlatformStable (pure value : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source A) := by
  change RegistrationNativePlatformViewStable.Stable platformView _
  rw [platform_pack_pure]
  exact RegistrationNativePlatformViewStable.pure_stable platformView (fun _ => rfl) value
private theorem platform_bind (work : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source A)
    (next : A → RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source B)
    (first : PlatformStable work) (later : ∀ value, PlatformStable (next value)) : PlatformStable (work >>= next) := by
  change RegistrationNativePlatformViewStable.Stable platformView _
  rw [platform_pack_bind]
  exact RegistrationNativePlatformViewStable.bind_stable platformView _ _ first later
private theorem platform_get : PlatformStable (get : RegistrationNativePlatformIdentityProgram.M n KemSK Auxiliary Platform source (RegistrationNativeIdentityFrontend.State source)) := by
  rintro ⟨⟨owners, env⟩, previous⟩
  simp only [RegistrationNativePlatformIdentityHistoryView.pack, StateT.run, get_apply, pure_apply, map_pure,
    platformView, RegistrationNativeIdentityEnvReceiptView.view, Prod.map_def, id_eq]
private theorem platform_next (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RegistrationNativePlatformIdentityBundle.Reply) :
    PlatformStable (RegistrationNativePlatformIdentityBundle.next (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (Platform := Platform) index owner oneTime reply) := by
  cases reply with
  | fail error | div => exact platform_pure _
  | ok reply => cases reply with
    | Err previous => exact platform_pure _
    | Ok published =>
      unfold RegistrationNativePlatformIdentityBundle.next
      exact platform_bind _ _ (platform_native _ (modify_stable _)) (fun _ =>
        platform_bind _ _ (platform_native _ (effect_stable _)) (fun _ => platform_pure _))
private theorem platform_bundled (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformStable (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := Auxiliary) setup index owner oneTime writer) := by
  unfold RegistrationNativePlatformIdentityBundle.bundled
  exact platform_bind _ _ (RegistrationNativeIdentityEnvReceiptView.platform_program setup index owner writer _)
    (platform_next index owner oneTime)
private theorem platform_start (setup : Setup base KemSK) (index : Nat) (owner : Owner source)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformStable (RegistrationNativePlatformIdentityBundleRun.start (n := n) (Auxiliary := Auxiliary) setup index owner writer) := by
  cases phase : owner.phase with
  | fresh =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact platform_bind _ _ (platform_native _ (sample_stable _)) (fun scalar => platform_bundled setup index owner scalar writer)
  | freshWithCoins scalar =>
    simpa only [RegistrationNativePlatformIdentityBundleRun.start, phase, pure_bind] using platform_bundled setup index owner scalar writer
  | initSent pending scalar | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformIdentityBundleRun.start, phase]
    exact platform_pure _

/-- The complete actual shared-P bundle, including lookup, scalar sampling, failed source writers and terminal owner updates, ignores only compact raw receipt payloads. -/
theorem bundle (setup : Setup base KemSK) (index : Nat)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    PlatformStable (RegistrationNativePlatformIdentityBundleRun.bundle (n := n) (Auxiliary := Auxiliary) (source := source) setup index writer) := by
  unfold RegistrationNativePlatformIdentityBundleRun.bundle
  apply platform_bind _ _ platform_get
  intro owners
  cases owners[index]? with
  | none => exact platform_pure _
  | some owner => exact platform_start setup index owner writer
end BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityEnvReceiptLifecycle.bundle
