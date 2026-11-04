-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformInitWriterFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundle
import BeaconcryptCore.Computational.RegistrationNativeMldsaBundleOwnership

/-! Actual free corrected Platform Init bundle preserves complete owner metadata for arbitrary raw named ML replies and counts. The literal effectful source writer, every crypto failure and terminal phase update are retained. The resulting opaque Live-owner frame requires no closed dummy signer law or private-key injectivity. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Phase M)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeOwnerFields (metadata)
open RegistrationNativePlatformBeaconPublication
variable {n : Nat} {E Platform ι KemSK Value Next Encoded : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
private abbrev PWork (V : Type) := StateT (Local n KemSK source) (RegistrationNativePlatformMldsaProgram.M source Platform) V
private def SourceKeeps (work : M n KemSK source RegistrationServerRoleBackend.State Value) : Prop :=
  ∀ owners env result, result ∈ support ((work.run owners).run env) →
    result.1.2.map metadata = owners.map metadata
private theorem source_lift (work : StateT (EnvState RegistrationServerRoleBackend.State)
    (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value) :
    SourceKeeps (StateT.lift work : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem source_get : SourceKeeps
    (get : M n KemSK source RegistrationServerRoleBackend.State (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem source_bind (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next)
    (first : SourceKeeps work) (rest : ∀ value, SourceKeeps (next value)) : SourceKeeps (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle queried)
private theorem source_pure (value : Value) :
    SourceKeeps (pure value : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem source_simulate {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (M n KemSK source RegistrationServerRoleBackend.State))
    (law : ∀ query, SourceKeeps (implementation query)) (work : OracleComp queries Value) : SourceKeeps (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact source_pure value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact source_bind _ _ (law query) ih
private theorem source_sample (draw : ProbComp Value) :
    SourceKeeps (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  unfold RegistrationNativeBeaconFrontend.sample
  exact source_simulate (fun (query : unifSpec.Domain) => RegistrationNativeBeaconFrontend.effect (.inl query))
    (fun _ => source_lift _) draw
private theorem source_phase (index : Nat) (phase : Phase) :
    SourceKeeps (RegistrationNativeBeaconFrontend.updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) index phase) := by
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


private def Keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → result.1.2.1.map metadata = before.1.map metadata
private theorem pure_keeps (value : Value) : Keeps (pure value : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) Value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_keeps (work : PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) Value)
    (next : Value → PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform) Next)
    (first : Keeps work) (rest : ∀ value, Keeps (next value)) : Keeps (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)
private theorem simulate_support {I J A : Type} {spec : OracleSpec I} {target : OracleSpec J}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec A) (value : A)
    (supported : value ∈ support (simulateQ impl work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure input => simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported ⊢; exact supported
  | query_bind query next ih =>
    rw [simulateQ_query_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, _called, continued⟩ := supported
    rw [mem_support_bind_iff]
    exact ⟨reply, mem_support_query query reply, ih reply continued⟩

private theorem lift_support (work : StateT (Local n KemSK source) (StateT Platform ProbComp) Value)
    (before : Local n KemSK source) (previous : Platform) (result : (Value × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformMldsaProgram.lift (source := source) work).run before).run previous)) :
    result ∈ support ((work.run before).run previous) := by
  change result ∈ support (simulateQ (RegistrationNativeMldsaProgram.ordinary (source := source)) ((work.run before).run previous)) at supported
  exact simulate_support (RegistrationNativeMldsaProgram.ordinary (source := source)) _ result supported

private theorem native_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (law : SourceKeeps work) :
    Keeps (RegistrationNativePlatformMldsaProgram.lift (source := source)
      (RegistrationNativePlatformBundleLower.native (m := StateT Platform ProbComp) RegistrationNativePlatformMldsaProgram.coins setup checks representation created work)) := by
  intro before previous result supported
  have closed := lift_support _ before previous result supported
  have actual : result.1 ∈ support ((lower setup checks representation created work).run before) :=
    RegistrationNativePlatformHashReceipt.native_support RegistrationNativePlatformMldsaProgram.coins _ _ previous result.2 closed
  simp only [lower, StateT.run, support_map] at actual
  obtain ⟨inner, possible, same⟩ := actual
  have ownersEq : inner.1.1.2 = result.1.2.1 := congrArg (fun value => value.2.1) same
  rw [← ownersEq]
  apply law before.1 before.2.1 inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before.2.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem outgoing_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps (RegistrationNativePlatformMldsaBundle.outgoing (n := n) (Platform := Platform) setup checks representation created index owner query) := by
  intro before previous result supported
  change result ∈ support (((StateT.lift ((RegistrationNativeMldsaBundle.outgoing setup checks representation created index owner query).run before) :
    StateT Platform (OracleComp (RegistrationNativeMldsaProgram.Spec source))
      (RegistrationBeaconInitExecutor.Spec.Range query × Local n KemSK source)).run previous)) at supported
  rw [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨raw, called, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaBundleOwnership.outgoing setup checks representation created index owner query before raw called

private theorem encoder_keeps
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedInitView) :
    Keeps (RegistrationNativePlatformMldsaProgram.lift (source := source)
      (RegistrationNativePlatformInitWriterFrame.encoder (n := n) (KemSK := KemSK) (source := source) writer view)) := by
  intro before previous result supported
  have actual := lift_support _ before previous result supported
  rw [RegistrationNativePlatformInitWriterFrame.encoder_frame] at actual
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at actual
  obtain ⟨raw, _called, same⟩ := actual
  cases same
  rfl

local notation "PWork" => PWork (n := n) (KemSK := KemSK) (source := source) (Platform := Platform)
private theorem continue_keeps {Input : Type} (action : RustM Input)
    (next : Input → PWork (RustM (RegistrationBeaconInitExecutor.Result Encoded)))
    (law : ∀ value, Keeps (next value)) : Keeps (continueWith action next) := by
  cases action with
  | fail error | div => exact pure_keeps _
  | ok value => exact law value
private theorem ready_keeps (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
    (law : ∀ view, Keeps (encode view)) (pending : registration.BeaconInitReady) : Keeps (ready encode pending) := by
  unfold ready
  exact continue_keeps _ _ fun view => bind_keeps _ _ (law view) fun _ => pure_keeps _
private theorem signing_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork))
    (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
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
private theorem hash_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork))
    (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
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
private theorem fingerprint_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork))
    (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
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
private theorem ed_keeps (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork))
    (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
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
private theorem publication (impl : QueryImpl RegistrationBeaconInitExecutor.Spec (PWork))
    (encode : registration.SignedInitView → PWork (RustM (core.option.Option Encoded)))
    (queries : ∀ query, Keeps (impl query)) (encoding : ∀ view, Keeps (encode view))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Keeps (begin impl encode control inputs coins pin mldsa) := by
  unfold begin
  apply continue_keeps _ _
  intro effect
  cases effect <;> first | exact pure_keeps _ | exact ed_keeps impl encode queries encoding _



attribute [local irreducible] RegistrationNativePlatformBundleLower.native
  RegistrationNativePlatformMldsaProgram.lift RegistrationNativePlatformGenericBundle.encoderWith

/-- The actual free bundle retains owner metadata for every raw ML reply/count and every source writer branch. -/
theorem bundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before : Local n KemSK source) (previous : Platform)
    (result : (RustM (Option (alloc.vec.Vec U8)) × Local n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformMldsaBundle.bundle setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index).run before).run previous)) :
    result.1.2.1.map metadata = before.1.map metadata := by
  have law : Keeps (RegistrationNativePlatformMldsaBundle.bundle (n := n) (Platform := Platform) setup checks representation created
      (RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := RegistrationServerRoleBackend.State)
        (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) writer)) index) := by
    unfold RegistrationNativePlatformMldsaBundle.bundle
    apply bind_keeps _ _ (native_keeps setup checks representation created _ source_get)
    intro current
    cases current[index]? with
    | none => exact pure_keeps _
    | some owner =>
      dsimp only
      cases owner.phase with
      | fresh | freshWithCoins _ =>
        apply bind_keeps _ _ ?_
        · intro oneTime
          apply bind_keeps _ _ (publication _ _ (outgoing_keeps setup checks representation created index owner)
            (encoder_keeps writer) _ _ _ _ _)
          intro published
          cases published with
          | fail error | div => exact pure_keeps _
          | ok answer => cases answer with
            | Err previous => exact pure_keeps _
            | Ok completed =>
              apply bind_keeps _ _ (native_keeps setup checks representation created _ (source_phase index _))
              intro ignored
              exact bind_keeps _ _ (native_keeps setup checks representation created _ (source_lift _)) (fun _ => pure_keeps _)
        · first | exact pure_keeps _ | exact native_keeps setup checks representation created _ (source_sample _)
      | _ => exact pure_keeps _
  exact law before previous result supported

/-- Full corrected free sourceBundle restores that exact metadata to the native envelope on all branches. -/
theorem sourceBundle (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run before).run previous)) :
    after.beacons.map metadata = before.beacons.map metadata := by
  simp only [RegistrationNativePlatformMldsaBundle.sourceBundle, StateT.run, map_apply, support_map] at supported
  obtain ⟨⟨⟨raw, localAfter⟩, platform⟩, called, same⟩ := supported
  have ownersEq : localAfter.1 = after.beacons := congrArg (fun result => result.1.2.beacons) same
  rw [← ownersEq]
  exact bundle setup checks representation created writer index
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) previous ((raw, localAfter), platform) called

/-- Live opaque owner handles survive the actual free source bundle independently of arbitrary named signing reply/count values. -/
theorem sourceBundle_live (actual : RegistrationNativeMldsa.Source) (pool : RegistrationNativeMldsaOpaque.Pool actual)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before after : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource actual)) (previous next : Platform)
    (reply : RustM (Option Pqxdh.Bytes)) (live : RegistrationNativeMldsaPoolMap.StateLive actual pool before)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformMldsaBundle.sourceBundle setup checks representation created writer index).run before).run previous)) :
    RegistrationNativeMldsaPoolMap.StateLive actual pool after :=
  RegistrationNativeMldsaLiveOwners.metadata_live actual pool before.beacons after.beacons
    (sourceBundle setup checks representation created writer index before after previous next reply supported) live

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.sourceBundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.sourceBundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.sourceBundle_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaBundleOwnership.sourceBundle_live
