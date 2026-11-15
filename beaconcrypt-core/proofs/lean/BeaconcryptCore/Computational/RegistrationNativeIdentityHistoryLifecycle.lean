-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityFinishRun
import BeaconcryptCore.Computational.RegistrationNativePlatformViewStable

/-! Incoming assigned-ID completion uses no earlier Ed signature bytes from its captured opaque owner. The source-generated identity, pin, private independent prekey/KEM material and every current phase remain unchanged by the history view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle
open PqxdhServerAuthExperiment (Setup)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {n : Nat} {I KemSK Auxiliary Value Next : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
open RegistrationNativeIdentityFrontend (M Owner)
open RegistrationNativeIdentityHistoryView (Stable owners pack project)

private theorem history_idempotent (placeholder : Ed25519Signature) (before : PqxdhJointIdentity.History) :
    RegistrationNativeIdentityHistoryView.history placeholder (RegistrationNativeIdentityHistoryView.history placeholder before) =
      RegistrationNativeIdentityHistoryView.history placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih => cases head <;>
      simp only [RegistrationNativeIdentityHistoryView.history, List.map_cons] at ih ⊢ <;> rw [ih]

/-- Applying the private signature-history projection twice changes no additional source field. -/
theorem owners_idempotent (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityFrontend.State source) :
    owners placeholder (owners placeholder before) = owners placeholder before := by
  induction before with
  | nil => rfl
  | cons head rest ih =>
    simp only [owners, List.map_cons] at ih ⊢
    rw [ih]
    exact congrArg (fun selected => selected :: rest.map (RegistrationNativeIdentityHistoryView.owner placeholder))
      (show RegistrationNativeIdentityHistoryView.owner placeholder (RegistrationNativeIdentityHistoryView.owner placeholder head) =
        RegistrationNativeIdentityHistoryView.owner placeholder head by
          simp only [RegistrationNativeIdentityHistoryView.owner, history_idempotent])

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl
private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl
private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) : (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

private theorem pack_bind (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next) :
    pack (work >>= next) = (pack work >>= fun value => pack (next value)) := by
  funext before
  simp only [pack, StateT.run, state_bind_apply, map_bind, bind_map_left]

private theorem pure_stable (placeholder : Ed25519Signature) (value : Value) :
    Stable placeholder (pure value : M n KemSK Auxiliary source Value) := by
  intro before
  simp only [pack, StateT.run, state_pure_apply, map_pure, Prod.map_def, id_eq, project, owners_idempotent]

private theorem lift_stable (placeholder : Ed25519Signature)
    (work : StateT (RegistrationWorldAgreementCompiler.EnvState Auxiliary)
      (OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK)) Value) :
    Stable placeholder (StateT.lift work : M n KemSK Auxiliary source Value) := by
  intro before
  simp only [pack, StateT.run, state_lift_apply, state_map_apply, Functor.map_map,
    Prod.map_def, id_eq, project, owners_idempotent]

private theorem bind_stable (placeholder : Ed25519Signature)
    (work : M n KemSK Auxiliary source Value) (next : Value → M n KemSK Auxiliary source Next)
    (initial : Stable placeholder work) (following : ∀ value, Stable placeholder (next value)) :
    Stable placeholder (work >>= next) := by
  change RegistrationNativePlatformViewStable.Stable (project placeholder) (pack (work >>= next))
  rw [pack_bind]
  exact RegistrationNativePlatformViewStable.bind_stable _ _ _ initial following

private theorem program_stable {Q : Type} {spec : OracleSpec Q} (placeholder : Ed25519Signature)
    (callbacks : QueryImpl spec (M n KemSK Auxiliary source))
    (leaves : ∀ query, Stable placeholder (callbacks query)) (work : OracleComp spec Value) :
    Stable placeholder (simulateQ callbacks work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_stable placeholder _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_stable placeholder _ _ (leaves query) ih

/-- Actual phase updates retain the same private history projection on every owner. -/
theorem phase_stable (placeholder : Ed25519Signature) (index : Nat) (phase : RegistrationNativeBeaconFrontend.Phase) :
    Stable placeholder (RegistrationNativeIdentityFrontend.updatePhase (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) index phase) := by
  rintro ⟨before, env⟩
  change pure ((), (owners placeholder (RegistrationNativeIdentityHistoryView.update index (fun selected => {selected with phase}) before), env)) =
    (pure ((), (owners placeholder (RegistrationNativeIdentityHistoryView.update index (fun selected => {selected with phase})
      (owners placeholder before)), env)) : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) _)
  rw [RegistrationNativeIdentityHistoryView.phase, RegistrationNativeIdentityHistoryView.phase, owners_idempotent]

private theorem effect_stable (placeholder : Ed25519Signature) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable placeholder (RegistrationNativeIdentityFrontend.effect (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) query) :=
  lift_stable placeholder _

/-- Original source sampling has no input dependency on owner signature histories. -/
theorem sample_stable (placeholder : Ed25519Signature) (work : ProbComp Value) :
    Stable placeholder (RegistrationNativeIdentityFrontend.sample (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) work) :=
  program_stable placeholder (fun (query : unifSpec.Domain) => RegistrationNativeIdentityFrontend.effect (.inl query))
    (fun _ => effect_stable placeholder _) work

private theorem kem_stable (placeholder : Ed25519Signature)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Stable placeholder (RegistrationNativeIdentityFrontend.kem (n := n) (Auxiliary := Auxiliary) (source := source) query) :=
  lift_stable placeholder _

private theorem prepare_stable (placeholder : Ed25519Signature)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Stable placeholder (RegistrationNativeIdentityFrontend.prepare (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) source edPin mlPin keyId) := by
  unfold RegistrationNativeIdentityFrontend.prepare
  cases begun : registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
  | fail error | div => exact pure_stable placeholder _
  | ok pin =>
    apply bind_stable placeholder _ _ (lift_stable placeholder _)
    intro identity
    cases identity with
    | none => exact pure_stable placeholder _
    | some identity => exact bind_stable placeholder _ _ (sample_stable placeholder _) (fun _ => pure_stable placeholder _)

private theorem append_stable (placeholder : Ed25519Signature) (born : Owner source)
    (fixed : RegistrationNativeIdentityHistoryView.owner placeholder born = born) :
    Stable placeholder (do
      let current ← get
      set (current ++ [born])
      pure (.ok (some current.length)) : M n KemSK Auxiliary source (RustM (Option Nat))) := by
  rintro ⟨before, env⟩
  have append : ∀ current, owners placeholder (current ++ [born]) = owners placeholder current ++ [born] := by
    intro current
    simp only [owners, List.map_append, List.map_cons, List.map_nil, fixed]
  have size : (owners placeholder before).length = before.length := by simp only [owners, List.length_map]
  change pure ((.ok (some before.length) : RustM (Option Nat)), (owners placeholder (before ++ [born]), env)) =
    (pure ((.ok (some (owners placeholder before).length) : RustM (Option Nat)),
      (owners placeholder (owners placeholder before ++ [born]), env)) : OracleComp (RegistrationNativeIdentityFrontend.Trusted n KemSK) _)
  rw [append, append, owners_idempotent, size]

private theorem old_stable (placeholder : Ed25519Signature)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) :
    Stable placeholder (RegistrationNativeIdentityFrontend.liftOld work) := lift_stable placeholder _

private theorem abort_stable (placeholder : Ed25519Signature) (before : Owner source) :
    Stable placeholder (RegistrationNativeIdentityFrontend.abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) before) :=
  bind_stable placeholder _ _ (effect_stable placeholder _) (fun _ => pure_stable placeholder ())

private theorem primitive_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (before : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Stable placeholder (RegistrationNativeIdentityFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup before oneTime query) := by
  cases query with
  | convertSecret role => cases role <;> exact pure_stable placeholder _
  | dh request =>
      cases role : request.secret_role <;> simp only [RegistrationNativeIdentityFrontend.primitive, role]
      all_goals exact lift_stable placeholder _
  | convertPublic key | generate role | encapsulate key | decapsulate ciphertext => exact old_stable placeholder _

private theorem agreement_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (before : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Stable placeholder (RegistrationNativeIdentityFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup before oneTime query) := by
  apply bind_stable placeholder _ _ (lift_stable placeholder _)
  intro _
  cases query <;> simp only [RegistrationNativeIdentityFrontend.agreementCore]
  all_goals first | exact pure_stable placeholder _ | exact primitive_stable placeholder setup before oneTime _

private theorem authentication_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK)
    (query : RegistrationAuthenticationExecutor.Request) :
    Stable placeholder (RegistrationNativeIdentityFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_stable placeholder _ _ (effect_stable placeholder _) (fun _ => pure_stable placeholder _)
  | mldsa request | ed25519 request => exact pure_stable placeholder _

private theorem record_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    Stable placeholder (RegistrationNativeIdentityFrontend.record (n := n) (Auxiliary := Auxiliary) (source := source) setup wire query) :=
  old_stable placeholder _

private theorem install_stable (placeholder : Ed25519Signature) (index : Nat) (before : Owner source)
    (completed : registration.CompletedBeacon) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishRecord.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index before completed) := by
  rw [RegistrationNativePlatformIdentityFinishRecord.install_exact]
  apply bind_stable placeholder _ _ (effect_stable placeholder _)
  intro installed
  cases installed with
  | false => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
  | true => exact bind_stable placeholder _ _ (phase_stable placeholder _ _) (fun _ => pure_stable placeholder _)

private theorem afterRecord_stable (placeholder : Ed25519Signature) (index : Nat) (before : Owner source)
    (result : RustM RegistrationBeaconRecordExecutor.Result) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishRecord.after (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index before result) := by
  cases result with
  | fail error | div => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
  | ok result => cases result with
    | Err error => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
    | Ok completed => exact install_stable placeholder index before completed

private theorem afterAgreement_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Owner source) (result : RustM agreement.AgreementEffect) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishSteps.afterAgreement (n := n) (Auxiliary := Auxiliary) setup wire index before result) := by
  cases result with
  | fail error | div => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
  | ok effect => cases effect <;> first
    | exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
    | exact bind_stable placeholder _ _ (program_stable placeholder _ (record_stable placeholder setup wire) _)
        (afterRecord_stable placeholder index before)

private theorem afterAuthentication_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (before : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (result : RustM RegistrationResponseExecutor.ResponseResult) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishSteps.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index before oneTime result) := by
  cases result with
  | fail error | div => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
  | ok result => cases result with
    | Err error => exact bind_stable placeholder _ _ (abort_stable placeholder before) (fun _ => pure_stable placeholder _)
    | Ok accepted =>
      exact bind_stable placeholder _ _
        (program_stable placeholder _ (agreement_stable placeholder setup before oneTime) _)
        (afterAgreement_stable placeholder setup wire index before)

/-- Actual Init input selection cannot read raw prior Ed signatures. -/
theorem inputs (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityFrontend.Owner source) :
    RegistrationNativeIdentityFrontend.inputs (RegistrationNativeIdentityHistoryView.owner placeholder before) =
      RegistrationNativeIdentityFrontend.inputs before := rfl

/-- The corrected complete incoming continuation uses the same captured owner fields under the history view. -/
theorem finish_start (placeholder : Ed25519Signature) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (before : RegistrationNativeIdentityFrontend.Owner source) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index
      (RegistrationNativeIdentityHistoryView.owner placeholder before) packet =
      RegistrationNativePlatformIdentityFinishRun.start setup wire index before packet := rfl

/-- The corrected entire captured response continuation ignores earlier raw Ed signatures in its working owner roster. -/
theorem start_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (before : Owner source) (packet : Option registration.ResponsePacket) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishRun.start (n := n) (Auxiliary := Auxiliary) setup wire index before packet) := by
  cases phase : before.phase with
  | fresh | freshWithCoins scalar | established completed | aborted aborted =>
      simpa only [RegistrationNativePlatformIdentityFinishRun.start, phase] using
        (pure_stable (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) (source := source) placeholder (.ok none : RustM (Option Pqxdh.Bytes)))
  | initSent pending oneTime =>
    simp only [RegistrationNativePlatformIdentityFinishRun.start, phase, RegistrationNativePlatformIdentityFinishSteps.begin]
    cases aborted : pending.aborted_state with
    | fail error | div => exact pure_stable placeholder _
    | ok aborted =>
      apply bind_stable placeholder _ _ (phase_stable placeholder _ _)
      intro _
      exact bind_stable placeholder _ _
        (program_stable placeholder _ (authentication_stable placeholder setup) _)
        (afterAuthentication_stable placeholder setup wire index before oneTime)

/-- Actual owner lookup and the full corrected finish preserve the same complete private history view. -/
theorem finish_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    Stable placeholder (RegistrationNativePlatformIdentityFinishRun.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  rintro ⟨before, env⟩
  cases found : before[index]? with
  | none =>
    have viewed : (owners placeholder before)[index]? = none := by
      simp only [owners, List.getElem?_map, found, Option.map_none]
    simp only [pack, RegistrationNativePlatformIdentityFinishRun.finish, StateT.run, state_bind_apply,
      state_get_apply, state_pure_apply, pure_bind, found, project, viewed,
      map_pure, Prod.map_def, id_eq, owners_idempotent]
  | some selected =>
    have viewed : (owners placeholder before)[index]? = some (RegistrationNativeIdentityHistoryView.owner placeholder selected) := by
      simp only [owners, List.getElem?_map, found, Option.map_some]
    have actual := start_stable (n := n) (Auxiliary := Auxiliary) placeholder setup wire index selected packet (before, env)
    simpa only [pack, RegistrationNativePlatformIdentityFinishRun.finish, StateT.run, state_bind_apply,
      state_get_apply, state_pure_apply, pure_bind, found, project, viewed, finish_start] using actual

/-- Actual adaptive creation appends its fresh empty-history owner without consulting any existing raw Ed signature. -/
theorem create_stable (placeholder : Ed25519Signature) (setup : Setup base KemSK)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Stable placeholder (RegistrationNativeIdentityFrontend.create (n := n) (Auxiliary := Auxiliary) setup source edPin mlPin keyId) := by
  unfold RegistrationNativeIdentityFrontend.create
  apply bind_stable placeholder _ _ (prepare_stable placeholder edPin mlPin keyId)
  intro prepared
  cases prepared with
  | fail error | div => exact pure_stable placeholder _
  | ok prepared => cases prepared with
    | none => exact pure_stable placeholder _
    | some prepared =>
      apply bind_stable placeholder _ _ (kem_stable placeholder _)
      intro born
      apply bind_stable placeholder _ _ (effect_stable placeholder _)
      intro worldOwner
      exact append_stable placeholder _ rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.inputs
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.finish_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.finish_start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.start_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.start_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.finish_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.finish_stable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.create_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.create_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.owners_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.owners_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.phase_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.phase_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.sample_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHistoryLifecycle.sample_stable
