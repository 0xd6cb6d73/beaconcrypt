-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerStartup
import BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-! Root preparation returns only an executable message reference and the actual cleared native token. Selected root32 bytes remain in the private service interpretation. This reference is stored by the one-use session frontend and consumed only after native completion admission. The naturality theorem below derives the exact original related-root result when the private interpreter supplies the earlier root reply; no game equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceRoot
open RegistrationNativeRelatedFamily (Message)
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhSecretInputKdf (RootOutput)
open PqxdhServerRootPreparation (Inputs)
open PqxdhJointIdentity (PeerEncoding)

abbrev PrepareSpec := Message →ₒ Option Message

/-- No root32, initializer chain or consumed kernel appears in this public session capability. -/
structure Ready where
  agreement : RegistrationBoundGate.PublicAgreement
  reference : Message

def atRoot (ready : Ready) (root : RootOutput) : agreement.ServerAgreement :=
  RegistrationBoundGate.atRoot ready.agreement root

/-- Native erasure callbacks are quiet in this phase; owned replay insertion remains outside, at the actual frontend retain operation. -/
noncomputable def client {Reader E : Type} (binding : session.RegistrationBinding)
    (input : Inputs Reader E PeerEncoding) : OracleComp PrepareSpec (RustM (Option Ready)) := by
  classical
  exact if ¬ PqxdhServerRelatedRootInput.localNonzero input then pure (.ok none) else do
    let reference ← PrepareSpec.query (Message.ofLegacy (PqxdhServerRelatedRootInput.message input))
    pure (.ok (reference.map fun reference =>
      ⟨⟨PqxdhServerClearedRoot.pending binding.server_pin.binding input, binding⟩, reference⟩))

/-- The root reply is private interpreter state, never an argument to client. -/
def annotate : QueryImpl PrepareSpec (StateT (Option RootOutput) (OracleComp RootSpec)) :=
  fun message _ => match message.toLegacy? with
  | none => pure (none, none)
  | some legacy => do
      let root ← (RootSpec.query (.inr (.derive legacy)) : OracleComp RootSpec _)
      pure (root.map (fun _ => message), root)


/-- The complete native phase interpreter accepts every descriptor, including arbitrary-pin selected Beacon and ordinary supplied inputs. -/
def annotateNative : QueryImpl PrepareSpec
    (StateT (Option RootOutput) (OracleComp RegistrationNativeRelatedRoot.RootSpec)) :=
  fun message _ => do
    let root ← (RegistrationNativeRelatedRoot.RootSpec.query (.inr (.derive message)) :
      OracleComp RegistrationNativeRelatedRoot.RootSpec _)
    pure (root.map (fun _ => message), root)

def quietRoot : QueryImpl PqxdhServerRelatedRootConsumer.Spec (OracleComp RootSpec)
  | .inl query => RootSpec.query query
  | .inr _ => pure ()

def restored (root : Option RootOutput) : RustM (Option Ready) → RustM agreement.AgreementEffect
  | .fail error => .fail error
  | .div => .div
  | .ok none => .ok (.Rejected .None)
  | .ok (some ready) => .ok (.ServerComplete (atRoot ready (root.getD RegistrationBoundKeySchedule.zero)))

private theorem map_state_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

/-- Source reconstruction retains every private root reply and the actual populated native binding/token. The executable client sees only its message reference. -/
theorem client_source (binding : session.RegistrationBinding)
    (input : Inputs registration.InitPacket Unit PeerEncoding) :
    (fun result => restored result.2 result.1) <$>
      (simulateQ annotate (client binding input)).run none =
      simulateQ quietRoot (RegistrationRelatedRoot.client binding input) := by
  classical
  simp only [client, RegistrationRelatedRoot.client, PqxdhServerRelatedRootConsumer.client,
    simulateQ_map, simulateQ_bind, simulateQ_spec_query, quietRoot, pure_bind]
  by_cases admitted : PqxdhServerRelatedRootInput.localNonzero input
  · simp only [admitted, not_true_eq_false, ite_false, simulateQ_bind, simulateQ_spec_query,
      simulateQ_map, quietRoot, annotate, Message.toLegacy_ofLegacy, StateT.run, restored,
      bind_pure_comp, map_state_apply, Functor.map_map, pure_bind, map_bind]
    rw [map_eq_bind_pure_comp]
    apply congrArg (fun continuation =>
      (RootSpec.query (.inr (.derive (PqxdhServerRelatedRootInput.message input))) : OracleComp RootSpec _) >>= continuation)
    funext root
    cases root <;> simp only [simulateQ_pure, simulateQ_map, simulateQ_spec_query, quietRoot,
      RegistrationRelatedRoot.completed, map_pure, atRoot, RegistrationBoundGate.atRoot,
      Function.comp_def, Prod.map, id_eq, Option.map_some, Option.map_none, Option.getD_some]
  · simp only [admitted, not_false_eq_true, ite_true, simulateQ_pure, StateT.run_pure, map_pure,
      restored, RegistrationRelatedRoot.completed]

/-- The reference capability has the literal source replay identifier and already-cleared root-input storage. -/
theorem ready_fields {Reader E : Type} (binding : session.RegistrationBinding)
    (input : Inputs Reader E PeerEncoding) (ready : Ready)
    (supported : .ok (some ready) ∈ support (client binding input)) :
    ready.agreement.pending.registration_id = PqxdhServerClearedRoot.registrationIdValue input.verified ∧
      ready.agreement.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8 ∧
      ready.agreement.binding = binding := by
  classical
  simp only [client] at supported
  split at supported
  · simp only [mem_support_pure_iff, RustM.ok.injEq, Option.some_ne_none] at supported
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨reference, reached, equal⟩ := supported
    cases reference with
    | none => cases equal
    | some reference =>
        cases equal
        exact ⟨rfl, rfl, rfl⟩

/-- Each reached native root preparation asks its service at most once, including every rejection. -/
theorem client_bound {Reader E : Type} (binding : session.RegistrationBinding)
    (input : Inputs Reader E PeerEncoding) : (client binding input).IsTotalQueryBound 1 := by
  classical
  unfold client
  split
  · trivial
  · rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => by trivial⟩

abbrev Spec := RootSpec + PrepareSpec

def rootLift : QueryImpl RootSpec (OracleComp Spec) := fun query => Spec.query (.inl query)
def prepareLift : QueryImpl PrepareSpec (OracleComp Spec) := fun query => Spec.query (.inr query)

def interpretation : QueryImpl Spec (StateT (Option RootOutput) (OracleComp RootSpec))
  | .inl query => fun before => (fun value => (value, before)) <$> (RootSpec.query query : OracleComp RootSpec _)
  | .inr message => annotate message

noncomputable def collect {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (RegistrationServerRootCompiler.Shared n) (OracleComp RootSpec)
      (Option (Inputs registration.InitPacket Unit PeerEncoding)) :=
  simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationServerRootCompiler.backend setup checks))
    RegistrationServerRootCompiler.visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))

/-- The complete native public preparation retains every original source effect and returns a root-free capability to the session table. -/
noncomputable def stage {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (RegistrationServerRootCompiler.Shared n) (OracleComp Spec) (RustM (Option Ready)) := fun before => do
  let collected ← simulateQ rootLift ((collect setup checks packet authenticated).run before)
  match collected.1 with
  | none => pure (.ok none, collected.2)
  | some input => do
      let ready ← simulateQ prepareLift (client authenticated.binding input)
      pure (ready, collected.2)

private theorem root_interpret {X : Type} (work : OracleComp RootSpec X) (before : Option RootOutput) :
    (simulateQ interpretation (simulateQ rootLift work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : interpretation ∘ₛ rootLift =
      (QueryImpl.ofLift RootSpec (OracleComp RootSpec)).liftTarget (StateT (Option RootOutput) (OracleComp RootSpec)) := by
    funext query
    simp only [QueryImpl.compose, rootLift, simulateQ_spec_query, interpretation]
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

private theorem root_interpret_raw {X : Type} (work : OracleComp RootSpec X) (before : Option RootOutput) :
    (simulateQ interpretation (simulateQ rootLift work)) before =
      (fun value => (value, before)) <$> work := root_interpret work before

private theorem prepare_interpret {X : Type} (work : OracleComp PrepareSpec X) :
    simulateQ interpretation (simulateQ prepareLift work) = simulateQ annotate work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : interpretation ∘ₛ prepareLift = annotate := by
    funext query
    simp only [QueryImpl.compose, prepareLift, simulateQ_spec_query, interpretation]
  rw [same]

private theorem consumer_source {X : Type} {n : Nat}
    (work : OracleComp PqxdhServerRelatedRootConsumer.Spec X) (before : RegistrationServerRootCompiler.Shared n) :
    (simulateQ RegistrationServerRootCompiler.consumer work).run before =
      (fun value => (value, before)) <$> simulateQ quietRoot work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases query with
      | inl query =>
          simp only [RegistrationServerRootCompiler.consumer, quietRoot, StateT.run, bind_map_left,
            map_bind]
          congr 1
          funext value
          exact ih value
      | inr query =>
          simp only [RegistrationServerRootCompiler.consumer, quietRoot, StateT.run_pure, pure_bind]
          exact ih ()

private theorem consumer_source_raw {X : Type} {n : Nat}
    (work : OracleComp PqxdhServerRelatedRootConsumer.Spec X) (before : RegistrationServerRootCompiler.Shared n) :
    (simulateQ RegistrationServerRootCompiler.consumer work) before =
      (fun value => (value, before)) <$> simulateQ quietRoot work := consumer_source work before

/-- Restoring the root privately recovers the exact original open native stage, including full World/cache state and source root-call order. -/
theorem stage_source {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerRootCompiler.Shared n) :
    (fun result => (restored result.2 result.1.1, result.1.2)) <$>
      (simulateQ interpretation ((stage setup checks packet authenticated).run before)).run none =
      (RegistrationServerRootCompiler.stage setup checks setup.serverDomain packet authenticated).run before := by
  simp only [StateT.run, stage, simulateQ_bind, StateT.monad_bind_def, StateT.bind,
    root_interpret_raw, map_bind, bind_map_left]
  change (do
    let collected ← (collect setup checks packet authenticated).run before
    (fun result : (RustM (Option Ready) × RegistrationServerRootCompiler.Shared n) × Option RootOutput =>
      (restored result.2 result.1.1, result.1.2)) <$>
      (simulateQ interpretation
        (match collected.1 with
        | none => pure ((.ok none : RustM (Option Ready)), collected.2)
        | some input => do
            let ready ← simulateQ prepareLift (client authenticated.binding input)
            pure (ready, collected.2))).run none) = _
  simp only [RegistrationServerRootCompiler.stage, StateT.monad_bind_def, StateT.bind, StateT.run]
  apply congrArg (fun continuation => (collect setup checks packet authenticated).run before >>= continuation)
  funext collected
  rcases collected with ⟨input, current⟩
  cases input with
  | none => simp only [simulateQ_pure, restored]; rfl
  | some input =>
      simp only [simulateQ_map, prepare_interpret, bind_pure_comp, map_state_apply, Functor.map_map, consumer_source_raw]
      simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map, Prod.map, id_eq, StateT.run] using
        congrArg (fun work => (fun value => (value, current)) <$> work) (client_source authenticated.binding input)

end BeaconcryptCore.Computational.RegistrationServerReferenceRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRoot.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRoot.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRoot.ready_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRoot.ready_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRoot.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRoot.client_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceRoot.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceRoot.stage_source
