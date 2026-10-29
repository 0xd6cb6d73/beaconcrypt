-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerRoleBackend

/-! The Server agreement compiler is an actual open client of the related-root oracle. Its state contains only local ephemeral material, the public World, and the existing CTX cache. Selected identity bytes and the selected static-DH reply occur only in the private family interpretation. Probabilistic native callbacks forward all coins through RootSpec; the unchanged World counters still count each original draw. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerRootCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

abbrev Local (n : Nat) := RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State
abbrev Shared (n : Nat) := RawCtxSharedPrimitive.SharedState (Local n)
abbrev Family := PqxdhJointDhExtractFamily.State

def coins : QueryImpl unifSpec (OracleComp RootSpec) := fun query => RootSpec.query (.inl query)

def liftProb {A Value : Type} (work : StateT A ProbComp Value) : StateT A (OracleComp RootSpec) Value :=
  fun before => simulateQ coins (work.run before)

/-- The private root oracle state is retained while all public client state is threaded explicitly. -/
def interpret {A Value : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (work : StateT A (OracleComp RootSpec) Value) : StateT (Family × A) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ family (work.run before.2)).run before.1

theorem interpret_pure {A Value : Type} (family : QueryImpl RootSpec (StateT Family ProbComp)) (value : Value) :
    interpret (A := A) family (pure value) = pure value := by
  funext before
  simp only [interpret, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

theorem interpret_bind {A Value Result : Type} (family : QueryImpl RootSpec (StateT Family ProbComp))
    (work : StateT A (OracleComp RootSpec) Value) (next : Value → StateT A (OracleComp RootSpec) Result) :
    interpret family (work >>= next) = (interpret family work >>= fun value => interpret family (next value)) := by
  funext before
  change (interpret family (work >>= next)).run before =
    (interpret family work >>= fun value => interpret family (next value)).run before
  simp only [StateT.run_bind]
  simp only [interpret, StateT.run, StateT.monad_bind_def, StateT.bind,
    simulateQ_bind, map_bind, bind_map_left]

theorem interpret_program {A I Result : Type} {spec : OracleSpec I}
    (family : QueryImpl RootSpec (StateT Family ProbComp))
    (compiler : QueryImpl spec (StateT A (OracleComp RootSpec)))
    (native : QueryImpl spec (StateT (Family × A) ProbComp))
    (step : ∀ query, interpret family (compiler query) = native query) (work : OracleComp spec Result) :
    interpret family (simulateQ compiler work) = simulateQ native work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using interpret_pure family value
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [interpret_bind, step]
      apply congrArg (fun continuation => native query >>= continuation)
      funext value
      exact ih value

noncomputable def family (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl RootSpec (StateT Family ProbComp) :=
  PqxdhJointDhExtractFamily.realImpl hmac joint dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction

theorem liftProb_exact {A Value : Type}
    (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : StateT A ProbComp Value) :
    interpret (family hmac joint dh seed scalar) (liftProb work) = RegistrationRootStage.lift work := by
  funext before
  simp only [interpret, liftProb, StateT.run, ← QueryImpl.simulateQ_compose]
  have same : family hmac joint dh seed scalar ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT Family ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (liftM (work.run before.2) : StateT Family ProbComp _).run before.1 = RegistrationRootStage.lift work before
  rw [StateT.run_liftM, bind_pure_comp]
  simp only [RegistrationRootStage.lift, StateT.run, Functor.map_map]

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (Shared n) (OracleComp RootSpec)) :=
  fun query => liftProb (RegistrationAgreementShared.implementation setup.source
    (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks)) query)

def visit (point : Word32) : StateT (Shared n) (OracleComp RootSpec) Unit :=
  liftProb (RegistrationWorldRoot.visitShared point)

def consumer : QueryImpl PqxdhServerRelatedRootConsumer.Spec (StateT (Shared n) (OracleComp RootSpec))
  | .inl query => fun before => (fun reply => (reply, before)) <$>
      (RootSpec.query query : OracleComp RootSpec _)
  | .inr _ => pure ()

/-- This complete post-authentication client receives only the opaque root result; no selected seed is an argument or a state field. -/
noncomputable def stage (setup : Setup base KemSK) (checks : Checks)
    (domain : PqxdhServerStaticDhSource.PublicDomain setup.joint)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Shared n) (OracleComp RootSpec) (RustM agreement.AgreementEffect) := do
  let input ← simulateQ (PqxdhServerStaticDhSource.prefixImpl domain
    (RegistrationAgreementInterpreter.prepImpl (backend setup checks)) visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))
  match input with
  | none => pure (.ok (.Rejected .None))
  | some input => simulateQ consumer (RegistrationRelatedRoot.client authenticated.binding input)

private theorem backend_exact (setup : Setup base KemSK) (checks : Checks)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    interpret (family hmac setup.joint dh seed scalar) (backend (n := n) setup checks query) =
      RegistrationRootStage.lifted (RegistrationAgreementShared.implementation setup.source
        (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks))) query :=
  liftProb_exact hmac setup.joint dh seed scalar _

private theorem prep_exact (setup : Setup base KemSK) (checks : Checks)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain) :
    interpret (family hmac setup.joint dh seed scalar)
      (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks) query) =
    RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted
      (RegistrationAgreementShared.implementation setup.source
        (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks)))) query := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | exact interpret_program _ _ _ (backend_exact setup checks hmac dh seed scalar) _
    | exact interpret_pure _ _

private theorem prefix_exact (setup : Setup base KemSK) (checks : Checks)
    (domain : PqxdhServerStaticDhSource.PublicDomain setup.joint)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PeerEncoding).Domain) :
    interpret (family hmac setup.joint dh seed scalar)
      (PqxdhServerStaticDhSource.prefixImpl domain
        (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit query) =
    PqxdhServerStaticDhSource.prefixImpl domain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted
        (RegistrationAgreementShared.implementation setup.source
          (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks)))))
      (fun point => RegistrationRootStage.lift (RegistrationWorldRoot.visitShared point)) query := by
  cases query <;> simp only [PqxdhServerStaticDhSource.prefixImpl]
  all_goals try exact prep_exact setup checks hmac dh seed scalar _
  simp only [interpret_bind, visit, liftProb_exact, interpret_pure]

private theorem map_state_apply {S X Y : Type} (mapResult : X → Y) (work : StateT S ProbComp X)
    (state : S) : (mapResult <$> work) state = Prod.map mapResult id <$> work state := by
  change (work state >>= fun result => pure (mapResult result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem consumer_exact (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : PqxdhServerRelatedRootConsumer.Spec.Domain) :
    interpret (family hmac joint dh seed scalar) (consumer (n := n) query) =
      PqxdhServerRelatedRootConsumer.impl (family hmac joint dh seed scalar) RegistrationAgreementFinish.quiet query := by
  cases query with
  | inl query =>
      funext before
      simp only [interpret, consumer, StateT.run, simulateQ_map, simulateQ_spec_query,
        PqxdhServerRelatedRootConsumer.impl, PqxdhServerRelatedRootConsumer.familyImpl]
      simp only [map_state_apply, Functor.map_map, Prod.map, id_eq]
      rfl
  | inr query =>
      simp only [consumer, interpret_pure]
      rfl

/-- The entire open client, including every abort and all family/cache/World state, interprets to the existing actual related-root stage. -/
theorem stage_exact (setup : Setup base KemSK) (checks : Checks)
    (domain : PqxdhServerStaticDhSource.PublicDomain setup.joint)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    interpret (family hmac setup.joint dh seed scalar) (stage (n := n) setup checks domain packet authenticated) =
      RegistrationRelatedRoot.stage domain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationRootStage.lifted
          (RegistrationAgreementShared.implementation setup.source
            (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks)))))
        (fun point => RegistrationRootStage.lift (RegistrationWorldRoot.visitShared point))
        (family hmac setup.joint dh seed scalar) RegistrationAgreementFinish.quiet packet authenticated := by
  simp only [stage, RegistrationRelatedRoot.stage, interpret_bind]
  rw [interpret_program _ _ _ (prefix_exact setup checks domain hmac dh seed scalar)]
  congr 1
  funext input
  cases input with
  | none => exact interpret_pure _ _
  | some input => exact interpret_program _ _ _ (consumer_exact hmac setup.joint dh seed scalar) _

/-- The redundant cache is initialized from the same World and removed after the native root phase. -/
noncomputable def worldStage (setup : Setup base KemSK) (checks : Checks)
    (domain : PqxdhServerStaticDhSource.PublicDomain setup.joint)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (Local n) (OracleComp RootSpec) (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, result.2.1)) <$>
    (stage setup checks domain packet authenticated).run (before, before.world.1.primitive.2)

/-- The concrete seed-free client retains exactly the full family and World state of the real native profile. -/
theorem world_exact (setup : Setup base KemSK) (checks : Checks)
    (domain : PqxdhServerStaticDhSource.PublicDomain setup.joint)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    interpret (family hmac setup.joint dh seed scalar)
      (worldStage (n := n) setup checks domain packet authenticated) =
      RegistrationWorldRoot.stage setup.source hmac setup.joint dh domain seed scalar
        (RegistrationServerRoleBackend.localBackend setup checks) packet authenticated := by
  funext before
  have same := congrFun (stage_exact (n := n) setup checks domain hmac dh seed scalar packet authenticated)
    (before.1, (before.2, before.2.world.1.primitive.2))
  have mapped := congrArg (fun work => (fun result => (result.1, (result.2.1, result.2.2.1))) <$> work) same
  simpa only [interpret, worldStage, RegistrationWorldRoot.stage, family, StateT.run,
    simulateQ_map, map_state_apply, Functor.map_map, Prod.map, id_eq] using mapped

private theorem native_world (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : IdentitySeed) :
    RegistrationWorldAgreement.agreement (n := n) setup.source
      (RegistrationServerRoleBackend.native setup checks representation seed) =
      RegistrationAgreementInterpreter.sourceImpl setup.joint seed
        (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.localBackend setup checks))
        RegistrationWorldRoot.visit := by
  funext query before
  cases query with
  | convertSecret role =>
      cases role <;> simp only [RegistrationAgreementInterpreter.sourceImpl,
        RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
        RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
        RegistrationServerRoleBackend.selected_conversion setup representation]
  | dh request =>
      cases role : request.secret_role <;>
        simp only [RegistrationAgreementInterpreter.sourceImpl, role]
      simp only [RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
        RegistrationServerRoleBackend.native, role, PqxdhRecordLiftWorld.sampled,
        simulateQ_pure, bind_pure_comp, map_pure, RegistrationWorldAgreement.recorded,
        StateT.run, StateT.monad_pure_def, StateT.pure, simulateQ_pure, map_pure]
      cases request
      cases role
      rfl
      all_goals simp only [RegistrationWorldAgreement.agreement, RegistrationAgreementShared.auxiliary,
        RegistrationServerRoleBackend.native, role]
  | root request => rfl
  | convertPublic key => rfl
  | generate role => rfl
  | encapsulate key => rfl
  | decapsulate ciphertext => rfl

/-- Interpreting the selected root service recovers the actual concrete Server backend, including real optional public conversion, source generators, all coins, and populated native authentication metadata. The selected 32-byte conversion representation is an explicit functional SDK boundary. -/
theorem world_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (control : pqxdh.ServerState) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationWorldRoot.FullState n RegistrationServerRoleBackend.State) :
    Prod.map id Prod.snd <$>
      (interpret (family setup.hmac setup.joint setup.dh seed scalar)
        (worldStage setup checks setup.serverDomain packet authenticated)).run before =
      (simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation seed))
        (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before.2 := by
  rw [world_exact, native_world]
  exact RegistrationWorldRoot.stage_project setup.source setup.hmac correct setup.joint setup.dh
    setup.serverDomain setup.secretOfSeed setup.wiring seed scalar
    (RegistrationServerRoleBackend.localBackend setup checks) control packet authenticated before

end BeaconcryptCore.Computational.RegistrationServerRootCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_program' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.interpret_program

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.liftProb_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.liftProb_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.stage_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.stage_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.world_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.world_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationServerRootCompiler.world_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerRootCompiler.world_native
