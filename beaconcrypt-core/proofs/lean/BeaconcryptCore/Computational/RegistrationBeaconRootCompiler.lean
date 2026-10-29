-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRoleBackend
import BeaconcryptCore.Computational.RegistrationServerRootCompiler

/-! The concrete Beacon root compiler is an open related-root client. Its inputs contain the public challenge and authenticated response, while its local state owns only ordinary Beacon identity/one-time/KEM material and the existing World cache. Selected prekey and Server identity secrets occur solely in the private family interpretation. Both selected prekey DH positions retain their actual public request operands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconRootCompiler
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhJointDhExtractRoot (RootSpec)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationServerRootCompiler (liftProb interpret interpret_pure interpret_bind interpret_program family liftProb_exact)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

abbrev Local (n : Nat) (KemSK : Type) := RegistrationWorldAgreement.State n (RegistrationBeaconRoleBackend.State KemSK)
abbrev Shared (n : Nat) (KemSK : Type) := RawCtxSharedPrimitive.SharedState (Local n KemSK)

noncomputable def backend (setup : Setup base KemSK) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (Shared n KemSK) (OracleComp RootSpec)) :=
  fun query => liftProb (RegistrationAgreementShared.implementation setup.source
    (RegistrationWorldRoot.primitive setup.source
      (RegistrationPublicConversion.primitive setup.source.crypto (RegistrationBeaconRoleBackend.localBackend setup))) query)

def visit (point : Word32) : StateT (Shared n KemSK) (OracleComp RootSpec) Unit :=
  liftProb (RegistrationWorldBeaconRoot.visitShared point)

def rootLift : QueryImpl RootSpec (StateT (Shared n KemSK) (OracleComp RootSpec)) :=
  fun query before => (fun reply => (reply, before)) <$> (RootSpec.query query : OracleComp RootSpec _)

/-- The public source prefix cannot read the selected prekey scalar. Its root continuation receives only the opaque related-root reply. -/
noncomputable def stage (setup : Setup base KemSK) (domain : PqxdhPhase2GapDhSource.PublicDomain setup.dh)
    (publicValue : PublicChallenge) (authenticated : registration.AuthenticatedResponse) :
    StateT (Shared n KemSK) (OracleComp RootSpec) (RustM agreement.AgreementEffect) := do
  let pending ← simulateQ (PqxdhPhase2GapDhSource.prefixImpl domain
    (RegistrationBeaconRootInterpreter.auxImpl (backend setup) authenticated) visit)
    (PqxdhPhase2DhMetadata.prepare authenticated.pending.control () () () [])
  match pending with
  | none => pure (.ok (RegistrationBeaconAgreementRoot.rejected authenticated))
  | some pending => simulateQ rootLift (RegistrationBeaconRelatedRoot.client publicValue authenticated pending)

private theorem backend_exact (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar) (backend (n := n) setup query) =
      RegistrationRootStage.lifted (RegistrationAgreementShared.implementation setup.source
        (RegistrationWorldRoot.primitive setup.source
          (RegistrationPublicConversion.primitive setup.source.crypto (RegistrationBeaconRoleBackend.localBackend setup)))) query :=
  liftProb_exact setup.hmac setup.joint setup.dh seed scalar _

private theorem aux_exact (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (query : RegistrationBeaconRootInterpreter.AuxSpec.Domain) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar)
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup) authenticated query) =
    RegistrationBeaconRootInterpreter.auxImpl (RegistrationRootStage.lifted
      (RegistrationAgreementShared.implementation setup.source
        (RegistrationWorldRoot.primitive setup.source
          (RegistrationPublicConversion.primitive setup.source.crypto (RegistrationBeaconRoleBackend.localBackend setup)))))
      authenticated query := by
  cases query <;> simp only [RegistrationBeaconRootInterpreter.auxImpl]
  all_goals exact interpret_program _ _ _ (backend_exact setup seed scalar) _

private theorem prefix_exact (setup : Setup base KemSK) (domain : PqxdhPhase2GapDhSource.PublicDomain setup.dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar)
      (PqxdhPhase2GapDhSource.prefixImpl domain
        (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup) authenticated) visit query) =
    PqxdhPhase2GapDhSource.prefixImpl domain
      (RegistrationBeaconRootInterpreter.auxImpl (RegistrationRootStage.lifted
        (RegistrationAgreementShared.implementation setup.source
          (RegistrationWorldRoot.primitive setup.source
            (RegistrationPublicConversion.primitive setup.source.crypto (RegistrationBeaconRoleBackend.localBackend setup))))) authenticated)
      (fun point => RegistrationRootStage.lift (RegistrationWorldBeaconRoot.visitShared point)) query := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl]
  all_goals try exact aux_exact setup seed scalar authenticated _
  simp only [interpret_bind, visit, liftProb_exact, interpret_pure]

private theorem map_state_apply {S X Y : Type} (mapResult : X → Y) (work : StateT S ProbComp X)
    (state : S) : (mapResult <$> work) state = Prod.map mapResult id <$> work state := by
  change (work state >>= fun result => pure (mapResult result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem rootLift_exact (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) (query : RootSpec.Domain) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar) (rootLift (n := n) (KemSK := KemSK) query) =
      PqxdhPhase2DhRootConsumer.familyImpl (A := Shared n KemSK) (family setup.hmac setup.joint setup.dh seed scalar) query := by
  funext before
  simp only [interpret, rootLift, StateT.run, simulateQ_map, simulateQ_spec_query, PqxdhPhase2DhRootConsumer.familyImpl]
  simp only [map_state_apply, Functor.map_map, Prod.map, id_eq]

/-- Full family, source cache and native World state agree through every optional failure of the actual public prefix and root continuation. -/
theorem stage_exact (setup : Setup base KemSK) (domain : PqxdhPhase2GapDhSource.PublicDomain setup.dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge)
    (authenticated : registration.AuthenticatedResponse) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar) (stage (n := n) setup domain publicValue authenticated) =
      RegistrationBeaconRootStage.stage domain
        (RegistrationAgreementShared.implementation setup.source
          (RegistrationWorldRoot.primitive setup.source
            (RegistrationPublicConversion.primitive setup.source.crypto (RegistrationBeaconRoleBackend.localBackend setup))))
        RegistrationWorldBeaconRoot.visitShared (family setup.hmac setup.joint setup.dh seed scalar) publicValue authenticated := by
  simp only [stage, RegistrationBeaconRootStage.stage, interpret_bind]
  rw [interpret_program _ _ _ (prefix_exact setup domain seed scalar authenticated)]
  congr 1
  funext pending
  cases pending with
  | none => exact interpret_pure _ _
  | some pending => exact interpret_program _ _ _ (rootLift_exact setup seed scalar) _

noncomputable def worldStage (setup : Setup base KemSK) (domain : PqxdhPhase2GapDhSource.PublicDomain setup.dh)
    (publicValue : PublicChallenge) (authenticated : registration.AuthenticatedResponse) :
    StateT (Local n KemSK) (OracleComp RootSpec) (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, result.2.1)) <$>
    (stage setup domain publicValue authenticated).run (before, before.world.1.primitive.2)

/-- Removing only the retained redundant outer cache recovers the complete actual World Beacon related-root stage. -/
theorem world_exact (setup : Setup base KemSK) (domain : PqxdhPhase2GapDhSource.PublicDomain setup.dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    interpret (family setup.hmac setup.joint setup.dh seed scalar)
      (worldStage (n := n) setup domain (challenge setup.joint setup.dh seed scalar) authenticated) =
      RegistrationWorldBeaconRoot.stage setup.source setup.hmac setup.joint setup.dh domain seed scalar
        (RegistrationBeaconRoleBackend.localBackend setup) authenticated := by
  funext before
  have same := congrFun (stage_exact (n := n) setup domain seed scalar (challenge setup.joint setup.dh seed scalar) authenticated)
    (before.1, (before.2, before.2.world.1.primitive.2))
  have mapped := congrArg (fun work => (fun result => (result.1, (result.2.1, result.2.2.1))) <$> work) same
  simpa only [interpret, worldStage, RegistrationWorldBeaconRoot.stage, family, StateT.run,
    simulateQ_map, map_state_apply, Functor.map_map, Prod.map, id_eq] using mapped

/-- The concrete public client under its real root service equals the actual native Beacon role backend, preserving the complete World and all native request operands. -/
theorem world_native (setup : Setup base KemSK)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : IdentitySeed) (scalar : ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (pin : absBytes authenticated.pending.control.expected_server_binding.identity_public_key =
      (setup.joint.publicKeys seed).ed25519.toList)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (before : RegistrationWorldRoot.FullState n (RegistrationBeaconRoleBackend.State KemSK)) :
    Prod.map id Prod.snd <$>
      (interpret (family setup.hmac setup.joint setup.dh seed scalar)
        (worldStage setup setup.beaconDomain (challenge setup.joint setup.dh seed scalar) authenticated)).run before =
      (simulateQ (RegistrationWorldAgreement.agreement setup.source (RegistrationBeaconRoleBackend.native setup scalar))
        (RegistrationAgreementExecutor.beacon authenticated)).run before.2 := by
  rw [world_exact, RegistrationBeaconRoleBackend.native_world]
  have actual := RegistrationWorldBeaconRoot.stage_project setup.source setup.hmac correct setup.joint setup.dh
    setup.beaconDomain seed scalar setup.secretOfSeed setup.wiring
    (RegistrationBeaconRoleBackend.localBackend setup) authenticated pin coherent before
  simpa only [RegistrationBeaconRoleBackend.public_conversion] using actual

end BeaconcryptCore.Computational.RegistrationBeaconRootCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.stage_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.stage_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.world_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.world_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.world_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconRootCompiler.world_native
