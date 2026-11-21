-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
/-! Literal global embeddings transport corrected Beacon source materialization through public owner selection and the same persistent platform coordinate. Selected or ordinary scalar preparation changes only preparation queries, independently of the private seed interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFinish
variable {n : Nat} {KemSK Platform A : Type}

noncomputable def embedding : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal ∘ₛ
    RegistrationNativePlatformPublicFrontend.localQuery false

private theorem embedding_source : embedding (n := n) (KemSK := KemSK) = RegistrationNativePublicFrontend.liftLocal false := by
  funext query
  rcases query with prepare | service | kem
  · rfl
  · rfl
  · simp only [embedding, QueryImpl.apply_compose, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativePublicFrontend.liftLocal, QueryImpl.simulateQ_compose]
    rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
    congr 1
private theorem routed (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    RegistrationNativeG3MaterializedLocal.translate (KemSK := KemSK) full seeds ∘ₛ RegistrationNativePublicFrontend.liftRoutedKem =
      RegistrationNativePublicFrontend.liftRoutedKem := by
  funext query
  rfl

private theorem translation (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    RegistrationNativeG3MaterializedLocal.translate (KemSK := KemSK) full seeds ∘ₛ embedding =
      embedding ∘ₛ RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds := by
  rw [embedding_source]
  funext query
  rcases query with prepare | ((message | (publication | environment)) | kem)
  · rfl
  · cases full <;> rfl
  · rfl
  · cases environment with
    | inl coin => cases full <;> rfl
    | inr capability =>
      cases capability <;> try (cases full <;> rfl)
      case installServer keyId binding kernel => cases kernel <;> cases full <;> rfl
      case installBeacon owner shell kernel => cases kernel <;> cases full <;> rfl
  · simp only [QueryImpl.apply_compose, RegistrationNativePublicFrontend.liftLocal,
      RegistrationNativePlatformMaterializedBeaconFrontend.translate, simulateQ_spec_query]
    rw [← QueryImpl.simulateQ_compose, routed]
private theorem ordinary_commutes {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :
    RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds ∘ₛ RegistrationNativePublicOwners.ordinary setup scalar =
      RegistrationNativePublicOwners.ordinary setup scalar ∘ₛ RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds := by
  funext query
  rcases query with prepare | ((message | (publication | environment)) | kem)
  · cases mapped : RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar prepare <;>
      simp only [QueryImpl.apply_compose, RegistrationNativePublicOwners.ordinary, mapped,
        RegistrationNativePlatformMaterializedBeaconFrontend.translate, simulateQ_pure, simulateQ_spec_query]
  · cases full <;> rfl
  · rfl
  · cases environment with
    | inl coin => cases full <;> rfl
    | inr capability =>
      cases capability <;> try (cases full <;> rfl)
      case installServer keyId binding kernel => cases kernel <;> cases full <;> rfl
      case installBeacon owner shell kernel => cases kernel <;> cases full <;> rfl
  · rfl
private theorem lifted_plain (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run before =
      (fun value => (value, before)) <$>
        simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.localHandler,
        StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, ih, map_bind]

private theorem lifted (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        ((simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run before)) =
      (fun value => (value, before)) <$> simulateQ embedding work := by
  rw [lifted_plain]
  simp only [simulateQ_map, embedding, QueryImpl.simulateQ_compose]

private theorem translated (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (before : Platform) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate full seeds)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          ((simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run before))) =
      (fun value => (value, before)) <$>
        simulateQ embedding (simulateQ (RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds) work) := by
  rw [lifted, simulateQ_map, ← QueryImpl.simulateQ_compose, translation, QueryImpl.simulateQ_compose]
private theorem ordinary_program {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (full : Bool) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) :
    simulateQ (RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds)
      (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work) =
      simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
        (simulateQ (RegistrationNativePlatformMaterializedBeaconFrontend.translate full seeds) work) := by
  rw [← QueryImpl.simulateQ_compose, ordinary_commutes, QueryImpl.simulateQ_compose]

private theorem reference_source {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (scalar : Option PqxdhJointGapDh.ScalarBytes) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (env : RegistrationServerReferenceCompiler.Environment) :
    simulateQ (RegistrationNativePlatformMaterializedBeaconFrontend.translate true seeds)
      (match scalar with
        | none => ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env
        | some value => simulateQ (RegistrationNativePublicOwners.ordinary setup value)
            (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)) =
      simulateQ (RegistrationNativePlatformMaterializedBeaconFrontend.translate false seeds)
        (match scalar with
          | none => ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env
          | some value => simulateQ (RegistrationNativePublicOwners.ordinary setup value)
              (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)) := by
  cases scalar with
  | none => exact RegistrationNativePlatformMaterializedBeaconFinish.finish_source setup wire source seeds packet owner env
  | some value =>
      rw [ordinary_program, ordinary_program, RegistrationNativePlatformMaterializedBeaconFinish.finish_source]

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : V → W) (work : StateT S m V) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

private theorem local_source {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source) (index : Nat)
    (packet : Option registration.ResponsePacket) (owners : RegistrationNativePublicOwners.State source)
    (env : RegistrationServerReferenceCompiler.Environment) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) (previous : Platform) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate true seeds)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          ((((RegistrationNativePlatformPublicFrontend.finish setup wire source index packet).run owners).run env).run previous))) =
      simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
            ((((RegistrationNativePlatformPublicFrontend.finish setup wire source index packet).run owners).run env).run previous))) := by
  cases found : owners[index]? with
  | none =>
      simp only [RegistrationNativePlatformPublicFrontend.finish, found, StateT.run]
      change simulateQ (RegistrationNativeG3MaterializedLocal.translate true seeds)
          (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
            (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (pure (((RustM.ok (none : Option Pqxdh.Bytes), owners), env), previous)))) = _
      simp only [simulateQ_pure]
      rfl
  | some owner =>
      simp only [RegistrationNativePlatformPublicFrontend.finish, found, StateT.run, map_apply, simulateQ_map]
      let work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)
          ((RustM (Option Pqxdh.Bytes) × RegistrationBeaconReferenceCompiler.SelectedOwner source) × RegistrationServerReferenceCompiler.Environment) := match owner.scalar with
        | none => ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run env
        | some scalar => simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
            (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run env)
      have sourceEq := congrArg (fun action => (fun value => (value, previous)) <$> simulateQ (embedding (n := n) (KemSK := KemSK)) action)
        (reference_source setup wire source packet owner.view owner.scalar seeds env)
      have compared := (translated true seeds work previous).trans (sourceEq.trans (translated false seeds work previous).symm)
      exact congrArg (Functor.map (Prod.map (fun result => ((result.1.1, owners.set index { owner with view := result.1.2 }), result.2)) id)) compared
/-- The entire literal corrected public finish retains its frontend, returned application and shared P under known/opaque materialization. -/
theorem finish_source {I : Type} {base : OracleSpec I} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) {source : RegistrationNativeMldsa.Source} (index : Nat)
    (packet : Option registration.ResponsePacket) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    simulateQ (RegistrationNativeG3MaterializedLocal.translate true seeds)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (KemSK := KemSK)
          (RegistrationNativePlatformPublicFrontend.beacon
            (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run before)) =
      simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds)
        (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
          ((RegistrationNativePlatformPublicFrontend.executeLocal (KemSK := KemSK)
            (RegistrationNativePlatformPublicFrontend.beacon
              (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run before)) := by
  have same := local_source setup wire source index packet before.1.beacons before.1.environment seeds before.2
  have mapped := congrArg (Functor.map (fun result =>
    (result.1.1.1, ({ before.1 with beacons := result.1.1.2, environment := result.1.2 }, result.2)))) same
  simpa only [RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    StateT.run, simulateQ_map] using mapped
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedFinish.finish_source
