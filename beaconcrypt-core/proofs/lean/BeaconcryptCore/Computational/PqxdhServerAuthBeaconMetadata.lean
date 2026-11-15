-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins

/-! Valid generation/control and exact AD-retention facts of the generic post-hash suffix. AD151 is the supplied completed-binding metadata retained by the actual tail; these lemmas do not infer an Ed identity from opaque AD or establish that a current transcript hash was performed. Current source identity recovery uses its separate real Init/hash/cache receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity
variable (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity PqxdhJointGapDh
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The original Phase1 publication installs the exact pinned Server and generated Beacon identity fields. -/
theorem phase1_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (result : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (supported : result ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)) :
    ∀ control prekey other kem, result.2.beacon.phase = .initSent control prekey other kem →
      control.expected_server_binding = binding setup publicValue ∧
      control.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys beaconSeed).ed25519 := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon, simulateQ_bind, simulateQ_spec_query,
    mem_support_bind_iff] at supported
  obtain ⟨generated, _, supported⟩ := supported
  intro control prekey other kem phase
  cases generated with
  | none =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_none,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases phase
  | some generated =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_some,
        simulateQ_bind, mem_support_bind_iff] at supported
      obtain ⟨signed, _, supported⟩ := supported
      cases signed with
      | none =>
          simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases phase
      | some bundle =>
          simp only [PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
            PqxdhBeaconPhase1Publication.prepare, Option.map_some, simulateQ_bind, simulateQ_spec_query,
            mem_support_bind_iff] at supported
          obtain ⟨written, _, supported⟩ := supported
          cases written with
          | none =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              cases phase
          | some bytes =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              simp only [PqxdhBeaconPhase1Publication.publish, RawCtxBeaconLifecycle.Phase.initSent.injEq] at phase
              rw [← phase.1]
              exact ⟨rfl, rfl⟩

/-- The actual successful Beacon prefix supplies its original metadata admission equation. -/
theorem prefix_admitted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (supported : some pending ∈ support ((beaconPrefix (completedBinding := completedBinding) setup codec beaconSeed control identity oneTime kem raw).run' ())) :
    PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control pending.collected = some pending.metadata := by
  simp only [beaconPrefix, PqxdhPhase2DhMetadata.prepare, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, support_map, Set.mem_image,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, ⟨⟨collected, state⟩, reached, rfl⟩, same⟩ := supported
  cases collected with
  | none => cases same
  | some input =>
    simp only [Option.bind_some] at same
    cases admitted : PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control input with
    | none => simp only [admitted, Option.map_none, reduceCtorEq] at same
    | some metadata =>
      simp only [admitted, Option.map_some, Option.some.injEq] at same
      cases same
      exact admitted

/-- Every successful sequence/binding gate retains the exact AD151 supplied by its post-hash caller. -/
theorem opening_ad (candidate : pqxdh.BeaconRegistrationCandidate)
    (associatedData : Std.Array U8 151#usize) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : PqxdhBeaconPhase2Publication.Staged)
    (accepted : PqxdhBeaconPhase2Publication.afterOpening candidate associatedData kernel reply = some staged) :
    staged.associatedData = associatedData := by
  unfold PqxdhBeaconPhase2Publication.afterOpening at accepted
  cases reply with
  | none => cases accepted
  | some opened =>
    dsimp only at accepted
    split_ifs at accepted
    split at accepted
    · contradiction
    · cases accepted
      rfl

/-- The complete concrete factored tail retains the actual admitted associated data for every successful optional result. -/
theorem factor_ad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (value : PqxdhServerAuthSendFactor.Factor)
    (before : RawCtxSharedPrimitive.SharedState Unit)
    (result : Option PqxdhBeaconPhase2Publication.Staged × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((PqxdhServerAuthBeaconFactor.factored
      (PqxdhServerAuthBeaconFactor.nativePrim setup codec) (fun entry _ => pure (entry, none)) setup.source
      (fun response => pure (codec.application response)) codec.frameRead
      (PqxdhPhase2DhRootConsumer.cleared pending) value).run before))
    (staged : PqxdhBeaconPhase2Publication.Staged) (returned : result.1 = some staged) :
    staged.associatedData = pending.metadata.associatedData := by
  simp only [PqxdhServerAuthBeaconFactor.factored, pure_bind] at supported
  cases raw : codec.application pending.collected.response with
  | none =>
    simp only [PqxdhPhase2DhRootConsumer.cleared, raw, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    cases returned
  | some raw =>
    simp only [PqxdhPhase2DhRootConsumer.cleared, raw, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact opening_ad _ _ _ _ staged returned

/-- The original known-root tail has the same associated-data property through its exact complete source factorization. -/
theorem native_ad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : PqxdhSecretInputKdf.RootOutput)
    (before : RawCtxSharedPrimitive.SharedState Unit)
    (result : Option PqxdhBeaconPhase2Publication.Staged × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((simulateQ (beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run before))
    (staged : PqxdhBeaconPhase2Publication.Staged) (returned : result.1 = some staged) :
    staged.associatedData = pending.metadata.associatedData := by
  rw [PqxdhServerAuthBeaconFactor.beacon_afterRoot_run setup codec (fun entry _ => pure (entry, none))] at supported
  exact factor_ad setup codec pending _ before result supported staged returned

end BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.phase1_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.phase1_control

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.prefix_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.prefix_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.opening_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.opening_ad

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_ad

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.native_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.native_ad
