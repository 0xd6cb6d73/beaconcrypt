-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointCreation
import BeaconcryptCore.Computational.PqxdhLiveJointSigning

/-! Actual registration bundle generation through the indexed joint identity service. Public owner addresses and private creation indices remain distinct. Local prekey/one-time state stays with the client; its identity/KEM representation has no separate seed or KEM-secret coordinate. The identity lookup is explicit; the carried KEM index is not certified by this bundle-only equation. The complete signing history survives optional writer rejection. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBundle
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhBeaconPhase1Publication PqxdhJointPhase1SourceWriter
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

abbrev Identity := Nat × PqxdhEd25519EufCma.Ed25519PublicKey
abbrev Key := PqxdhKemIndCca.MlKem768PublicKey × Nat
abbrev Owner := RawCtxBeaconLifecycle.State Identity ScalarBytes Key

def identityMap (setup : Setup baseSpec KemSK) (index : Nat) (seed : IdentitySeed) : Identity :=
  (index, (setup.joint.publicKeys seed).ed25519)

def keyMap (index : Nat) (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) : Key :=
  (pair.1, index)

def projection (setup : Setup baseSpec KemSK) :
    PqxdhLivePhase1Bundle.Public Identity ScalarBytes Key :=
  ⟨Prod.fst, Prod.snd, setup.dh.publicKey, Prod.fst⟩

def encode (setup : Setup baseSpec KemSK) (identityIndex kemIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) : Owner :=
  mapState (identityMap setup identityIndex) (keyMap kemIndex) owner

def generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec ScalarBytes) (StateT A ProbComp) :=
  fun _ => StateT.lift (some <$> sampleScalar)

def writer (codec : Codec Reader Response) : QueryImpl WriterSpec (StateT A ProbComp) :=
  fun candidate => pure (codec.write1 candidate)

/-- The analysis records the exact source signing block before its optional writer; it does not disclose this private record to the client. -/
def after (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (generated : Option ScalarBytes)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState :=
  match prepare owner generated with
  | none => ((none, owner), pool)
  | some prepared =>
    let identity := (setup.joint.publicKeys owner.beacon.identity).ed25519
    let keys : PqxdhEd25519EufCma.Phase1KeyTuple :=
      ⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩
    let signed := signedState setup.joint owner.beacon.identity identityIndex keys pool
    match codec.write1 (signedCandidate setup.joint owner.beacon.identity identity keys) with
    | none => ((none, owner), signed)
    | some bytes => ((some bytes, publish (PqxdhLivePhase1Bundle.identityArray identity) prepared owner), signed)

/-- The only local draw is the actual Fresh one-time generation. Retained-coin and terminal branches retain their original source behavior. -/
def trace (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState) :
    ProbComp ((Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => (fun scalar => after setup codec identityIndex owner (some scalar) pool) <$> sampleScalar
  | .freshWithCoins _ _ _ _ => pure (after setup codec identityIndex owner none pool)
  | _ => pure ((none, owner), pool)

set_option backward.isDefEq.respectTransparency false in
/-- The handle client returns the exact mapped native owner and complete updated private signing state, retaining all auxiliary KEM, cache and scheduler state. -/
theorem client_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A)
    (created : pool.seeds[identityIndex]? = some owner.beacon.identity) :
    (simulateQ (PqxdhLiveJointSigning.impl setup.joint generate (writer codec))
      (PqxdhLivePhase1Bundle.bundle (projection setup) (encode setup identityIndex kemIndex owner))).run
        (pool, auxiliary) =
      (fun result => ((result.1.1, encode setup identityIndex kemIndex result.1.2), (result.2, auxiliary))) <$>
        trace setup codec identityIndex owner pool := by
  rw [show encode setup identityIndex kemIndex owner = mapState (identityMap setup identityIndex) (keyMap kemIndex) owner from rfl,
    ← PqxdhLivePhase1Bundle.bundle_map_run (identityMap setup identityIndex) (keyMap kemIndex)
      (PqxdhRegistrationSchedule.projection setup identityIndex) (projection setup)
      (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl)]
  rw [PqxdhLiveJointSigning.bundle_source setup.joint generate (writer codec)
    (PqxdhRegistrationSchedule.projection setup identityIndex) owner (pool, auxiliary)
    owner.beacon.identity created]
  cases phase : owner.beacon.phase <;> simp only [PqxdhLiveJointSigning.sourceBundle, trace, phase, generate,
    StateT.run_lift, map_bind, bind_map_left, map_pure, encode]
  all_goals simp only [PqxdhLiveJointSigning.sourceAfter, after, prepare, phase,
    PqxdhRegistrationSchedule.projection, afterSigning, simulateQ_bind, simulateQ_spec_query,
    writer, pure_bind, bind_assoc, Functor.map_map, Option.map_some]
  case fresh =>
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    intro scalar
    split <;> simp_all
  case freshWithCoins =>
    split <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- The literal native callback result is the first projection of the same complete signing trace. Its public owner address need not equal the private service index. -/
theorem native_after (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState) :
    simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.afterGenerated (PqxdhRegistrationSchedule.projection setup ownerAddress) generated owner) =
        pure (after setup codec identityIndex owner generated pool).1 := by
  unfold PqxdhLivePhase1Bundle.afterGenerated after
  cases prepared : prepare owner generated <;> simp only [simulateQ_pure, simulateQ_bind]
  simp only [PqxdhLivePhase1Bundle.signing, signingProgram, simulateQ_bind,
    simulateQ_spec_query, simulateQ_pure, PqxdhRegistrationSchedule.bundleCallbacks,
    pure_bind, Option.map_some, PqxdhLivePhase1Bundle.writing, afterSigning, prepared,
    PqxdhRegistrationSchedule.projection, signedCandidate]
  split <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- Complete native bundle execution uses precisely the same local draw as the indexed client, with the full source owner retained on every branch. -/
theorem native_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.bundle (PqxdhRegistrationSchedule.projection setup ownerAddress) owner) =
        Prod.fst <$> trace setup codec identityIndex owner pool := by
  cases phase : owner.beacon.phase <;> simp only [PqxdhLivePhase1Bundle.bundle, trace, phase,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, PqxdhRegistrationSchedule.bundleCallbacks,
    native_after setup codec ownerAddress identityIndex owner _ pool,
    bind_pure_comp, Functor.map_map, map_pure]

/-- The same trace reinstalls exactly the source owner at its public address, preserving every other owner and the complete shared Server and primitive state. -/
theorem native_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex : Nat) (state : PqxdhRegistrationSchedule.State KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (found : state.owners[ownerAddress]? = some owner) :
    (PqxdhRegistrationSchedule.bundle setup codec ownerAddress).run state =
      (fun result => (result.1.1, { state with owners := state.owners.set ownerAddress result.1.2 })) <$>
        trace setup codec identityIndex owner pool := by
  change PqxdhRegistrationSchedule.bundle setup codec ownerAddress state = _
  rw [PqxdhRegistrationSchedule.bundle_source setup codec ownerAddress state owner found,
    native_bundle setup codec ownerAddress identityIndex owner pool, Functor.map_map]

/-- Every complete source continuation receives the exact public reply, all owner states and the same shared caches. -/
theorem native_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ownerAddress identityIndex : Nat) (state : PqxdhRegistrationSchedule.State KemSK)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (found : state.owners[ownerAddress]? = some owner)
    (next : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State KemSK → ProbComp Result) :
    ((PqxdhRegistrationSchedule.bundle setup codec ownerAddress).run state >>= next) =
      (trace setup codec identityIndex owner pool >>= fun result =>
        next (result.1.1, { state with owners := state.owners.set ownerAddress result.1.2 })) := by
  rw [native_source setup codec ownerAddress identityIndex state owner pool found, bind_map_left]

/-- The exact handle-client equation remains valid for any continuation observing all its private state and prior history. -/
theorem client_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A)
    (created : pool.seeds[identityIndex]? = some owner.beacon.identity)
    (next : ((Option Pqxdh.Bytes × Owner) × (PqxdhDynamicIdentityPool.SourceState × A)) → ProbComp Result) :
    ((simulateQ (PqxdhLiveJointSigning.impl setup.joint generate (writer codec))
      (PqxdhLivePhase1Bundle.bundle (projection setup) (encode setup identityIndex kemIndex owner))).run
        (pool, auxiliary) >>= next) =
      (trace setup codec identityIndex owner pool >>= fun result =>
        next ((result.1.1, encode setup identityIndex kemIndex result.1.2), (result.2, auxiliary))) := by
  rw [client_source setup codec identityIndex kemIndex owner pool auxiliary created, bind_map_left]

/-- The actual source trace performs at most 32 local byte draws; retained coins and inactive phases perform none. Signing and optional writing are deterministic in these stated interfaces. -/
theorem trace_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) :
    (trace setup codec identityIndex owner pool).IsTotalQueryBound 32 := by
  cases phase : owner.beacon.phase <;> simp only [trace, phase, IsTotalQueryBound,
    isQueryBound_map_iff, isQueryBound_pure]
  exact sampleScalar_uniform

/-- Every admitted handle-client run pays for its complete evaluated randomness, retaining the separately counted three signing requests. -/
theorem client_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex kemIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (pool : PqxdhDynamicIdentityPool.SourceState) (auxiliary : A)
    (created : pool.seeds[identityIndex]? = some owner.beacon.identity) :
    ((simulateQ (PqxdhLiveJointSigning.impl setup.joint generate (writer codec))
      (PqxdhLivePhase1Bundle.bundle (projection setup) (encode setup identityIndex kemIndex owner))).run
        (pool, auxiliary)).IsTotalQueryBound 32 := by
  rw [client_source setup codec identityIndex kemIndex owner pool auxiliary created]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using trace_uniform setup codec identityIndex owner pool

/-- Before evaluation every branch is billed for at most one generation, three joint signature-service attempts and one optional writer attempt. -/
theorem client_bills (setup : Setup baseSpec KemSK) (owner : Owner)
    (kind : PqxdhLivePhase1Bundle.Kind) :
    (PqxdhLivePhase1Bundle.bundle (projection setup) owner).IsQueryBoundP
      (PqxdhLivePhase1Bundle.IsKind (D := ScalarBytes) kind)
      ((if kind = .generation then 1 else 0) +
        ((if kind = .signing then 3 else 0) + (if kind = .serialization then 1 else 0))) := by
  exact PqxdhLivePhase1Bundle.bundle_bound (projection setup) owner kind

/-- All three source signature replies extend the entire previous history even when the later writer rejects. No exact-three-total-history premise is used. -/
theorem after_history (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState)
    (prepared : Prepared ScalarBytes (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (ready : prepare owner generated = some prepared) :
    (after setup codec identityIndex owner generated pool).2 =
      signedState setup.joint owner.beacon.identity identityIndex
        ⟨setup.dh.publicKey prepared.prekey, setup.dh.publicKey prepared.oneTime, prepared.kem.1⟩ pool := by
  simp only [after, ready]
  split <;> rfl

/-- The complete private identity pool survives every local outcome, so the created-handle relation is available to later source operations. -/
theorem after_seeds (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (identityIndex : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK)
    (generated : Option ScalarBytes) (pool : PqxdhDynamicIdentityPool.SourceState) :
    (after setup codec identityIndex owner generated pool).2.seeds = pool.seeds := by
  cases prepared : prepare owner generated <;> simp only [after, prepared]
  split <;> rfl

end BeaconcryptCore.Computational.PqxdhRegistrationJointBundle

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_after
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_bundle
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.native_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.trace_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.trace_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.client_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.after_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.after_history
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.after_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBundle.after_seeds
