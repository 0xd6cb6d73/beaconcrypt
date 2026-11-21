-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleInitial
import BeaconcryptCore.Computational.PqxdhLiveKemOwnership

/-! The actual registration constructor uses the existing indexed joint identity and KEM services. Its client keeps its actual prekey locally and receives public identity/KEM replies and creation handles from the private services; those services retain the actual identity seeds and KEM pairs. The prekey draw stays between identity and KEM creation, and the one-time draw remains in the later bundle callback. This is a complete source-distribution correspondence, not a security assumption or a global protocol bound. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointCreation
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The client retains its actual private prekey but receives no identity seed or KEM secret. Service indices are distinct from public owner addresses. -/
structure Birth where
  identityIndex : Nat
  identity : PublicIdentity
  prekey : ScalarBytes
  kemIndex : Nat
  kemPublic : PqxdhKemIndCca.MlKem768PublicKey

/-- Literal identity, prekey, KEM ordering of `RegistrationSchedule.create`, with private cryptographic ownership moved only into the existing services. -/
def client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) (Option Birth) := do
  let identity ← (PqxdhLiveKemBirth.Spec KemSK).query (.inl (.inr .create))
  match identity with
  | none => pure none
  | some identity =>
      let prekey ← PqxdhLiveKemBirth.coins sampleScalar
      let pair ← (PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inr .create))
      pure (some ⟨identity.1, identity.2, prekey, pair.1, pair.2⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Every sampled value and both entire private service histories are retained. No generator moves across a continuation or across another generator. -/
theorem client_source (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (client (KemSK := KemSK))).run pool = (do
        let seed ← sampleSeed
        let prekey ← sampleScalar
        let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
        pure (some (⟨pool.1.seeds.length, setup.joint.publicKeys seed, prekey,
          pool.2.keys.length, pair.1⟩ : Birth),
          ((PqxdhDynamicIdentityPool.createdReply setup.joint pool.1 seed).2,
            (PqxdhLiveKemBirth.created pool.2 pair).2))) := by
  simp only [client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    PqxdhLiveKemBirth.joint_step, PqxdhDynamicIdentityPool.lazyImpl_create,
    bind_map_left, PqxdhDynamicIdentityPool.createdReply,
    PqxdhLiveKemBirth.coins_complete, simulateQ_pure, StateT.run_pure,
    PqxdhLiveKemBirth.created]
  simp only [StateT.run, PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl,
    bind_map_left, PqxdhLiveKemBirth.created]

/-- Private analysis of the source constructor's three actual generated values. This record is never returned by the indexed client. -/
structure Material (KemSK : Type) where
  seed : IdentitySeed
  prekey : ScalarBytes
  keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK

def material (setup : Setup baseSpec KemSK) : ProbComp (Material KemSK) := do
  let seed ← sampleSeed
  let prekey ← sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  pure ⟨seed, prekey, keys⟩

/-- Installation changes precisely the source owner list, retaining the complete shared Server, pending registrations, primitive caches and analysis state. -/
def install (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) (value : Material KemSK) :
    Nat × PqxdhRegistrationSchedule.State KemSK :=
  (state.owners.length, { state with owners := state.owners ++
    [⟨⟨value.seed, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ value.prekey value.keys⟩, 0⟩] })

set_option backward.isDefEq.respectTransparency false in
/-- The literal scheduler constructor has exactly this full result and poststate distribution, with no marginalization of earlier source state. -/
theorem native_source (setup : Setup baseSpec KemSK)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.create setup pin keyId).run state =
      install pin keyId state <$> material setup := by
  simp only [PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift,
    StateT.run_get, StateT.run_set, StateT.run_pure, bind_assoc,
    pure_bind, material, map_bind, map_pure, install]

/-- Mathematical view of the same private source draw through both existing services. Previous seed/KEM prefixes and histories are retained literally. -/
def serviceView (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK)
    (value : Material KemSK) : Option Birth × PqxdhLiveKemBirth.State KemSK :=
  (some ⟨pool.1.seeds.length, setup.joint.publicKeys value.seed, value.prekey,
    pool.2.keys.length, value.keys.1⟩,
    ((PqxdhDynamicIdentityPool.createdReply setup.joint pool.1 value.seed).2,
      (PqxdhLiveKemBirth.created pool.2 value.keys).2))

/-- The indexed client consumes the same complete joint source draw as the native constructor. This equation retains all actual private service fields, not just public-key marginals. -/
theorem client_material (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (client (KemSK := KemSK))).run pool = serviceView setup pool <$> material setup := by
  simpa only [serviceView, material, map_bind, map_pure] using client_source setup pool

/-- Every continued native distribution retains all previous owners, the new private owner, both primitive caches and the public address. -/
theorem native_continuation (setup : Setup baseSpec KemSK)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK)
    (next : Nat × PqxdhRegistrationSchedule.State KemSK → ProbComp Result) :
    ((PqxdhRegistrationSchedule.create setup pin keyId).run state >>= next) =
      (material setup >>= fun value => next (install pin keyId state value)) := by
  rw [native_source, bind_map_left]

/-- The same joint draw equation quantifies over the full later service continuation, including every private seed/KEM pair and all earlier logs. -/
theorem client_continuation (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK)
    (next : Option Birth × PqxdhLiveKemBirth.State KemSK → ProbComp Result) :
    ((simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (client (KemSK := KemSK))).run pool >>= next) =
      (material setup >>= fun value => next (serviceView setup pool value)) := by
  rw [client_material, bind_map_left]

/-- A supported creation cannot take the exhausted/failing identity-service branch: the ordinary lazy generator supplies the next actual seed. -/
theorem client_present (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK)
    (result : Option Birth × PqxdhLiveKemBirth.State KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (client (KemSK := KemSK))).run pool)) : ∃ birth, result.1 = some birth := by
  exact (show ∃ value, value ∈ support (material setup) ∧ serviceView setup pool value = result from
    by simpa only [client_material, support_map, Set.mem_image] using supported).elim
      (fun value witness => ⟨_, congrArg Prod.fst witness.2.symm⟩)

/-- The actual newly allocated indices recover exactly the source seed and KEM pair. Equal public encodings never select or merge either private slot. -/
theorem service_owns (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK)
    (value : Material KemSK) :
    (serviceView setup pool value).2.1.seeds[pool.1.seeds.length]? = some value.seed ∧
      (serviceView setup pool value).2.2.keys[pool.2.keys.length]? = some value.keys := by
  simp [serviceView, PqxdhDynamicIdentityPool.createdReply, PqxdhDynamicIdentityPool.record,
    PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record]

/-- One source constructor pays one joint identity request, one KEM request and 32 local byte draws. The private identity and KEM samplers are charged separately below. -/
theorem client_bills (kind : PqxdhLiveKemBirth.Kind) :
    (client (KemSK := KemSK)).IsQueryBoundP (PqxdhLiveKemBirth.IsKind (KemSK := KemSK) kind)
      ((if kind = .joint then 1 else 0) +
        ((if kind = .localUniform then 32 else 0) + (if kind = .kem then 1 else 0))) := by
  apply isQueryBoundP_bind
  case h' =>
    intro identity _
    cases identity with
    | some identity =>
      apply isQueryBoundP_bind (PqxdhLiveKemBirth.coins_bills sampleScalar 32 sampleScalar_uniform kind)
      simp +contextual [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff, PqxdhLiveKemBirth.IsKind]
    | none => simp
  case h => simp +contextual [isQueryBoundP_query_iff, PqxdhLiveKemBirth.IsKind]

/-- Interpreting creation charges both 32-byte source draws and every uniform query made by the complete KEM/base interpreter. `qKeygen` is a bound on that evaluated callback, not free ambient work. -/
theorem client_uniform (setup : Setup baseSpec KemSK) (pool : PqxdhLiveKemBirth.State KemSK)
    (qKeygen : Nat)
    (bounded : (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      setup.kem.keygen).IsTotalQueryBound qKeygen) :
    ((simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
      (client (KemSK := KemSK))).run pool).IsTotalQueryBound (64 + qKeygen) := by
  rw [client_source]
  apply (isTotalQueryBound_bind sampleSeed_uniform_bound (n₂ := 32 + qKeygen) ?_).mono (by omega)
  exact fun seed => isTotalQueryBound_bind sampleScalar_uniform (fun prekey => by
    simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using bounded)

end BeaconcryptCore.Computational.PqxdhRegistrationJointCreation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.native_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_material

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.native_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.native_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_present

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.service_owns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.service_owns

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointCreation.client_uniform
