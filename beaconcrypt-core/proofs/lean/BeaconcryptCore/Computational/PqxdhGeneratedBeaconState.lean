import BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication

/-!
Freshly generated private DH pairs enter a new native Beacon slot. Every existing identity/KEM representation remains in an `existing` payload, disjoint from the new `generated` handle even when the old value contains index zero or matching public bytes. Complete old controls, kernels, private DH pairs, routing fields, attempts and reveal histories are preserved. The new handle accepts only its index and public keys; no fresh Ed25519 seed or target KEM secret is a constructor argument. This representation separates old from freshly generated ownership but does not itself interpret the fresh secret or add a Phase2 capability.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedBeaconState
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhRootTableInitialization (rootArray)

variable {ι : Type} {baseSpec : OracleSpec ι} {M P A I K : Type} {S B : Nat}

/-- Old identities remain actual private payloads, disjoint from the newly generated source handle. -/
inductive IdentityHandle (PriorIdentity : Type) where
  | existing : PriorIdentity → IdentityHandle PriorIdentity
  | generated : Nat → PublicIdentity → IdentityHandle PriorIdentity

/-- Old KEM representations remain actual private payloads, disjoint from the fresh challenger handle. -/
inductive KemHandle (PriorKem : Type) where
  | existing : PriorKem → KemHandle PriorKem
  | generated : Nat → TargetKemPublicKey → KemHandle PriorKem

/-- Each original generated private pair is retained in full; the tag identifies its source role. -/
abbrev DhPair (setup : StatefulPhase1Setup baseSpec) :=
  PrivatePrekey setup.PrivatePre ⊕ PrivateOneTime setup.PrivateOne

abbrev Beacon (setup : StatefulPhase1Setup baseSpec) (I K : Type) :=
  RawCtxBeaconLifecycle.State (IdentityHandle I) (DhPair setup) (KemHandle K)

abbrev InitialState (setup : StatefulPhase1Setup baseSpec) (M P I K A : Type) (S B : Nat) :=
  PqxdhRegistrationProtocolState.State M P I (DhPair setup) K A S B

abbrev State (setup : StatefulPhase1Setup baseSpec) (M P I K A : Type) (S B : Nat) :=
  PqxdhRegistrationProtocolState.State M P (IdentityHandle I) (DhPair setup) (KemHandle K) A S B

/-- A complete old owner is embedded using the checked generic representation map. -/
def existing (setup : StatefulPhase1Setup baseSpec)
    (beacon : RawCtxBeaconLifecycle.State I (DhPair setup) K) : Beacon setup I K :=
  PqxdhBeaconPhase1Publication.mapState IdentityHandle.existing KemHandle.existing beacon

/-- Embedding an old object keeps every field, tagging only its private identity/KEM representation. -/
theorem existing_fields (setup : StatefulPhase1Setup baseSpec)
    (beacon : RawCtxBeaconLifecycle.State I (DhPair setup) K) :
    (existing setup beacon).beacon.identity = .existing beacon.beacon.identity ∧
    (existing setup beacon).beacon.identityKeyId = beacon.beacon.identityKeyId ∧
    (existing setup beacon).beacon.serverIdentity = beacon.beacon.serverIdentity ∧
    (existing setup beacon).rawAttempts = beacon.rawAttempts ∧
    (existing setup beacon).beacon.phase =
      PqxdhBeaconPhase1Publication.mapPhase KemHandle.existing beacon.beacon.phase :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A prior identity representation cannot alias the fresh source handle. -/
theorem existing_identity_ne_generated (prior : I) (index : Nat) (publicIdentity : PublicIdentity) :
    IdentityHandle.existing prior ≠ IdentityHandle.generated index publicIdentity := by
  intro equal
  cases equal

/-- A prior KEM representation cannot alias the fresh target handle. -/
theorem existing_kem_ne_generated (prior : K) (index : Nat) (target : TargetKemPublicKey) :
    KemHandle.existing prior ≠ KemHandle.generated index target := by
  intro equal
  cases equal

/-- Construction precedes Phase1 publication. The generated one-time pair remains local until the writer succeeds. -/
def fresh (setup : StatefulPhase1Setup baseSpec) (index : Nat) (publicIdentity : PublicIdentity)
    (generated : Generated setup Unit) (binding : pqxdh.ServerBinding) : Beacon setup I K :=
  ⟨⟨.generated index publicIdentity, binding.identity_key_id, binding.identity_public_key,
    .fresh ⟨binding⟩ (.inl generated.before) (.generated index generated.target)⟩, 0⟩

def embedOwner : RawCtxProtocolReveals.Owner S B → RawCtxProtocolReveals.Owner S (B + 1)
  | .server index peer => .server index peer
  | .beacon index => .beacon index.succ

def embedRequest : RawCtxProtocolReveals.Request S B → RawCtxProtocolReveals.Request S (B + 1)
  | .sendChain owner => .sendChain (embedOwner owner)
  | .receiveChain owner => .receiveChain (embedOwner owner)
  | .skippedKey owner sequence => .skippedKey (embedOwner owner) sequence

def embedObservation (observation : RawCtxProtocolReveals.Observation S B) :
    RawCtxProtocolReveals.Observation S (B + 1) :=
  match observation with
  | ⟨.sendChain owner, reply⟩ => ⟨.sendChain (embedOwner owner), reply⟩
  | ⟨.receiveChain owner, reply⟩ => ⟨.receiveChain (embedOwner owner), reply⟩
  | ⟨.skippedKey owner sequence, reply⟩ => ⟨.skippedKey (embedOwner owner) sequence, reply⟩

def embedHistory (history : RawCtxProtocolReveals.History S B) :
    RawCtxProtocolReveals.History S (B + 1) :=
  ⟨history.position, history.observations.map (fun entry => (entry.1, embedObservation entry.2))⟩

/-- Fin.succ retains every prior owner; index zero is newly allocated for this generated Beacon. -/
def extend {setup : StatefulPhase1Setup baseSpec}
    (beacon : Beacon setup I K) (state : InitialState setup M P I K A S B) : State setup M P I K A S (B + 1) :=
  ⟨((state.roles.1.1, Fin.cons beacon (fun index => existing setup (state.roles.1.2 index))), embedHistory state.roles.2),
    state.controls, state.consumed, state.primitive⟩

theorem extend_fields {setup : StatefulPhase1Setup baseSpec}
    (beacon : Beacon setup I K) (state : InitialState setup M P I K A S B) :
    (extend beacon state).roles.1.2 0 = beacon ∧
    (∀ index, (extend beacon state).roles.1.2 index.succ = existing setup (state.roles.1.2 index)) ∧
    (extend beacon state).roles.1.1 = state.roles.1.1 ∧
    (extend beacon state).controls = state.controls ∧
    (extend beacon state).consumed = state.consumed ∧
    (extend beacon state).primitive = state.primitive ∧
    (extend beacon state).roles.2 = embedHistory state.roles.2 := by
  simp [extend]

/-- Prior compromise observations still select the same actual kernel after adding the new object. -/
theorem extend_kernel {setup : StatefulPhase1Setup baseSpec}
    (beacon : Beacon setup I K) (state : InitialState setup M P I K A S B) (owner : RawCtxProtocolReveals.Owner S B) :
    RawCtxProtocolReveals.selectedKernel (embedOwner owner) (extend beacon state).roles.1 =
      RawCtxProtocolReveals.selectedKernel owner state.roles.1 := by
  cases owner with
  | server index peer => rfl
  | beacon index =>
      simp only [RawCtxProtocolReveals.selectedKernel, embedOwner, extend, Fin.cons_succ,
        existing, PqxdhBeaconPhase1Publication.mapState]
      cases (state.roles.1.2 index).beacon.phase <;> rfl

/-- Publication changes only the fresh slot, retaining callback state and every earlier object/history. -/
def reinstall {setup : StatefulPhase1Setup baseSpec}
    (state : State setup M P I K A S (B + 1))
    (result : (Option Pqxdh.Bytes × Beacon setup I K) × RawCtxSharedPrimitive.SharedState A) :
    Option Pqxdh.Bytes × State setup M P I K A S (B + 1) :=
  (result.1.1,
    { state with
      roles := ((state.roles.1.1, Function.update state.roles.1.2 0 result.1.2), state.roles.2)
      primitive := result.2 })

noncomputable def start (setup : StatefulPhase1Setup baseSpec)
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (binding : pqxdh.ServerBinding) (bundle : Phase1Candidate) (state : InitialState setup M P I K A S B) :
    ProbComp (Option Pqxdh.Bytes × State setup M P I K A S (B + 1)) :=
  let beacon := fresh setup index publicIdentity generated binding
  reinstall (extend beacon state) <$>
    (simulateQ writer (PqxdhBeaconPhase1Publication.afterSigning (rootArray publicIdentity.ed25519)
      bundle (some (.inr generated.after)) beacon)).run state.primitive

/-- The complete exact source writer result precedes publication; failure retains Fresh and discards only the local one-time pair. -/
theorem start_complete (setup : StatefulPhase1Setup baseSpec)
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (binding : pqxdh.ServerBinding) (bundle : Phase1Candidate) (state : InitialState setup M P I K A S B) :
    start setup writer index publicIdentity generated binding bundle state =
      (writer bundle).run state.primitive >>= fun result =>
        let beacon := fresh setup index publicIdentity generated binding
        let current := extend beacon state
        match result.1 with
        | none => pure (none, { current with primitive := result.2 })
        | some bytes => pure (some bytes,
            { current with
              roles := ((current.roles.1.1,
                Function.update current.roles.1.2 0
                  (PqxdhBeaconPhase1Publication.publish (rootArray publicIdentity.ed25519)
                    ⟨⟨binding⟩, .inl generated.before, .inr generated.after, (.generated index generated.target)⟩ beacon)), current.roles.2)
              primitive := result.2 }) := by
  simp only [start, PqxdhBeaconPhase1Publication.afterSigning,
    PqxdhBeaconPhase1Publication.prepare, fresh, Option.map_some, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind, map_bind]
  apply bind_congr
  intro result
  cases result.1 <;> simp [reinstall, extend]

/-- Source Phase1 serialization is real work with its own explicit uniform-call allowance. -/
theorem start_uniform (setup : StatefulPhase1Setup baseSpec)
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qWrite : Nat) (bounded : ∀ bundle auxiliary, ((writer bundle).run auxiliary).IsTotalQueryBound qWrite)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (binding : pqxdh.ServerBinding) (bundle : Phase1Candidate) (state : InitialState setup M P I K A S B) :
    (start setup writer index publicIdentity generated binding bundle state).IsTotalQueryBound qWrite := by
  rw [start_complete]
  simpa only [Nat.add_zero] using isTotalQueryBound_bind (bounded bundle state.primitive)
    (n₂ := 0) (fun result => by cases result.1 <;> trivial)

/-- The exact Phase1 result changes no Server identity, peer map, registration control or consumed history. -/
theorem start_servers (setup : StatefulPhase1Setup baseSpec)
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (binding : pqxdh.ServerBinding) (bundle : Phase1Candidate) (state : InitialState setup M P I K A S B)
    (result : Option Pqxdh.Bytes × State setup M P I K A S (B + 1))
    (present : result ∈ support (start setup writer index publicIdentity generated binding bundle state)) :
    result.2.roles.1.1 = state.roles.1.1 ∧ result.2.controls = state.controls ∧ result.2.consumed = state.consumed := by
  rw [start_complete, mem_support_bind_iff] at present
  obtain ⟨written, _, present⟩ := present
  dsimp only at present
  cases reply : written.1 <;>
    simp only [reply] at present <;>
    have equal := eq_of_mem_support_pure _ present <;>
    subst result <;> exact ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.PqxdhGeneratedBeaconState

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_identity_ne_generated' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_identity_ne_generated

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_kem_ne_generated' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.existing_kem_ne_generated

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.extend_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.extend_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.extend_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.extend_kernel

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_servers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedBeaconState.start_servers
