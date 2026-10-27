-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleCosts

/-! Generated Server birth and admitted Beacon construction in literal source order, retaining runtime and complete deployment state. The public Rust adapter remains reviewed transcription; CE's approved once-only initialization scope is unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryBirth
open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}

/-- Initialization precedes the actual generated identity; a failed initialization retains its returned runtime and makes no identity draw. -/
def serverBirth (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (sender : Std.U64) :
    StateT A ProbComp (Option (PqxdhLiveServerConstruction.Created Unit)) := fun runtime => do
  let ready ← ensureInit.run runtime
  if ready.1 then
    let seed ← sampleSeed
    pure (some (PqxdhLiveServerConstruction.initialized primitives identityIndex sender .generated seed), ready.2)
  else pure (none, ready.2)

/-- The CE generated-only constructor is this complete source-ordered runtime execution. -/
theorem server_source (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (sender : Std.U64) :
    PqxdhLiveServerConstruction.construct (P := Unit) primitives ensureInit identityIndex sender none =
      serverBirth primitives ensureInit identityIndex sender := by
  funext runtime
  simp only [PqxdhLiveServerConstruction.construct, serverBirth, bind_pure_comp]

/-- An arbitrary continuation sees the actual constructor result together with the returned runtime; failed initialization does not erase its effects. -/
theorem server_continuation (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (sender : Std.U64) (runtime : A)
    (next : Option (PqxdhLiveServerConstruction.Created Unit) × A → ProbComp Result) :
    (PqxdhLiveServerConstruction.construct (P := Unit) primitives ensureInit identityIndex sender none).run runtime >>= next =
      ensureInit.run runtime >>= fun ready =>
        if ready.1 then sampleSeed >>= fun seed =>
          next (some (PqxdhLiveServerConstruction.initialized primitives identityIndex sender .generated seed), ready.2)
        else next (none, ready.2) := by
  rw [server_source]
  simp only [serverBirth, StateT.run, bind_assoc]
  apply bind_congr
  intro ready
  split <;> simp only [bind_assoc, pure_bind]

/-- Generated Server birth is charged the declared runtime-initialization bill on every attempt and, after successful initialization, the 32 uniform byte draws of the generated identity seed (`PqxdhLiveServerConstruction.construct_uniform` at `supplied = none`). The initialization bill `initBound` is the same premise form the CE headlines carry. -/
theorem server_bills (primitives : Primitives) (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (identityIndex : Nat) (sender : Std.U64) (runtime : A) :
    ((serverBirth primitives ensureInit identityIndex sender).run runtime).IsTotalQueryBound (qInit + 32) := by
  rw [← server_source]
  simpa only [Option.isNone_none, ite_true] using
    PqxdhLiveServerConstruction.construct_uniform (P := Unit) primitives ensureInit qInit initBound
      identityIndex sender none runtime

/-- Admitted Beacon creation in the source order of `Beacon::try_new` (`beaconcrypt/src/beacon.rs:65-82`) after CE deviation D1 (no repeated runtime initialization at creation): the 32-byte width parse of the pinned Server identity key (`PublicKey::from_bytes`, `beacon.rs:68`); a wrong width returns `none` with no draw and the complete state unchanged; otherwise the identity seed, the prekey scalar and the ML-KEM key pair are generated in that order and the fresh owner is appended at the next handle. Every other field of the deployment state (Server, pending tokens, caches, counters, produced frames, the other owners) is the entry state's. -/
noncomputable def beaconCreate (setup : Setup baseSpec KemSK) (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option Nat) := fun state =>
  match PqxdhDeploymentInterface.parsePin pin with
  | none => pure (none, state)
  | some word => do
      let identity ← sampleSeed
      let prekey ← sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let owner : PqxdhRegistrationSchedule.Owner KemSK :=
        ⟨⟨identity, keyId, word, .fresh ⟨⟨word, keyId⟩⟩ prekey keys⟩, 0⟩
      pure (some state.native.owners.length,
        { state with native := { state.native with owners := state.native.owners ++ [owner] } })

/-- An admitted pin runs exactly the published post-admission constructor `PqxdhRegistrationSchedule.create` on the registration state and reinstalls its complete result; the counters and produced frames of the deployment state are kept. -/
theorem beaconCreate_native (setup : Setup baseSpec KemSK) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (word : PqxdhBeaconPhase2Preparation.Word32) (parsed : PqxdhDeploymentInterface.parsePin pin = some word)
    (state : PqxdhDeploymentNative.State KemSK) :
    (beaconCreate setup pin keyId).run state =
      (fun result => (some result.1, { state with native := result.2 })) <$>
        (PqxdhRegistrationSchedule.create setup word keyId).run state.native := by
  change beaconCreate setup pin keyId state = _
  change _ = _ <$> PqxdhRegistrationSchedule.create setup word keyId state.native
  rw [PqxdhRegistrationSchedule.create_source]
  simp only [beaconCreate, parsed, map_bind, map_pure]

/-- The CE `create` command is exactly the source-ordered Beacon creation, on every deployment state, for every pin (both the wrong-width rejection and every admitted creation) and every key ID. -/
theorem create_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.create pin keyId))).run state =
      (beaconCreate setup pin keyId).run state := by
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none =>
    change _ = beaconCreate setup pin keyId state
    simp only [PqxdhDeploymentNative.handler, parsed, beaconCreate, StateT.run_pure]
  | some word =>
    rw [beaconCreate_native setup pin keyId word parsed]
    simp only [PqxdhDeploymentNative.handler, parsed, PqxdhRegistrationSchedule.handler]
    change (some <$> PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.create setup word keyId)).run state = _
    rw [StateT.run_map]
    simp only [PqxdhDeploymentNative.onNative, StateT.run, Functor.map_map]

/-- An arbitrary continuation of the CE `create` command sees the actual creation result and complete deployment state in source order. -/
theorem create_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (state : PqxdhDeploymentNative.State KemSK)
    (next : Option Nat × PqxdhDeploymentNative.State KemSK → ProbComp Result) :
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.create pin keyId))).run state >>= next =
      (beaconCreate setup pin keyId).run state >>= next := by
  rw [create_source]

/-- A wrong-width pin is rejected by the source creation with no draw and the complete state unchanged. -/
theorem create_rejects (setup : Setup baseSpec KemSK) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (width : pin.length ≠ 32) (state : PqxdhDeploymentNative.State KemSK) :
    (beaconCreate setup pin keyId).run state = pure (none, state) := by
  have parsed : PqxdhDeploymentInterface.parsePin pin = none := by
    simp only [PqxdhDeploymentInterface.parsePin, PqxdhServerAuthExperiment.toWord32, width, _root_.dite_false]
  change beaconCreate setup pin keyId state = _
  simp only [beaconCreate, parsed]

/-- Source creation spends at most the two 32-byte draws and the declared ML-KEM generation and base-interpreter bill (`PqxdhRegistrationSchedule.create_uniform`); a rejected pin draws nothing. -/
theorem create_bills (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (state : PqxdhDeploymentNative.State KemSK) :
    ((beaconCreate setup pin keyId).run state).IsTotalQueryBound (64 + caps.keygenCost) := by
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none =>
    change (beaconCreate setup pin keyId state).IsTotalQueryBound _
    simp only [beaconCreate, parsed]
    trivial
  | some word =>
    rw [beaconCreate_native setup pin keyId word parsed]
    exact (isQueryBound_map_iff _ _ _ _ _).mpr
      (PqxdhRegistrationSchedule.create_uniform setup caps bounded word keyId state.native)

end BeaconcryptCore.Computational.PqxdhBoundaryBirth

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_source

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.server_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.beaconCreate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.beaconCreate_native

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_source

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_rejects

/--
info: 'BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryBirth.create_bills
