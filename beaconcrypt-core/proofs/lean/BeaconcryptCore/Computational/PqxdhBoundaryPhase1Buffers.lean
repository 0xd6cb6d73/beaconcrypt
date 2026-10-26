-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryPhase1Native

/-! The actual extracted unsigned builder supplies the native Phase-1 signing and optional writer buffers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.ProtocolComposition
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRegistrationSchedule (Owner)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}

/-- Exact byte conversion to the extracted 32-byte input representation. -/
def array32 (bytes : List.Vector UInt8 32) : Std.Array Std.U8 32#usize :=
  ⟨bytes.toList.map concreteByte, by simp⟩

/-- Exact byte conversion to the extracted ML-KEM-768 public-key representation. -/
def array1184 (bytes : List.Vector UInt8 1184) : Std.Array Std.U8 1184#usize :=
  ⟨bytes.toList.map concreteByte, by simp⟩

theorem array32_bytes (bytes : List.Vector UInt8 32) : absBytes (array32 bytes) = bytes.toList := by
  simp [array32, absBytes, List.map_map, Function.comp_def]

theorem array1184_bytes (bytes : List.Vector UInt8 1184) : absBytes (array1184 bytes) = bytes.toList := by
  simp [array1184, absBytes, List.map_map, Function.comp_def]

/-- The inputs use precisely the native owner's identity and already-prepared public keys. -/
def inputs (setup : Setup baseSpec KemSK) (owner : Owner KemSK)
    (prepared : PqxdhBeaconPhase1Publication.Prepared PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) : pqxdh.BeaconStartInputs :=
  ⟨array32 (setup.joint.publicKeys owner.beacon.identity).ed25519,
    array32 (setup.dh.publicKey prepared.prekey), array1184 prepared.kem.1⟩

def coins (setup : Setup baseSpec KemSK)
    (prepared : PqxdhBeaconPhase1Publication.Prepared PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) : pqxdh.BeaconCoins :=
  ⟨array32 (setup.dh.publicKey prepared.oneTime)⟩

/-- The real extracted builder returns the exact tagged fields and complete InitSent control for these actual native projections. -/
theorem core_build (setup : Setup baseSpec KemSK) (owner : Owner KemSK)
    (prepared : PqxdhBeaconPhase1Publication.Prepared PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK)) :
    ∃ out : pqxdh.BeaconStart,
      pqxdh.beacon_start prepared.control (inputs setup owner prepared) (coins setup prepared) = ok out ∧
      out.state = PqxdhBeaconPhase1Publication.control prepared.control
        (PqxdhLivePhase1Bundle.identityArray (setup.joint.publicKeys owner.beacon.identity).ed25519) ∧
      absBytes out.message.identity_key = PqxdhEd25519EufCma.encodedIdentity (setup.joint.publicKeys owner.beacon.identity).ed25519 ∧
      absBytes out.message.prekey = PqxdhEd25519EufCma.prekeyMessage (setup.dh.publicKey prepared.prekey) ∧
      absBytes out.message.one_time_key = PqxdhEd25519EufCma.oneTimeMessage (setup.dh.publicKey prepared.oneTime) ∧
      absBytes out.message.pq_key = PqxdhEd25519EufCma.pqMessage prepared.kem.1 := by
  obtain ⟨out, built, pin, identity, prekey, oneTime, pq⟩ :=
    PqxdhJointPhase1SourceWriter.beacon_start_unsigned prepared.control (inputs setup owner prepared) (coins setup prepared)
  obtain ⟨started, same, control⟩ := PqxdhBeaconPhase1Publication.core_control prepared.control (inputs setup owner prepared) (coins setup prepared)
  rw [built] at same
  cases (show out = started from by injection same)
  refine ⟨out, built, control, ?_⟩
  simpa only [inputs, coins, array32_bytes, array1184_bytes, PqxdhEd25519EufCma.encodedIdentity, PqxdhEd25519EufCma.prekeyMessage, PqxdhEd25519EufCma.oneTimeMessage, PqxdhEd25519EufCma.pqMessage] using And.intro identity (And.intro prekey (And.intro oneTime pq))

/-- These attached signatures consume the exact extracted unsigned buffers in source order. -/
def signedOutput (setup : Setup baseSpec KemSK) (owner : Owner KemSK)
    (out : pqxdh.BeaconStart) : PqxdhEd25519EufCma.Phase1Candidate :=
  ⟨absBytes out.message.identity_key,
    PqxdhEd25519EufCma.attachSignature (setup.joint.sign owner.beacon.identity (absBytes out.message.prekey)) (absBytes out.message.prekey),
    PqxdhEd25519EufCma.attachSignature (setup.joint.sign owner.beacon.identity (absBytes out.message.one_time_key)) (absBytes out.message.one_time_key),
    PqxdhEd25519EufCma.attachSignature (setup.joint.sign owner.beacon.identity (absBytes out.message.pq_key)) (absBytes out.message.pq_key)⟩

/-- The actual native prepared computation uses the extracted unsigned fields as the writer candidate and the extracted control on success; literal serialization failure retains the original owner. -/
theorem native_prepared_core (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : Owner KemSK) (generated : Option PqxdhJointGapDh.ScalarBytes)
    (prepared : PqxdhBeaconPhase1Publication.Prepared PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (chosen : PqxdhBeaconPhase1Publication.prepare owner generated = some prepared) :
    ∃ out : pqxdh.BeaconStart,
      pqxdh.beacon_start prepared.control (inputs setup owner prepared) (coins setup prepared) = ok out ∧
      simulateQ (PqxdhRegistrationSchedule.bundleCallbacks setup codec owner.beacon.identity)
        (PqxdhLivePhase1Bundle.afterGenerated (PqxdhRegistrationSchedule.projection setup index) generated owner) =
        pure (match codec.write1 (signedOutput setup owner out) with
          | none => (none, owner)
          | some bytes => (some bytes, { owner with beacon := { owner.beacon with
              phase := .initSent out.state prepared.prekey prepared.oneTime prepared.kem } })) := by
  obtain ⟨out, built, control, identity, prekey, oneTime, pq⟩ := core_build setup owner prepared
  refine ⟨out, built, ?_⟩
  simp only [PqxdhBoundaryPhase1Native.native_prepared, PqxdhBoundaryPhase1Native.preparedResult, chosen, signedOutput, identity, prekey, oneTime, pq, control]
  rfl

/-- Literal extracted builder, exact attached buffers, optional writer and returned extracted control form the complete prepared result. -/
def corePreparedResult (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (owner : Owner KemSK) :
    Option Pqxdh.Bytes × Owner KemSK :=
  match PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => (none, owner)
  | some prepared =>
      match pqxdh.beacon_start prepared.control (inputs setup owner prepared) (coins setup prepared) with
      | .ok out => match codec.write1 (signedOutput setup owner out) with
          | none => (none, owner)
          | some bytes => (some bytes, { owner with beacon := { owner.beacon with
              phase := .initSent out.state prepared.prekey prepared.oneTime prepared.kem } })
      | _ => (none, owner)

/-- Every native prepared result equals the literal extracted-builder execution, including all optional preparation and writer failures. -/
theorem prepared_result_core (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (generated : Option PqxdhJointGapDh.ScalarBytes) (owner : Owner KemSK) :
    PqxdhBoundaryPhase1Native.preparedResult setup codec generated owner =
      corePreparedResult setup codec generated owner := by
  cases chosen : PqxdhBeaconPhase1Publication.prepare owner generated with
  | none => simp only [PqxdhBoundaryPhase1Native.preparedResult, corePreparedResult, chosen]
  | some prepared =>
      obtain ⟨out, built, control, identity, prekey, oneTime, pq⟩ := core_build setup owner prepared
      simp only [PqxdhBoundaryPhase1Native.preparedResult, corePreparedResult, chosen, built, signedOutput, identity, prekey, oneTime, pq, control]
      rfl

/-- The source draws local Fresh coins before the extracted builder and retains the actual writer/control result. -/
def coreOwnerProgram (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Owner KemSK) : ProbComp (Option Pqxdh.Bytes × Owner KemSK) :=
  match owner.beacon.phase with
  | .fresh _ _ _ => (fun generated => corePreparedResult setup codec (some generated) owner) <$>
      PqxdhJointGapDh.sampleScalar
  | .freshWithCoins _ _ _ _ => pure (corePreparedResult setup codec none owner)
  | _ => pure (none, owner)

/-- The same complete native owner execution is obtained by literally running the extracted unsigned builder. -/
theorem owner_core (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : Owner KemSK) :
    PqxdhBoundaryPhase1Native.ownerProgram setup codec index owner = coreOwnerProgram setup codec owner := by
  simp only [PqxdhBoundaryPhase1Native.owner_source_order, prepared_result_core, coreOwnerProgram]
  cases owner.beacon.phase <;> rfl

/-- CE's actual full-state bundle handler consumes the extracted unsigned builder, original attached signatures, literal optional writer and exact reinstallation before any continuation. -/
theorem native_core_continuation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (state : PqxdhDeploymentNative.State KemSK)
    (next : Option Pqxdh.Bytes × PqxdhDeploymentNative.State KemSK → ProbComp Result) :
    (PqxdhDeploymentNative.handler setup codec checks route serverSeed (.inr (.bundle index))).run state >>= next =
      match state.native.owners[index]? with
      | none => next (none, state)
      | some owner => coreOwnerProgram setup codec owner >>= fun result =>
          next (result.1, { state with native := { state.native with owners := state.native.owners.set index result.2 } }) := by
  rw [PqxdhBoundaryPhase1Native.native_bundle]
  cases state.native.owners[index]? <;> simp only [owner_core, ← bind_pure_comp, bind_assoc, pure_bind]

end BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.array32_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.array32_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.array1184_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.array1184_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.core_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.core_build

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.native_prepared_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.native_prepared_core

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.prepared_result_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.prepared_result_core

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.owner_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.owner_core

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.native_core_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryPhase1Buffers.native_core_continuation
