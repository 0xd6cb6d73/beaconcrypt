-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeKemBirthRun
import BeaconcryptCore.Computational.RegistrationNativeKemPublicTarget
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! Original full-ledger native publication identifies the exact generated classical identity of the final retained owner. The argument is independent of the selected accept's timing and preserves all public-key aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeInterface (Entry)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode Handle)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}

private theorem bundle_mem (transcript : List PqxdhDeploymentInterface.Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf transcript owner = some raw) :
    (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry) ∈ transcript := by
  obtain ⟨entry, member, value⟩ := List.exists_of_findSome?_eq_some found
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases value
  · cases command with
    | bundle index =>
        cases reply with
        | none => cases value
        | some encoded =>
            simp only at value
            split at value
            · rename_i same
              simp only [Option.some.injEq] at value
              subst same value
              exact member
            · cases value
    | _ => cases value
  · cases value

private theorem erased_bundle (entry : Entry) (owner : Nat) (raw : Pqxdh.Bytes)
    (same : entry.erase = (⟨.inl (.inr (.bundle owner)), some raw⟩ : PqxdhDeploymentInterface.Entry)) :
    RegistrationNativeIdentityPublicationTrace.publication entry = some (owner, raw) := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases same
  · cases command <;> cases same
    rfl
  · cases same

/-- A successful bundle found by the original designation has the exact current source owner and native PQ bytes. -/
theorem original_bundle (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (index : Nat) (raw : Pqxdh.Bytes)
    (found : PqxdhDeploymentTranscript.bundleOf result.2.1.ledger.transcript index = some raw) :
    ∃ owner packet, result.2.2.beacons[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      PqxdhEd25519EufCma.parseIdentity (PqxdhRefinement.absBytes packet.identity_key) = some (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  have observed := RegistrationNativeIdentityPublicationTrace.run_holds setup checks wire route representation created credential readback bounds mode work before result supported
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) mode work before result supported
  have member := bundle_mem result.2.1.ledger.transcript index raw found
  rw [projected] at member
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  exact observed entry nativeMember index raw (erased_bundle entry index raw erased)


/-- Original broad publication eligibility refers to the final owner's generated tagged classical identity, even when that owner was created after the accepted packet. -/
theorem publishes_identity (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before))
    (accepted : PqxdhEd25519EufCma.Phase1Candidate) (pqKey : PqxdhKemIndCca.MlKem768PublicKey) (index : Nat)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (found : result.2.2.beacons[index]? = some owner)
    (published : PqxdhDeploymentTranscript.Publishes (RegistrationNativeWire.ledgerCodec wire) result.2.1.ledger.transcript accepted pqKey index) :
    accepted.identityKey = PqxdhEd25519EufCma.encodedIdentity (setup.joint.publicKeys owner.identitySeed).ed25519 := by
  obtain ⟨packet, publishedFound, identityMatches, _pqMatches⟩ := published
  obtain ⟨raw, bundled, packetRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  obtain ⟨actualOwner, nativePacket, ownerAt, parsed, identity⟩ :=
    original_bundle setup checks wire route representation created credential readback bounds mode work before result supported index raw bundled
  have sameOwner : actualOwner = owner := Option.some.inj (ownerAt.symm.trans found)
  subst actualOwner
  rw [RegistrationNativeKemPublicTarget.candidate_read wire raw nativePacket parsed] at packetRead
  have samePacket := Option.some.inj packetRead
  rw [← samePacket] at identityMatches
  have canonical := (PqxdhEd25519EufCma.parseIdentity_eq_some_iff _ _).mp identity
  exact identityMatches.symm.trans canonical

end BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace.original_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace.original_bundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace.publishes_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTargetTrace.publishes_identity
