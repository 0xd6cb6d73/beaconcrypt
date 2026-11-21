-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicStartup
import BeaconcryptCore.Computational.RegistrationNativeKeyServiceBound

/-! The complete concrete native reference frontend is also an executable client of the before-prepare key phases. Preparation returns only a public message reference; the actual root and PRK stay in the private phase interpreter. Every ordinary World/KEM/ML computation remains the same local algorithm. Both known and protected complete108 replies initially use the actual known-kernel native continuation; hiding its uniform seed is the subsequent proved paired-service rewrite, which must account for repeated-role aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicPhases
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKeyPhases (Spec)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

/-- Only the uniform branch is used by the concrete local World/primitive components. Root requests are replaced separately below. -/
def localCoins (hmac : PqxdhSecretInputKdf.HmacSha512) :
    QueryImpl RegistrationNativeRelatedRoot.RootSpec (OracleComp Spec)
  | .inl coin => Spec.query (.inl coin)
  | .inr (.sign _) => pure (List.Vector.replicate 64 0)
  | .inr (.publicHmac key message) => pure (hmac.eval key message)
  | .inr (.derive _) => pure none

def localWork {Result : Type} (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Result) :
    StateT (RegistrationNativePublicInterpreter.State n KemSK) (OracleComp Spec) Result :=
  fun before => simulateQ (localCoins hmac) (work.run before)

def choice : RegistrationNativeKeyPhases.Value → RegistrationNativePairedChoice.Choice n
  | .known output | .hidden output => .known output

noncomputable def handler (setup : Setup base KemSK) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (RegistrationNativePublicInterpreter.State n KemSK) (OracleComp Spec))
  | .inl (.inl message) => do
      let prepared ← StateT.lift (Spec.query (.inr (.prepare message)))
      modify fun before => { before with roots := Function.update before.roots message (prepared.map (fun _ => RegistrationBoundKeySchedule.zero)) }
      pure prepared
  | .inl (.inr (.inl (.inl message))) => do
      let before ← get
      if (before.roots message).isSome then
        StateT.lift (Option.map choice <$> (Spec.query (.inr (.demand message)) : OracleComp Spec _))
      else pure none
  | .inl (.inr (.inl (.inr query))) => localWork setup.hmac (RegistrationNativePublicInterpreter.common setup wire sign query)
  | .inl (.inr (.inr query)) => localWork setup.hmac (RegistrationNativePublicInterpreter.routedKem setup query)
  | .inr query => localWork setup.hmac (RegistrationNativePublicInterpreter.world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))

/-- Concrete World and ordinary primitive work forward precisely its actual coins; no fallback root/signing response is used. -/
theorem local_world (hmac : PqxdhSecretInputKdf.HmacSha512) {Result : Type}
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Result)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    (localWork hmac (RegistrationNativePublicInterpreter.world work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        simulateQ (fun coin => (Spec.query (.inl coin) : OracleComp Spec _)) (work.run before.world) := by
  simp only [localWork, RegistrationNativePublicInterpreter.world, StateT.run,
    simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

/-- Complete ordinary native execution, including its literal original secrecy draws, is a root-free and PRK-free client of the phase service. -/
noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicInterpreter.State n KemSK) :
    OracleComp Spec (((Value × RegistrationNativeLedger.State) × RegistrationNativePublicFrontend.State source) ×
      RegistrationNativePublicInterpreter.State n KemSK) :=
  (simulateQ (handler setup wire route (RegistrationNativeMldsa.owned source credential))
    (RegistrationNativePublicFrontend.run setup checks wire source (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work frontend)).run before

noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp Spec Bool := do
  let initialized ← (localWork setup.hmac
    (RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity)).run
      RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure false
  | some started => do
      let observed ← run setup checks wire route source started.credential selectedOwner selectedAccept publicValue.prekey serverKeyId bounds .P
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend initialized.2
      pure (RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim
        (observed.1.1.1, (observed.1.1.2, observed.1.2)))

/-- The same complete concrete phase client has the five-loss computational uniform108 bound. The scheduling cap is explicit until its native command-budget derivation is applied. -/
theorem key_distance (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (count : Nat)
    (bounded : (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue).IsQueryBoundP
      RegistrationNativeKeyBounds.IsDemand count) :
    (RegistrationNativeKeyServiceBound.g1 setup.source setup.hmac
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (fun bytes => decide (RegistrationNativeRelatedFamily.Protected
        (setup.joint.staticDh seed (setup.dh.publicKey scalar)) bytes))
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue)).boolDistance
      (RegistrationNativeKeyServiceBound.g2 setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (fun bytes => decide (RegistrationNativeRelatedFamily.Protected
          (setup.joint.staticDh seed (setup.dh.publicKey scalar)) bytes))
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue)) ≤
    ∑ index ∈ Finset.range count, RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
      (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
        (RegistrationNativeKeyCompiler.client setup.source
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (fun bytes => decide (RegistrationNativeRelatedFamily.Protected
            (setup.joint.staticDh seed (setup.dh.publicKey scalar)) bytes))
          (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue)
          RegistrationNativeKeyPhases.emptyMeta) index) :=
  RegistrationNativeKeyServiceBound.bound setup.source setup.hmac correct _ _ _ count bounded

end BeaconcryptCore.Computational.RegistrationNativePublicPhases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicPhases.key_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicPhases.key_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicPhases.local_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicPhases.local_world
