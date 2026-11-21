-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityWorld

/-! Native signing and converted-static-DH execute the ordinary joint service at the exact generated handle. The source retains the attempted signing service before attached-buffer packing, and the outgoing owner history records that signature even if packing subsequently fails. All unrelated World fields remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity
open RegistrationNativeIdentityWorld (State implementation)
open RegistrationNativeIdentityFrontend (Ambient Owner)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual native signing source retains the attempted indexed request and signature before any callback buffer conversion. -/
theorem sign_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeIdentityInterface.Credential) (seed : IdentitySeed)
    (message : Pqxdh.Bytes) (before : State n KemSK)
    (found : before.identities.seeds[credential.handle]? = some seed) :
    (simulateQ (implementation (mlSource := source) setup checks representation created)
      (RegistrationNativeIdentityInterface.sign (Ambient n KemSK) credential message)).run before =
      pure (some (setup.joint.sign seed message), { before with
        identities := PqxdhDynamicIdentityPool.record (.inr (.service credential.handle (.sign message)))
          (some (setup.joint.sign seed message)) before.identities }) := by
  simp only [RegistrationNativeIdentityInterface.sign, simulateQ_spec_query]
  rw [RegistrationNativeIdentityWorld.service_source]
  simp only [found, Option.map_some, primitiveReply]

/-- Static-DH uses the same private generated seed and keeps optional source rejection without publishing its converted secret. -/
theorem dh_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeIdentityInterface.Credential) (seed : IdentitySeed)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (before : State n KemSK)
    (found : before.identities.seeds[credential.handle]? = some seed) :
    (simulateQ (implementation (mlSource := source) setup checks representation created)
      (RegistrationNativeIdentityCallbacks.dh (Ambient n KemSK) credential peer)).run before =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer)).map PqxdhRootTableInitialization.rootArray),
        { before with
          identities := PqxdhDynamicIdentityPool.record
            (.inr (.service credential.handle (.staticDh (PqxdhPhase2GapDhSource.peer peer))))
            (some (setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer peer))) before.identities }) := by
  simp only [RegistrationNativeIdentityCallbacks.dh, bind_pure_comp,
    RegistrationNativeIdentityInterface.staticDh, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [RegistrationNativeIdentityWorld.service_source]
  simp only [found, Option.map_some, primitiveReply, map_pure]
  rfl

def appendHistory (owners : RegistrationNativeIdentityFrontend.State source) (index : Nat)
    (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    RegistrationNativeIdentityFrontend.State source :=
  match owners[index]? with
  | none => owners
  | some current => owners.set index { current with edHistory := current.edHistory ++ [.signed message signature] }

/-- A successful indexed signature is recorded in both the joint-service transcript and the current owner history before packing, including the path where native packing returns none. -/
theorem outgoing_ed_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (request : registration.Ed25519SigningRequest) (seed : IdentitySeed)
    (owners : RegistrationNativeIdentityFrontend.State source) (env : EnvState Auxiliary) (before : State n KemSK)
    (found : before.identities.seeds[owner.identity.handle]? = some seed)
    (matched : request.public_key = PqxdhRootTableInitialization.rootArray owner.identity.publicIdentity.ed25519) :
    (simulateQ (implementation (mlSource := source) setup checks representation created)
      (((RegistrationNativeIdentityFrontend.outgoing setup source index owner (.inr request)).run owners).run env)).run before =
      (let message := TranscriptAuthParts.absSlice request.message
       let signature := setup.joint.sign seed message
       pure (((RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ message)),
          appendHistory owners index message signature), env),
        { before with
          identities := PqxdhDynamicIdentityPool.record
            (.inr (.service owner.identity.handle (.sign message))) (some signature) before.identities })) := by
  classical
  simp only [RegistrationNativeIdentityFrontend.outgoing, ite_eq_left matched,
    StateT.run_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, bind_map_left]
  rw [sign_source setup checks representation created owner.identity seed _ before found]
  simp only [pure_bind, RegistrationNativeIdentityFrontend.logEd, StateT.run_modify,
    StateT.run_map, StateT.run_pure, simulateQ_pure, map_pure, appendHistory]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.sign_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.sign_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.dh_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.outgoing_ed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityWorldServices.outgoing_ed_source
