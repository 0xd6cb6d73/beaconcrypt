-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInterpreter
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationNativeSelectedEvents

/-! The complete related-root reference client performs actual runtime initialization and local ML generation, initializes one World with the challenge's public Server identity, and runs the selected owner share of the original broad native CE-APP observation. Its dummy constructor identity draw is private local randomness, discarded before the public API starts. The source-to-reference sampling interchange remains a separate proof obligation; this module does not rename the reference probability as the source probability. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicStartup
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationNativePublicInterpreter (State M world)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

structure Started (source : RegistrationNativeMldsa.Source) where
  credential : RegistrationNativeMldsa.Credential source
  frontend : RegistrationNativePublicFrontend.State source

/-- Actual dummy constructor draws retain their normal counted position; only their unused public identity is replaced by the challenge public identity. -/
noncomputable def start (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity) : M n KemSK (Option (Started source)) := do
  let constructed ← world (PqxdhRecordLiftWorld.sampled
    ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()))
  match constructed.1 with
  | none => pure none
  | some _ =>
    let generated ← world (PqxdhRecordLiftWorld.sampled (RegistrationNativeMldsa.generate source))
    match generated with
    | none => pure none
    | some credential =>
      let created := RegistrationServerStartup.publicCreated identity identityIndex serverKeyId
      let _ ← world (PqxdhRecordLiftWorld.initializeServer created)
      let digest ← RegistrationNativePublicInterpreter.effect (.inr (.hash (absBytes credential.publicKey)))
      let pin : session.ServerAuthenticationPin :=
        ⟨⟨PqxdhRootTableInitialization.rootArray identity.ed25519, serverKeyId⟩,
          credential.publicKey, RegistrationAuthenticationShared.digestArray digest⟩
      let frontend : RegistrationNativePublicFrontend.State source :=
        ⟨RegistrationServerMaterialFrontend.initial created.control pin, [],
          ⟨RegistrationServerRoleBackend.empty, [], [], []⟩, 0⟩
      pure (some ⟨credential, frontend⟩)

/-- The executable client contains both roles, all ordinary sessions and the literal original hidden-bit/fresh-message ledger. -/
noncomputable def client (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (publicValue : PqxdhJointGapDh.PublicChallenge) : OracleComp RootSpec Bool := do
  let initialized ← (start (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
    RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure false
  | some started => do
      let observed ← RegistrationNativePublicInterpreter.run setup checks wire route source started.credential
        selectedOwner selectedAccept publicValue.prekey serverKeyId bounds .P
        (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend initialized.2
      pure (RegistrationNativeSelectedEvents.ceAppOwnerEvent setup.source.crypto wire serverKeyId budget selectedOwner claim
        (observed.1.1.1, (observed.1.1.2, observed.1.2)))

/-- The complete reference profile pays one explicitly broader native related-input advantage. This theorem does not supply the distinct source-sampling or repeated-role-alias bridges. -/
theorem family_distance (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (budget : PqxdhDeploymentInterface.Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value) :
    (RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary)).boolDistance
      (RegistrationNativeRelatedRoot.idealRootGame setup.hmac setup.joint setup.dh
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary)) =
    RegistrationNativeRelatedFamily.advantage setup.hmac setup.joint setup.dh
      (fun publicValue => simulateQ RegistrationNativeRelatedRoot.reduction
        (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds budget claim adversary publicValue)) :=
  RegistrationNativeRelatedRoot.advantage_exact setup.source setup.hmac correct setup.joint setup.dh _

end BeaconcryptCore.Computational.RegistrationNativePublicStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicStartup.family_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicStartup.family_distance
