-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFullTotal
import BeaconcryptCore.Computational.RegistrationNativeKemMixture

/-! Actual private native startup is sampled inside the single ordinary selected-KEM adversary. Its stored bootstrap has no private KEM pool. Complete original raw ledger decisions and inactive dummy-ciphertext substitutions remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemStartupGame
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open PqxdhKemIndCca
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

structure Bootstrap (n : Nat) (source : RegistrationNativeMldsa.Source) where
  created : PqxdhLiveServerConstruction.Created Unit
  credential : RegistrationNativeMldsa.Credential source
  state : RegistrationNativeKemServerState.State n source

def ofInitial (source : RegistrationNativeMldsa.Source) (initial : RegistrationNativeExperiment.Initial n KemSK source) :
    Bootstrap n source := ⟨initial.created, initial.credential, RegistrationNativeKemServerState.project initial.state⟩

def Bootstrap.public {source : RegistrationNativeMldsa.Source} (boot : Bootstrap n source) :
    RegistrationNativeExperiment.Public :=
  ⟨boot.created.publicIdentity, boot.credential.publicKey, boot.created.server.server.metadata.sender⟩

def silent (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) : OneKeyAdversary kem where
  Context := Unit
  preChallenge _ := pure ()
  postChallenge _ _ := pure false

noncomputable def family (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) : Option (Bootstrap n source) → OneKeyAdversary setup.kem
  | none => silent setup.kem
  | some boot => RegistrationNativeKemTotalGame.adversary setup.baseImpl setup.kem
      (RegistrationNativeKemParsedRouting.other setup checks wire route representation boot.created boot.credential)
      (pure boot.state) (RegistrationNativeKemFullTotal.client setup checks wire boot.created.server.server.metadata.sender
        bounds mode (work boot.public) parsed decision) budget.create selected index

noncomputable def sample (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) :
    ProbComp (Option (Bootstrap n source)) :=
  Option.map (ofInitial source) <$> RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId

noncomputable def adversary (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) : OneKeyAdversary setup.kem :=
  RegistrationNativeKemMixture.adversary setup.kem (sample (n := n) setup source ensureInit identityIndex serverKeyId)
    (family (n := n) setup checks wire route representation source bounds mode work budget parsed selected index decision)

noncomputable def hybrid (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool) : ProbComp Bool :=
  RegistrationNativeKemMixture.branch setup.baseImpl setup.kem
    (adversary (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work
      budget parsed selected index decision) real

/-- Actual startup is inside the ordinary KEM adversary, with exactly its original failure and successful bootstrap probabilities. -/
theorem branch_startup (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool) :
    EvalDistEq (hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work
      budget parsed selected index decision real)
      (do let initial ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
          RegistrationNativeKemMixture.branch setup.baseImpl setup.kem
            (family (n := n) setup checks wire route representation source bounds mode work budget parsed selected index decision
              (initial.map (ofInitial source))) real) := by
  simpa only [hybrid, adversary, sample, bind_map_left] using RegistrationNativeKemMixture.branch_mixture
    setup.baseImpl setup.kem (sample (n := n) setup source ensureInit identityIndex serverKeyId)
    (family setup checks wire route representation source bounds mode work budget parsed selected index decision) real

end BeaconcryptCore.Computational.RegistrationNativeKemStartupGame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStartupGame.branch_startup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStartupGame.branch_startup
