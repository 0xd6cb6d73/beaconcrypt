import BeaconcryptCore.Computational.PqxdhPhase2SourceScheduler
import BeaconcryptCore.Computational.PqxdhGeneratedBeaconSelector

/-!
The generated private driver extends the actual optional Phase1 publication with the full source scheduler, including native Beacon finish. The environment, prior owners and local callback implementation are fixed before target generation. The driver receives only the existing secret-erased generated representation; selected KEM decapsulation remains in the later ordinary CCA interpreter. Complete public replies, live roles, private state and histories are retained.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedPhase1Prefix PqxdhGeneratedBeaconState
open PqxdhGeneratedBeaconSelector (Published bundle)
open PqxdhPhase1AcceptanceOracle (BareState)
open PqxdhPrivateSourceCoins PqxdhPrivatePhase1Prefix PqxdhPrivateRootSource
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition PqxdhJointPhase1Reports
open PqxdhPhase2OldSource (packState unpackState)
variable {ι : Type} {baseSpec : OracleSpec ι} {M P I K X Response A : Type} {S B : Nat}

structure Program (baseSpec : OracleSpec ι) (Context : Type) (S B : Nat) where
  Selection : Type
  main : Option (Published Context) →
    OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) (Phase1Candidate × Selection)

structure Environment (setup : StatefulPhase1Setup baseSpec) (M P I K X Response A : Type) (S B : Nat)
    extends PqxdhGeneratedBeaconSelector.Environment setup M P I K A S B where
  localImpl : QueryImpl (PqxdhPhase2SourceAux.LocalSpec I (DhPair setup) K X Response) (StateT A ProbComp)

/-- The actual optional writer and installation precede every request; no fresh identity seed, target KEM secret or borrowed identity state is a driver argument. -/
noncomputable def driver {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1)) : Driver setup where
  State := program.Selection × State setup M P I K A S (B + 1)
  main index publicIdentity generated transcript := do
    let started ← PqxdhProtocolSelector.coins
      (start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial)
    let selected ← (simulateQ
      (PqxdhPhase2SourceScheduler.compiler env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
      (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))).run started.2
    pure (selected.1.1, (selected.1.2, selected.2))

/-- Later CCA interpretation receives only the original public key handle and current identity state; the selected secret remains confined to its interpreter. -/
noncomputable def ordinaryRun {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) :
    OracleComp (PqxdhKemIndCca.MlKemCCAOracleSpec baseSpec)
      (Phase1Candidate × program.Selection × State setup M P I K (A × BareState count) S (B + 1)) := do
  let started ← ccaCoins
    (start setup env.phase1Writer index publicIdentity generated env.binding (bundle transcript) env.initial)
  let selected ← (simulateQ
    (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives count env.source env.recordWriter
      env.senderId env.route env.decode env.localImpl)
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))).run (packState started.2 identities)
  pure (selected.1.1, (selected.1.2, selected.2))

/-- This literal inverse recovers the original private-prefix result representation, with every field retained. -/
def unpackSelection {setup : StatefulPhase1Setup baseSpec} {Selection : Type} {count : Nat}
    (result : Phase1Candidate × Selection × State setup M P I K (A × BareState count) S B) :
    (Phase1Candidate × Selection × State setup M P I K A S B) × BareState count :=
  ((result.1, (result.2.1, (unpackState result.2.2).1)), (unpackState result.2.2).2)

/-- The complete borrowed execution installs the actually generated owner before the adaptive ordinary schedule, preserving the original optional writer outcome. -/
theorem driver_borrowed {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) :
    (fun result => (result.1.1, (result.1.2.1, packState result.1.2.2 result.2))) <$>
      (simulateQ (borrowedSelector attachedVerify primitives count)
        ((driver env program).main index publicIdentity generated transcript)).run identities =
      ordinaryRun env program attachedVerify primitives count index publicIdentity generated transcript identities := by
  simp only [driver, ordinaryRun, simulateQ_bind, StateT.run_bind, PqxdhPhase2SourceAux.borrowed_coins,
    ccaCoins, simulateQ_map, bind_map_left, map_bind, bind_pure_comp]
  apply bind_congr
  intro started
  have complete := PqxdhPhase2SourceScheduler.compiler_complete attachedVerify primitives count
    env.source env.recordWriter env.senderId env.route env.decode env.localImpl
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩))) started.2 identities
  have reordered := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work) complete
  simpa only [StateT.run_map, Functor.map_map] using reordered

/-- Evaluating the ordinary CCA interpretation yields the exact original private source execution, including every optional reply and both complete private states. -/
theorem driver_private {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) :
    (simulateQ (PqxdhPrivateSourceCoins.privateImpl attachedVerify primitives count)
      (simulateQ (localSelector baseImpl kem secret)
        ((driver env program).main index publicIdentity generated transcript))).run identities =
      evalKem baseImpl kem secret (unpackSelection <$>
        ordinaryRun env program attachedVerify primitives count index publicIdentity generated transcript identities) := by
  rw [localSelector_complete]
  apply congrArg (evalKem baseImpl kem secret)
  have original := congrArg (fun work => unpackSelection <$> work)
    (driver_borrowed env program attachedVerify primitives count index publicIdentity generated transcript identities)
  simp only [Functor.map_map, unpackSelection, PqxdhPhase2OldSource.unpackState_packState,
    Prod.mk.eta] at original
  change (id <$> _) = _ at original
  rw [id_map] at original
  exact original

/-- Source identity, prekey, selected KEM and one-time generation, the three original signatures, actual optional publication, full live scheduler and all candidate acceptance branches occur in their original order. -/
theorem program_complete {KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : Environment setup M P I K X Response A S B) (program : Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    privateRun attachedVerify primitives count
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env program)) = (do
      let seed ← sampleSeed
      let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
      let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
      let signed := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
      let prior := singletonState primitives count seed
      let selected ← evalKem baseImpl kem generated.secret (unpackSelection <$>
        ordinaryRun env program attachedVerify primitives count 0 (primitives.publicKeys seed)
          (eraseGenerated generated) (transcript signed material.context)
          (signedGlobalState primitives seed count 0 material.keyTuple prior.1,
           signedState primitives seed 0 material.keyTuple prior.2))
      pure (some ⟨⟨0, primitives.publicKeys seed, generated, signed, selected.1.2⟩,
        ⟨0, selected.1.1⟩, sourceAccept attachedVerify selected.1.1⟩, selected.2)) := by
  rw [PqxdhGeneratedPhase1Prefix.program_complete]
  simp only [driver_private]
  rfl

end BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.driver_borrowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.driver_borrowed

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.driver_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.driver_private

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.program_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver.program_complete
