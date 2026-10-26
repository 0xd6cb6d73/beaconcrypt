import BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix
import BeaconcryptCore.Computational.PqxdhGeneratedRootSource

/-!
The concrete generated prefix keeps the actual identity/prekey/one-time sampler, original three signatures, optional publication and whole ordinary scheduler inside one explicit hash program. The selected KEM secret remains confined to its local interpreter. Source state is reconstructed from the reached ROM only at the semantic boundary; the executable local state cannot inspect or install that cache.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca
open PqxdhPrivatePhase1Prefix PqxdhPrivateCandidateAcceptance PqxdhJointPhase1Reports
open PqxdhGeneratedPhase1Prefix PqxdhInitializerSecrecy CtxRomAuth AdaptiveCtxSharedHash
open PqxdhJointPhase1AcceptanceComposition PqxdhJointPhase1SourceWriter
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

abbrev LocalOutput := Outcome (Retained setup Unit (program.Selection ×
  PqxdhOrdinarySharedScheduler.Local M P I (DhPair setup) K A S (B + 1) 1))

/-- Reconstruct the actual complete retained prefix only under the source interpreter. -/
def restore (output : LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) (cache : CtxRO.QueryCache) :
    PqxdhPrivateRootSource.Prepared setup
      (program.Selection × State setup M P I K A S (B + 1)) :=
  let state := PqxdhPhase2OldSource.unpackState (PqxdhOrdinarySharedScheduler.attach output.context.selection.2 cache)
  (⟨⟨output.context.index, output.context.publicIdentity, output.context.generated, output.context.bundle,
      (output.context.selection.1, state.1)⟩, output.candidate, output.accepted⟩, state.2)

/-- Identity and private prekey/one-time generation retain source order, followed by all original signing and native scheduling. -/
noncomputable def run (target : TargetKemPublicKey) : OracleComp HashSpec (LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) := do
  let seed ← simulateQ RawCtxSelectiveSharedRom.coins sampleSeed
  let before ← simulateQ RawCtxSelectiveSharedRom.coins
    (simulateQ (kemAmbientImpl baseImpl) (setup.prekey (primitives.publicKeys seed).ed25519))
  let after ← simulateQ RawCtxSelectiveSharedRom.coins
    (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime (primitives.publicKeys seed).ed25519 before target))
  let generated : Generated setup Unit := ⟨before, target, (), after⟩
  let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
  let bundle := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
  let initial := singletonState primitives 1 seed
  let selected ← PqxdhGeneratedSharedPrefix.run setup env callbacks program attachedVerify primitives 1 baseImpl kem secret
    0 (primitives.publicKeys seed) generated (transcript bundle material.context)
    (signedGlobalState primitives seed 1 0 material.keyTuple initial.1, signedState primitives seed 0 material.keyTuple initial.2)
  pure ⟨⟨0, primitives.publicKeys seed, generated, bundle, selected.2⟩,
    ⟨0, selected.1⟩, sourceAccept attachedVerify selected.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full generated-source prefix, including all original logs, cache and optional replies, equals its explicit same-ROM program. -/
theorem source (target : TargetKemPublicKey) (cache : CtxRO.QueryCache) :
    (fun result => restore setup program result.1 result.2) <$>
      (simulateQ hashImpl (PqxdhBorrowedSharedPrefix.run setup env callbacks program attachedVerify primitives baseImpl kem secret target)).run cache =
    evalKem baseImpl kem secret (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup
      (PqxdhPhase2GeneratedDriver.driver (PqxdhGeneratedSharedPrefix.environment setup env callbacks cache) program) target) := by
  simp only [PqxdhBorrowedSharedPrefix.run, simulateQ_bind, StateT.run_bind, map_bind,
    RawCtxSelectiveSharedRom.coins_complete, bind_map_left,
    PqxdhGeneratedRootSource.borrowedPrefix_evaluated, PqxdhPhase2GeneratedDriver.driver_private]
  apply bind_congr
  intro seed
  apply bind_congr
  intro before
  apply bind_congr
  intro after
  simp only [simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp, evalKem, simulateQ_map, Functor.map_map]
  let generated : Generated setup Unit := ⟨before, target, (), after⟩
  let material := publicMaterial setup (primitives.publicKeys seed).ed25519 generated
  let signed := signedCandidate primitives seed (primitives.publicKeys seed).ed25519 material.keyTuple
  have original := PqxdhGeneratedSharedPrefix.source setup env callbacks program attachedVerify primitives 1 baseImpl kem secret
    0 (primitives.publicKeys seed) generated (transcript signed material.context)
    (signedGlobalState primitives seed 1 0 material.keyTuple (singletonState primitives 1 seed).1,
      signedState primitives seed 0 material.keyTuple (singletonState primitives 1 seed).2) cache
  have mapped := congrArg (fun work =>
    (fun (selected : Phase1Candidate × program.Selection × State setup M P I K (A × BareState 1) S (B + 1)) =>
      let result := PqxdhPhase2GeneratedDriver.unpackSelection selected
      ((⟨⟨0, primitives.publicKeys seed, generated, signed, result.1.2⟩,
        ⟨0, result.1.1⟩, sourceAccept attachedVerify result.1.1⟩, result.2) :
        PqxdhPrivateRootSource.Prepared setup (program.Selection × State setup M P I K A S (B + 1)))) <$> work) original
  simpa only [Functor.map_map, restore, PqxdhPhase2GeneratedDriver.unpackSelection,
    evalKem, generated, material, signed] using mapped

end BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix.source
