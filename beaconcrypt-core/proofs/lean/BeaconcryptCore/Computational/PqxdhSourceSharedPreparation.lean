import BeaconcryptCore.Computational.PqxdhCommonSharedDispatch

/-!
The complete original generated-source preparation executes its identity/prekey/one-time prefix, optional publication, arbitrary native schedule and actual candidate admission inside one shared-ROM program. The initial cache is supplied only to its enclosing interpreter; executable local state never installs a sampled cache. The locally generated KEM secret belongs to this interpreter, while no selected message key is an argument to the program.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.PqxdhSourceSharedPreparation
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))

/-- The source boundary uses the actual local callbacks and the cache reached by the enclosing ROM interpreter. -/
def environment (cache : CtxRO.QueryCache) : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B :=
  { PqxdhPreparedSharedPrefix.environment env callbacks with initial := PqxdhGeneratedSharedPrefix.withCache setup env.initial cache }

abbrev LocalOutput := PqxdhCommonSharedDispatch.Mode
  (PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program)

/-- Every actual branch is executed after the full original generated prefix. -/
noncomputable def run (secret : KemSK) (target : TargetKemPublicKey) : OracleComp HashSpec (LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) := do
  let generated ← PqxdhBorrowedSharedPrefix.run setup env.toDriverEnvironment callbacks program attachedVerify primitives baseImpl kem secret target
  PqxdhCommonSharedDispatch.dispatch setup env callbacks program post attachedVerify primitives baseImpl kem secret generated

set_option backward.isDefEq.respectTransparency false in
/-- The complete protocol preparation equals the same-ROM program, including every ineligible/common outcome and the complete retained pending source state. -/
theorem source (secret : KemSK) (target : TargetKemPublicKey) (cache : CtxRO.QueryCache) :
    (fun result => PqxdhCommonSharedDispatch.restoreMode setup program result.1 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem secret target)).run cache =
    evalKem baseImpl kem secret ((PqxdhAuthenticatedRootExperiment.protocol
      (environment setup env callbacks cache) kem attachedVerify primitives program post).prepare target) := by
  simp only [run, simulateQ_bind, StateT.run_bind, map_bind,
    PqxdhAuthenticatedRootExperiment.protocol, evalKem_bind]
  have original := PqxdhBorrowedSharedPrefix.source setup env.toDriverEnvironment callbacks program attachedVerify primitives baseImpl kem secret target cache
  change _ = do
    let value ← evalKem baseImpl kem secret (PqxdhGeneratedRootSource.borrowedPrefix attachedVerify primitives setup
      (PqxdhPhase2GeneratedDriver.driver (PqxdhGeneratedSharedPrefix.environment setup env.toDriverEnvironment callbacks cache) program) target)
    evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.dispatch kem env.parameters attachedVerify primitives setup
      (PqxdhAuthenticatedRootExperiment.commonObserver (PqxdhPreparedSharedPrefix.environment env callbacks) program post) value)
  rw [← original]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  exact PqxdhCommonSharedDispatch.dispatch_source setup env callbacks program post attachedVerify primitives baseImpl kem secret result.1 result.2

/-- Private reduction packet; the KEM key stays in this interpreter and is never a protocol reply. -/
structure Packet (Output Secret : Type) where
  publicKey : TargetKemPublicKey
  secretKey : Secret
  state : Output
  ciphertext : MlKem768Ciphertext

/-- Both the actual KEM generation and outer encapsulation occur in their original full continuation order. -/
noncomputable def prepare : OracleComp HashSpec
    (Packet (LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK) := do
  let pair ← simulateQ RawCtxSelectiveSharedRom.coins (simulateQ (kemAmbientImpl baseImpl) kem.keygen)
  let state ← run setup env callbacks program post attachedVerify primitives baseImpl kem pair.2 pair.1
  let encapsulated ← simulateQ RawCtxSelectiveSharedRom.coins (simulateQ (kemAmbientImpl baseImpl) (kem.encaps pair.1))
  pure ⟨pair.1, pair.2, state, encapsulated.1⟩

/-- Only evaluation reconstructs the cache-bearing original source state. -/
def restore (packet : Packet (LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK)
    (cache initialCache : CtxRO.QueryCache) : PqxdhCorrelatedExtractFamily.Prepared
      (PqxdhAuthenticatedRootExperiment.protocol (environment setup env callbacks initialCache)
        kem attachedVerify primitives program post) KemSK :=
  ⟨packet.publicKey, packet.secretKey, PqxdhCommonSharedDispatch.restoreMode setup program packet.state cache, packet.ciphertext⟩

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual correlated preparation executes through one reached shared cache, including KEM generation, all source prefix work and the outer encapsulation. -/
theorem prepare_source (cache : CtxRO.QueryCache) :
    (fun result => restore setup env callbacks program post attachedVerify primitives kem result.1 result.2 cache) <$>
      (simulateQ hashImpl (prepare setup env callbacks program post attachedVerify primitives baseImpl kem)).run cache =
    PqxdhCorrelatedExtractFamily.prepare baseImpl kem
      (PqxdhAuthenticatedRootExperiment.protocol (environment setup env callbacks cache) kem attachedVerify primitives program post) := by
  simp only [prepare, simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete,
    bind_map_left, PqxdhCorrelatedExtractFamily.prepare]
  apply bind_congr
  intro pair
  change _ = do
    let state ← evalKem baseImpl kem pair.2
      ((PqxdhAuthenticatedRootExperiment.protocol (environment setup env callbacks cache) kem attachedVerify primitives program post).prepare pair.1)
    let encapsulated ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps pair.1)
    pure ({ publicKey := pair.1, secretKey := pair.2, state := state, ciphertext := encapsulated.1 } :
      PqxdhCorrelatedExtractFamily.Prepared (PqxdhAuthenticatedRootExperiment.protocol
        (environment setup env callbacks cache) kem attachedVerify primitives program post) KemSK)
  rw [← source setup env callbacks program post attachedVerify primitives baseImpl kem pair.2 pair.1 cache]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  apply bind_congr
  intro encapsulated
  simp only [simulateQ_pure, StateT.run_pure, map_pure, restore]

/-- Standard initialization starts the one ROM at its ordinary empty cache; no cache sampled by a local prefix is installed into the challenger. -/
theorem prepare_empty :
    (fun result => restore setup env callbacks program post attachedVerify primitives kem result.1 result.2 ∅) <$>
      (simulateQ hashImpl (prepare setup env callbacks program post attachedVerify primitives baseImpl kem)).run ∅ =
    PqxdhCorrelatedExtractFamily.prepare baseImpl kem
      (PqxdhAuthenticatedRootExperiment.protocol (environment setup env callbacks ∅) kem attachedVerify primitives program post) :=
  prepare_source setup env callbacks program post attachedVerify primitives baseImpl kem ∅

end BeaconcryptCore.Computational.PqxdhSourceSharedPreparation


/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.source

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.prepare_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.prepare_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparation.prepare_empty
