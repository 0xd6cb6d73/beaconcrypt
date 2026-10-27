import BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler
import BeaconcryptCore.Computational.PqxdhPhase2GeneratedDriver
import BeaconcryptCore.Computational.PqxdhSourceAuxiliary

/-!
Actual Phase1 publication and the generated owner's ordinary prechallenge scheduler execute through one ROM. The optional source writer is the concrete non-hash callback boundary; the complete generated keys, signed fields, old owners, original histories and scheduler remain unchanged. The initial cache is supplied by the enclosing executed prefix, and the final empty-ROM consumer will initialize that prefix once.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca
open PqxdhInitializerSecrecy CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)

/-- Replace only the external ROM component; all original prior owners and compromise observations are retained. -/
def withCache (state : InitialState setup M P I K A S B) (cache : CtxRO.QueryCache) :
    InitialState setup M P I K A S B := {state with primitive := (state.primitive.1, cache)}

def afterCache (state : State setup M P I K A S (B + 1)) (cache : CtxRO.QueryCache) :
    State setup M P I K A S (B + 1) := {state with primitive := (state.primitive.1, cache)}

set_option backward.isDefEq.respectTransparency false in
/-- The actual optional source writer is cache-free by its concrete callback interface; successful and failed publication retain the exact original private state. -/
theorem start_cache (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (binding : pqxdh.ServerBinding) (candidate : Phase1Candidate)
    (state : InitialState setup M P I K A S B) (cache : CtxRO.QueryCache) :
    start setup (PqxdhSourceAuxiliary.phase1 callbacks) index publicIdentity generated binding candidate (withCache setup state cache) =
      (fun result => (result.1, afterCache setup result.2 cache)) <$>
        start setup (PqxdhSourceAuxiliary.phase1 callbacks) index publicIdentity generated binding candidate (withCache setup state ∅) := by
  simp only [start_complete, PqxdhSourceAuxiliary.phase1_step, withCache, bind_map_left, map_bind]
  apply bind_congr
  intro result
  cases result.1 <;> simp only [map_pure, afterCache, extend]

variable (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

/-- The concrete Phase1 writer retains its original local state; only the ROM component is threaded by the enclosing interpreter. -/
def environment (cache : CtxRO.QueryCache) : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B :=
  {env with phase1Writer := PqxdhSourceAuxiliary.phase1 callbacks, initial := withCache setup env.initial cache}

/-- Original optional publication precedes the entire source scheduler. No selected message key is an argument. -/
noncomputable def run (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) :
    OracleComp HashSpec (Phase1Candidate × program.Selection ×
      PqxdhOrdinarySharedScheduler.Local M P I (DhPair setup) K A S (B + 1) count) := do
  let started ← simulateQ RawCtxSelectiveSharedRom.coins
    (start setup (PqxdhSourceAuxiliary.phase1 callbacks) index publicIdentity generated env.binding
      (PqxdhGeneratedBeaconSelector.bundle transcript) (withCache setup env.initial ∅))
  let selected ← (simulateQ
    (PqxdhOrdinarySharedScheduler.compiler attachedVerify primitives count env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret)
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))).run
      (PqxdhOrdinarySharedScheduler.separate (PqxdhPhase2OldSource.packState started.2 identities))
  pure (selected.1.1, (selected.1.2, selected.2))

set_option backward.isDefEq.respectTransparency false in
/-- The full generated-owner prefix equals the original ordinary driver, including failed publication, every optional scheduler reply and the exact reached cache. -/
theorem source (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2.1, PqxdhOrdinarySharedScheduler.attach result.1.2.2 result.2))) <$>
      (simulateQ hashImpl (PqxdhGeneratedSharedPrefix.run setup env callbacks program attachedVerify primitives count baseImpl kem secret
        index publicIdentity generated transcript identities)).run cache =
      evalKem baseImpl kem secret
        (PqxdhPhase2GeneratedDriver.ordinaryRun (environment setup env callbacks cache) program attachedVerify primitives count
          index publicIdentity generated transcript identities) := by
  simp only [PqxdhGeneratedSharedPrefix.run, PqxdhPhase2GeneratedDriver.ordinaryRun,
    simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure, map_pure,
    environment, evalKem_bind, evalKem_coins]
  rw [start_cache setup callbacks index publicIdentity generated env.binding
    (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial cache]
  rw [RawCtxSelectiveSharedRom.coins_complete]
  simp only [bind_map_left]
  apply bind_congr
  intro started
  have original := PqxdhOrdinarySharedScheduler.program attachedVerify primitives count env.source env.recordWriter
    env.senderId env.route env.decode env.localImpl baseImpl kem secret
    (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))
    (PqxdhOrdinarySharedScheduler.separate (PqxdhPhase2OldSource.packState started.2 identities)) cache
  simp only [PqxdhPhase2NativeSource.interpretation, QueryImpl.simulateQ_compose] at original
  have mapped := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work) original
  simpa only [Functor.map_map, evalKem, simulateQ_pure, bind_pure_comp,
    PqxdhOrdinarySharedScheduler.attach, PqxdhOrdinarySharedScheduler.separate,
    PqxdhPhase2OldSource.packState, afterCache, PqxdhPhase2SharedIdentity.pack] using mapped

end BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix.start_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix.start_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefix.source
