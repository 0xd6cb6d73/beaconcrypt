import BeaconcryptCore.Computational.PqxdhCommonSharedRegistration
import BeaconcryptCore.Computational.PqxdhCommonOrdinaryObserver
import BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix

/-!
The actual common continuations execute registration and their complete unblocked post schedule through the same ROM as the generated prefix. The compiler contains no selected message key and retains arbitrary original common decisions. Full source states are reconstructed only by the interpreting cache boundary.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCommonSharedContinuation
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhPrivateAcceptedRoot
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

abbrev LocalOutput := PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program

noncomputable def completed (output : LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) : OracleComp HashSpec Bool :=
  Prod.fst <$> (simulateQ
    (PqxdhOrdinarySharedScheduler.compiler attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret)
    (post output.context.selection.1 (ok none))).run output.context.selection.2

/-- The complete ordinary source decision is preserved, including rejected, ineligible and attacker-owned candidate outcomes. -/
theorem completed_source (output : LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) (cache : CtxRO.QueryCache)
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    Prod.fst <$> (simulateQ hashImpl (completed setup env program post attachedVerify primitives baseImpl kem secret output)).run cache =
      evalKem baseImpl kem secret (observe env.source none attachedVerify primitives 1 setup
        (PqxdhAuthenticatedRootExperiment.commonObserver env program post)
        (some (PqxdhBorrowedSharedPrefix.restore setup program output cache).1) execution
        (PqxdhBorrowedSharedPrefix.restore setup program output cache).2) := by
  rw [PqxdhCommonOrdinaryObserver.completed]
  have original := congrArg (Functor.map Prod.fst)
    (PqxdhOrdinarySharedScheduler.program attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret
      (post output.context.selection.1 (ok none)) output.context.selection.2 cache)
  simp only [completed, simulateQ_map, StateT.run_map, Functor.map_map]
  simp only [Functor.map_map, PqxdhPhase2NativeSource.interpretation, QueryImpl.simulateQ_compose] at original
  simpa only [PqxdhBorrowedSharedPrefix.restore, evalKem, simulateQ_map,
    PqxdhPhase2OldSource.packState_unpackState, Functor.map_map] using original

noncomputable def accepted (output : LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) (ready : Ready) : OracleComp HashSpec Bool := do
  let before := PqxdhPhase2OldSource.unpackState (PqxdhOrdinarySharedScheduler.attach output.context.selection.2 ∅)
  let built ← PqxdhCommonSharedRegistration.build env.source env.recordWriter callbacks env.senderId env.index env.metadata ready before.1
  Prod.fst <$> (simulateQ
    (PqxdhOrdinarySharedScheduler.compiler attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret)
    (post output.context.selection.1 built.1)).run
      (PqxdhOrdinarySharedScheduler.separate (PqxdhPhase2OldSource.packState built.2 before.2))

/-- The original full ordinary continuation uses the reached cache and returns the same decision. -/
theorem post_source (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S (B + 1)) Bool)
    (state : PqxdhOrdinarySharedScheduler.Local M P I (DhPair setup) K A S (B + 1) 1) (cache : CtxRO.QueryCache) :
    Prod.fst <$> (simulateQ hashImpl (Prod.fst <$> (simulateQ
      (PqxdhOrdinarySharedScheduler.compiler attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret) client).run state)).run cache =
      evalKem baseImpl kem secret (Prod.fst <$> (simulateQ
        (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl) client).run
          (PqxdhOrdinarySharedScheduler.attach state cache)) := by
  have original := congrArg (Functor.map Prod.fst)
    (PqxdhOrdinarySharedScheduler.program attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl baseImpl kem secret client state cache)
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, evalKem,
    PqxdhPhase2NativeSource.interpretation, QueryImpl.simulateQ_compose] using original

set_option backward.isDefEq.respectTransparency false in
/-- Accepted common registration and its actual post schedule share all previous ROM entries and preserve every original optional response. -/
theorem accepted_source (output : LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program)
    (ready : Ready) (cache : CtxRO.QueryCache) :
    Prod.fst <$> (simulateQ hashImpl (accepted setup env callbacks program post attachedVerify primitives baseImpl kem secret output ready)).run cache =
      evalKem baseImpl kem secret (acceptedObserve env.source none attachedVerify primitives 1 setup
        (PqxdhAuthenticatedRootExperiment.commonObserver (PqxdhPreparedSharedPrefix.environment env callbacks) program post)
        (some (PqxdhBorrowedSharedPrefix.restore setup program output cache).1) ready
        (PqxdhBorrowedSharedPrefix.restore setup program output cache).2) := by
  have observed := PqxdhCommonOrdinaryObserver.accepted attachedVerify primitives 1
    (PqxdhPreparedSharedPrefix.environment env callbacks) program post
    (PqxdhBorrowedSharedPrefix.restore setup program output cache).1 ready
    (PqxdhBorrowedSharedPrefix.restore setup program output cache).2
  refine Eq.trans ?_ (congrArg (evalKem baseImpl kem secret) observed).symm
  simp only [evalKem_bind, evalKem_coins, PqxdhPreparedSharedPrefix.environment]
  have builder := PqxdhCommonSharedRegistration.build_source env.source env.recordWriter callbacks env.senderId env.index env.metadata ready
    (PqxdhPhase2OldSource.unpackState (PqxdhOrdinarySharedScheduler.attach output.context.selection.2 ∅)).1 cache
  simp only [accepted, simulateQ_bind, StateT.run_bind, map_bind]
  change _ = (do
    let value ← (PqxdhRegistrationProtocolState.build env.source env.recordWriter (PqxdhSourceAuxiliary.server callbacks)
      env.senderId env.index env.metadata ready).run
      (PqxdhCommonSharedRegistration.withCache
        (PqxdhPhase2OldSource.unpackState (PqxdhOrdinarySharedScheduler.attach output.context.selection.2 ∅)).1 cache)
    evalKem baseImpl kem secret (Prod.fst <$> (simulateQ
      (PqxdhPhase2SourceScheduler.ordinary attachedVerify primitives 1 env.source env.recordWriter env.senderId env.route env.decode env.localImpl)
      (post output.context.selection.1 value.1)).run
        (PqxdhPhase2OldSource.packState value.2 output.context.selection.2.auxiliary.2)))
  rw [← builder]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  rw [post_source]
  rfl

end BeaconcryptCore.Computational.PqxdhCommonSharedContinuation


/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.completed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.completed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.post_source

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.accepted_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedContinuation.accepted_source
