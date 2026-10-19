import BeaconcryptCore.Computational.PqxdhCommonSharedContinuation

/-!
The actual candidate admission boundary retains unchanged honest, changed signed, attacker-owned and rejected candidates in one same-ROM prefix. Internal eligibility selects the pending root interface; every other nonfiltered branch executes its original common continuation. This module introduces no selected-key honesty premise and no assertion that a common decision is false.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCommonSharedDispatch
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhPrivateAcceptedRoot PqxdhPrivateRootSource PqxdhHiddenRoot PqxdhSecretInputKdf
open PqxdhSourceAuthenticatedRoot
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

local notation "LocalOutput" => PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program
local notation "environment" => PqxdhPreparedSharedPrefix.environment env callbacks
local notation "restore" => PqxdhBorrowedSharedPrefix.restore setup program
local notation "completed" => PqxdhCommonSharedContinuation.completed setup env program post attachedVerify primitives baseImpl kem secret
local notation "accepted" => PqxdhCommonSharedContinuation.accepted setup env callbacks program post attachedVerify primitives baseImpl kem secret

noncomputable def afterEncapsulation (output : LocalOutput) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) : OracleComp HashSpec Bool :=
  match encapsulated with
  | none => completed output
  | some (ciphertext, shared) =>
    match rootFailure env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
    | some _ => completed output
    | none => accepted output (ready env.server env.application identity keys.oneTime ephemeral ciphertext
        (productionHiddenRoot env.source
          (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) shared))

noncomputable def common (output : LocalOutput) : OracleComp HashSpec Bool :=
  match output.accepted with
  | none => completed output
  | some (identity, keys) => do
    if identity.toList ++ keys.oneTime.toList ∈ env.server.consumed then completed output
    else
      let ephemeral ← simulateQ RawCtxSelectiveSharedRom.coins (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen)
      let encapsulated ← simulateQ RawCtxSelectiveSharedRom.coins (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps keys.pqKey))
      afterEncapsulation setup env callbacks program post attachedVerify primitives baseImpl kem secret output identity keys ephemeral encapsulated

/-- Common completion retains the original arbitrary source decision and all preceding common-ROM effects. -/
theorem completed_source (output : LocalOutput) (cache : CtxRO.QueryCache)
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    Prod.fst <$> (simulateQ hashImpl (completed output)).run cache =
      evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.observe env.source none attachedVerify primitives 1 setup
        (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1) execution (restore output cache).2) :=
  PqxdhCommonSharedContinuation.completed_source setup environment program post attachedVerify primitives baseImpl kem secret output cache execution

/-- The exact admission tests depend on original fields and actual identity/reveal state, independently of the external hash-cache representation. -/
theorem eligibility_cache (output : LocalOutput) (cache : CtxRO.QueryCache) :
    PqxdhPrivatePhase1Prefix.changedBit (some (restore output cache).1, (restore output cache).2) =
      PqxdhPrivatePhase1Prefix.changedBit (some (restore output ∅).1, (restore output ∅).2) ∧
    targetEligible env.parameters (restore output cache) = targetEligible env.parameters (restore output ∅) := by
  exact ⟨rfl, rfl⟩

/-- Optional encapsulation failure and all DH/root checks precede the same original completed or accepted common continuation. -/
theorem afterEncapsulation_source (output : LocalOutput) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) (cache : CtxRO.QueryCache) :
    Prod.fst <$> (simulateQ hashImpl
      (afterEncapsulation setup env callbacks program post attachedVerify primitives baseImpl kem secret output identity keys ephemeral encapsulated)).run cache =
    evalKem baseImpl kem secret (match encapsulated with
      | none => PqxdhPrivateAcceptedRoot.observe env.source none attachedVerify primitives 1 setup
          (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1)
          ⟨some ephemeral, none, .error .badEncoding, env.server⟩ (restore output cache).2
      | some (ciphertext, shared) =>
        match rootFailure env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
        | some failure => PqxdhPrivateAcceptedRoot.observe env.source none attachedVerify primitives 1 setup
            (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1)
            ⟨some ephemeral, some ciphertext, .error failure, env.server⟩ (restore output cache).2
        | none => acceptedObserve env.source none attachedVerify primitives 1 setup
            (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1)
            (ready env.server env.application identity keys.oneTime ephemeral ciphertext
              (productionHiddenRoot env.source
                (serverCoordinates env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime) shared))
            (restore output cache).2) := by
  cases encapsulated with
  | none => exact completed_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache _
  | some encapsulated =>
    rcases encapsulated with ⟨ciphertext, shared⟩
    simp only [afterEncapsulation]
    cases checked : rootFailure env.source.crypto env.server.ikSk ephemeral.toList identity keys.prekey keys.oneTime with
    | none => exact PqxdhCommonSharedContinuation.accepted_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output _ cache
    | some failure => exact completed_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache _

set_option backward.isDefEq.respectTransparency false in
/-- Every actual accepted/rejected candidate keeps its source optional encapsulation, replay check, real root and unblocked original common continuation in one shared-ROM execution. -/
theorem common_source (output : LocalOutput) (cache : CtxRO.QueryCache) :
    Prod.fst <$> (simulateQ hashImpl
      (common setup env callbacks program post attachedVerify primitives baseImpl kem secret output)).run cache =
    evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.allCandidateCommon env.source kem env.native attachedVerify primitives 1 setup
      (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1)
      (restore output cache).2 env.server env.application env.ephemeralGen) := by
  cases selected : output.accepted with
  | none =>
    simp only [common, selected]
    have actual := completed_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache
      ⟨none, none, .error .badEncoding, env.server⟩
    simpa only [PqxdhPrivateAcceptedRoot.allCandidateCommon, Option.bind_some, PqxdhBorrowedSharedPrefix.restore, selected] using actual
  | some selectedKeys =>
    rcases selectedKeys with ⟨identity, keys⟩
    simp only [common, selected, PqxdhPrivateAcceptedRoot.allCandidateCommon, Option.bind_some,
      PqxdhBorrowedSharedPrefix.restore, PqxdhPrivateAcceptedRoot.acceptedCommon]
    by_cases replay : identity.toList ++ keys.oneTime.toList ∈ env.server.consumed
    · simp only [ite_eq_left replay]
      exact completed_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache
        ⟨none, none, .error .registrationReplay, env.server⟩
    · simp only [ite_eq_right replay, simulateQ_bind, StateT.run_bind, map_bind,
        RawCtxSelectiveSharedRom.coins_complete, bind_map_left, evalKem_bind,
        ← PqxdhPrivateRootQueryBounds.ccaAmbient_eq_lift, evalKem_ambient]
      apply bind_congr
      intro ephemeral
      apply bind_congr
      intro encapsulated
      exact afterEncapsulation_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output identity keys ephemeral encapsulated cache

inductive Mode (Output : Type) where
  | completed : Bool → Mode Output
  | pending : Output → List.Vector UInt8 32 → Mode Output

def restoreMode (mode : Mode LocalOutput) (cache : CtxRO.QueryCache) :
    PqxdhPrivateRootSource.Mode setup (program.Selection × State setup M P I K A S (B + 1)) :=
  match mode with
  | .completed decision => .completed decision
  | .pending output ephemeral => .pending (restore output cache) ephemeral

noncomputable def dispatch (output : LocalOutput) : OracleComp HashSpec (Mode LocalOutput) := do
  let prepared := restore output ∅
  if PqxdhPrivatePhase1Prefix.changedBit (some prepared.1, prepared.2) then pure (.completed false)
  else if targetEligible env.parameters prepared then
    let ephemeral ← simulateQ RawCtxSelectiveSharedRom.coins (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen)
    match rootFailure env.source.crypto env.server.ikSk ephemeral.toList
      output.context.publicIdentity.ed25519 output.context.generated.before.publicKey output.context.generated.after.publicKey with
    | none => pure (.pending output ephemeral)
    | some _ =>
      let _encapsulated ← simulateQ RawCtxSelectiveSharedRom.coins
        (simulateQ (kemAmbientImpl baseImpl) (kem.encaps output.context.generated.target))
      Mode.completed <$> completed output
  else Mode.completed <$> common setup env callbacks program post attachedVerify primitives baseImpl kem secret output

set_option backward.isDefEq.respectTransparency false in
/-- The original internal target selection and every common branch form one exact same-ROM admission experiment. -/
theorem dispatch_source (output : LocalOutput) (cache : CtxRO.QueryCache) :
    (fun result => restoreMode setup program result.1 result.2) <$>
      (simulateQ hashImpl (dispatch setup env callbacks program post attachedVerify primitives baseImpl kem secret output)).run cache =
      evalKem baseImpl kem secret (PqxdhPrivateAcceptedRoot.dispatch kem env.parameters attachedVerify primitives setup
        (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (restore output cache)) := by
  simp only [dispatch, PqxdhPrivateAcceptedRoot.dispatch]
  rw [(eligibility_cache setup env program output cache).1, (eligibility_cache setup env program output cache).2]
  split
  · simp only [simulateQ_pure, StateT.run_pure, map_pure, restoreMode, evalKem, simulateQ_pure]
  · split
    · simp only [simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete,
        bind_map_left, evalKem_bind, evalKem_ambient]
      apply bind_congr
      intro ephemeral
      change _ = evalKem baseImpl kem secret (match rootFailure env.source.crypto env.server.ikSk ephemeral.toList
        output.context.publicIdentity.ed25519 output.context.generated.before.publicKey output.context.generated.after.publicKey with
        | none => pure (PqxdhPrivateRootSource.Mode.pending (restore output cache) ephemeral)
        | some failure => do
          let encapsulated ← ccaAmbient (kem.encaps output.context.generated.target)
          let decision ← PqxdhPrivateAcceptedRoot.observe env.source none attachedVerify primitives 1 setup
            (PqxdhAuthenticatedRootExperiment.commonObserver environment program post) (some (restore output cache).1)
            ⟨some ephemeral, some encapsulated.1, .error failure, env.server⟩ (restore output cache).2
          pure (PqxdhPrivateRootSource.Mode.completed decision))
      split
      · simp only [simulateQ_pure, StateT.run_pure, map_pure, restoreMode, evalKem, simulateQ_pure]
      · rename_i failureCheck failure checked
        simp only [simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete,
          bind_map_left, evalKem_bind, evalKem_ambient]
        apply bind_congr
        intro encapsulated
        simp only [simulateQ_map, StateT.run_map, Functor.map_map, evalKem_pure, bind_pure_comp]
        have actual := congrArg (fun work : ProbComp Bool => (PqxdhPrivateRootSource.Mode.completed <$> work :
            ProbComp (PqxdhPrivateRootSource.Mode setup (program.Selection × State setup M P I K A S (B + 1)))))
          (completed_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache
            ⟨some ephemeral, some encapsulated.1, .error failure, env.server⟩)
        simpa only [Functor.map_map, restoreMode] using actual
    · simp only [simulateQ_map, StateT.run_map, Functor.map_map]
      have actual := congrArg (fun work : ProbComp Bool => (PqxdhPrivateRootSource.Mode.completed <$> work :
            ProbComp (PqxdhPrivateRootSource.Mode setup (program.Selection × State setup M P I K A S (B + 1)))))
        (common_source setup env callbacks program post attachedVerify primitives baseImpl kem secret output cache)
      simpa only [Functor.map_map, restoreMode, evalKem, simulateQ_bind, simulateQ_pure, bind_pure_comp, simulateQ_map, PqxdhAuthenticatedRootExperiment.Environment.parameters] using actual

end BeaconcryptCore.Computational.PqxdhCommonSharedDispatch


/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.completed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.completed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.eligibility_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.eligibility_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.afterEncapsulation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.afterEncapsulation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.common_source

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.dispatch_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedDispatch.dispatch_source
