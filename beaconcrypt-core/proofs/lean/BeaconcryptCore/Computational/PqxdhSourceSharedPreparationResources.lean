import BeaconcryptCore.Computational.PqxdhCommonSharedRegistrationResources

/-!
The original source preparation receives one complete resource ledger. Bounds are supplied at concrete generators, native callbacks, and adversarial schedules, then composed through the actual candidate dispatch and retained common continuations. These are query bounds, not security assumptions or runtime-free declarations.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources
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
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qPost qSelector qLocal qPeer qPlaintext qWriter : Nat)
    (postBound : ∀ selection response, (post selection response).IsTotalQueryBound qPost)
    (selectorBound : ∀ query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)
    (peerBound : ∀ state, (callbacks.reservePeer.run state).IsTotalQueryBound qPeer)
    (plaintextBound : ∀ size state, ((callbacks.reservePlaintext size).run state).IsTotalQueryBound qPlaintext)
    (writerBound : ∀ fields state, ((callbacks.responseWrite fields).run state).IsTotalQueryBound qWriter)

local notation "LocalOutput" => PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program

/-- A complete source post schedule pays its actual callback cap, including all failures and optional replies. -/
def postCost (hash : Bool) (qPost qSelector qLocal : Nat) : Nat :=
  if hash then 69 * qPost else qPost * (1 + qSelector + 69 * qLocal)

def registrationCost (hash : Bool) (qPeer qPlaintext qWriter : Nat) : Nat :=
  if hash then 1 else qPeer + qPlaintext + qWriter

def coinsCost (hash : Bool) (q : Nat) : Nat := if hash then 0 else q

/-- Local probabilistic work introduces no hash query and retains its entire uniform-call bill. -/
theorem coins {Result : Type} (work : ProbComp Result) (q : Nat) (bounded : work.IsTotalQueryBound q) (hash : Bool) :
    (simulateQ RawCtxSelectiveSharedRom.coins work).IsQueryBoundP (HashClass hash) (coinsCost hash q) := by
  cases hash
  · exact RawCtxSelectiveSharedRom.coins_bound work q bounded
  · exact RawCtxSelectiveSharedRom.coins_no_hash work

include postBound selectorBound localBound in
/-- Common rejection and ineligible completion execute the whole original ordinary post schedule. -/
theorem completed (hash : Bool) (output : LocalOutput) :
    (PqxdhCommonSharedContinuation.completed setup env program post attachedVerify primitives baseImpl kem secret output).IsQueryBoundP
      (HashClass hash) (postCost hash qPost qSelector qLocal) := by
  have bounded := PqxdhOrdinarySharedSchedulerBounds.program_bills attachedVerify primitives 1 env.source env.recordWriter
    env.senderId env.route env.decode env.localImpl baseImpl kem secret qSelector qLocal selectorBound localBound
    (post output.context.selection.1 (.ok none)) output.context.selection.2 qPost (postBound _ _)
  cases hash
  · simpa only [PqxdhCommonSharedContinuation.completed, isQueryBoundP_map_iff, postCost, Bool.false_eq_true, if_false] using bounded.2
  · simpa only [PqxdhCommonSharedContinuation.completed, isQueryBoundP_map_iff, postCost, if_true] using bounded.1

include postBound selectorBound localBound peerBound plaintextBound writerBound in
/-- Accepted common candidates pay the actual registration builder and then the full adaptive post schedule, for every builder reply. -/
theorem accepted (hash : Bool) (output : LocalOutput) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    (PqxdhCommonSharedContinuation.accepted setup env callbacks program post attachedVerify primitives baseImpl kem secret output ready).IsQueryBoundP
      (HashClass hash) (registrationCost hash qPeer qPlaintext qWriter + postCost hash qPost qSelector qLocal) := by
  simp only [PqxdhCommonSharedContinuation.accepted]
  apply isQueryBoundP_bind (PqxdhCommonSharedRegistrationResources.build env.source env.recordWriter callbacks
    qPeer qPlaintext qWriter peerBound plaintextBound writerBound hash _ _ _ _ _)
  intro built _
  have bounded := PqxdhOrdinarySharedSchedulerBounds.program_bills attachedVerify primitives 1 env.source env.recordWriter
    env.senderId env.route env.decode env.localImpl baseImpl kem secret qSelector qLocal selectorBound localBound
    (post output.context.selection.1 built.1)
    (PqxdhOrdinarySharedScheduler.separate (PqxdhPhase2OldSource.packState built.2
      (PqxdhPhase2OldSource.unpackState (PqxdhOrdinarySharedScheduler.attach output.context.selection.2 ∅)).2))
    qPost (postBound _ _)
  cases hash
  · simpa only [isQueryBoundP_map_iff, postCost, Bool.false_eq_true, if_false] using bounded.2
  · simpa only [isQueryBoundP_map_iff, postCost, if_true] using bounded.1

include postBound selectorBound localBound peerBound plaintextBound writerBound in
/-- Every optional encapsulation and DH-check outcome keeps its corresponding complete common continuation. -/
theorem afterEncapsulation (hash : Bool) (output : LocalOutput) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (ephemeral : List.Vector UInt8 32) (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    (PqxdhCommonSharedDispatch.afterEncapsulation setup env callbacks program post attachedVerify primitives baseImpl kem secret
      output identity keys ephemeral encapsulated).IsQueryBoundP (HashClass hash)
      (registrationCost hash qPeer qPlaintext qWriter + postCost hash qPost qSelector qLocal) := by
  have rejected := (completed setup env program post attachedVerify primitives baseImpl kem secret qPost qSelector qLocal
    postBound selectorBound localBound hash output).mono (Nat.le_add_left _ (registrationCost hash qPeer qPlaintext qWriter))
  cases encapsulated with
  | none => exact rejected
  | some pair =>
    rcases pair with ⟨ciphertext, shared⟩
    simp only [PqxdhCommonSharedDispatch.afterEncapsulation]
    split
    · exact rejected
    · exact accepted setup env callbacks program post attachedVerify primitives baseImpl kem secret
        qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound hash output _

variable (qEphemeral qEncaps : Nat)
    (ephemeralBound : (simulateQ (kemAmbientImpl baseImpl) env.ephemeralGen).IsTotalQueryBound qEphemeral)
    (nativeEncapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (env.native.encaps target)).IsTotalQueryBound qEncaps)
    (encapsBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncaps)

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound in
/-- Attacker-owned and rejected candidate routes retain replay checks, optional native encapsulation, actual source DH checks, and all post work. -/
theorem common (hash : Bool) (output : LocalOutput) :
    (PqxdhCommonSharedDispatch.common setup env callbacks program post attachedVerify primitives baseImpl kem secret output).IsQueryBoundP
      (HashClass hash) (coinsCost hash qEphemeral + coinsCost hash qEncaps +
        registrationCost hash qPeer qPlaintext qWriter + postCost hash qPost qSelector qLocal) := by
  have rejected := completed setup env program post attachedVerify primitives baseImpl kem secret qPost qSelector qLocal
    postBound selectorBound localBound hash output
  simp only [PqxdhCommonSharedDispatch.common]
  split
  · exact rejected.mono (by omega)
  · split
    · exact rejected.mono (by omega)
    · simp only [Nat.add_assoc]
      apply isQueryBoundP_bind (coins _ qEphemeral ephemeralBound hash)
      intro ephemeral _
      apply isQueryBoundP_bind (coins _ qEncaps (nativeEncapsBound _) hash)
      intro encapsulated _
      exact afterEncapsulation setup env callbacks program post attachedVerify primitives baseImpl kem secret
        qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound hash output _ _ ephemeral encapsulated

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound in
/-- One actual candidate dispatcher pays at most one ephemeral draw and one encapsulation before the complete registration/post continuation. The internally rejected changed-signature branch remains present. -/
theorem dispatch (hash : Bool) (output : LocalOutput) :
    (PqxdhCommonSharedDispatch.dispatch setup env callbacks program post attachedVerify primitives baseImpl kem secret output).IsQueryBoundP
      (HashClass hash) (coinsCost hash qEphemeral + coinsCost hash qEncaps +
        registrationCost hash qPeer qPlaintext qWriter + postCost hash qPost qSelector qLocal) := by
  simp only [PqxdhCommonSharedDispatch.dispatch]
  split
  · trivial
  · split
    · simp only [Nat.add_assoc]
      apply isQueryBoundP_bind (coins _ qEphemeral ephemeralBound hash)
      intro ephemeral _
      split
      · trivial
      · apply isQueryBoundP_bind (coins _ qEncaps (encapsBound _) hash)
        intro encapsulated _
        simp only [isQueryBoundP_map_iff]
        exact (completed setup env program post attachedVerify primitives baseImpl kem secret qPost qSelector qLocal
          postBound selectorBound localBound hash output).mono (by omega)
    · simpa only [isQueryBoundP_map_iff] using common setup env callbacks program post attachedVerify primitives baseImpl kem secret
        qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
        qEphemeral qEncaps ephemeralBound nativeEncapsBound hash output

variable (qPre qOne qPhase1Write qMain : Nat)
    (preBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPre)
    (oneBound : ∀ identity before target, (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOne)
    (phase1WriteBound : ∀ candidate state, ((callbacks.phase1Write candidate).run state).IsTotalQueryBound qPhase1Write)
    (mainBound : ∀ published, (program.main published).IsTotalQueryBound qMain)

def generatedCost (hash : Bool) (qPre qOne qPhase1Write qMain qSelector qLocal : Nat) : Nat :=
  if hash then 69 * qMain else 32 + qPre + qOne + qPhase1Write + qMain * (1 + qSelector + 69 * qLocal)

include postBound selectorBound localBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound in
/-- The whole original generated prefix and candidate dispatcher retain every source sampler and complete common continuation in one ledger. -/
theorem run (hash : Bool) (target : TargetKemPublicKey) :
    (PqxdhSourceSharedPreparation.run setup env callbacks program post attachedVerify primitives baseImpl kem secret target).IsQueryBoundP
      (HashClass hash) (generatedCost hash qPre qOne qPhase1Write qMain qSelector qLocal +
        (coinsCost hash qEphemeral + coinsCost hash qEncaps +
        registrationCost hash qPeer qPlaintext qWriter + postCost hash qPost qSelector qLocal)) := by
  have generated := PqxdhGeneratedSharedPrefixBounds.borrowed_bills setup env.toDriverEnvironment callbacks program
    attachedVerify primitives baseImpl kem secret qPhase1Write qMain qSelector qLocal phase1WriteBound mainBound
    qPre qOne preBound oneBound selectorBound localBound target
  have bounded : (PqxdhBorrowedSharedPrefix.run setup env.toDriverEnvironment callbacks program attachedVerify primitives baseImpl kem secret target).IsQueryBoundP
      (HashClass hash) (generatedCost hash qPre qOne qPhase1Write qMain qSelector qLocal) := by
    cases hash
    · exact generated.2
    · exact generated.1
  exact isQueryBoundP_bind bounded (fun output _ => dispatch setup env callbacks program post attachedVerify primitives baseImpl kem secret
    qPost qSelector qLocal qPeer qPlaintext qWriter postBound selectorBound localBound peerBound plaintextBound writerBound
    qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound hash output)

/-- Complete local uniform bill, with the optional/total dispatch encapsulation and the outer encapsulation both charged. -/
def uniformCost (qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal
    qEphemeral qEncaps qPeer qPlaintext qWriter : Nat) : Nat :=
  qKeygen + 32 + qPre + qOne + qPhase1Write + (qMain + qPost) * (1 + qSelector + 69 * qLocal) +
    qEphemeral + 2 * qEncaps + qPeer + qPlaintext + qWriter

include postBound peerBound plaintextBound writerBound ephemeralBound nativeEncapsBound encapsBound
    preBound oneBound phase1WriteBound mainBound in
/-- The literal correlated-source sampler has a checked whole-preparation ledger: actual KEM keygen, full source prefix, every candidate branch, all local callbacks, and outer encapsulation. -/
theorem prepare (qKeygen : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (selectorAllBound : ∀ secret query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localAllBound : ∀ secret query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)
    (hash : Bool) :
    (PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem).IsQueryBoundP
      (HashClass hash) (if hash then 69 * qMain + 1 + 69 * qPost else
        uniformCost qKeygen qPre qOne qPhase1Write qMain qPost qSelector qLocal qEphemeral qEncaps qPeer qPlaintext qWriter) := by
  have whole := isQueryBoundP_bind (coins _ qKeygen keygenBound hash) (fun pair _ =>
    isQueryBoundP_bind (run setup env callbacks program post attachedVerify primitives baseImpl kem pair.2
      qPost qSelector qLocal qPeer qPlaintext qWriter postBound (selectorAllBound pair.2) (localAllBound pair.2)
      peerBound plaintextBound writerBound qEphemeral qEncaps ephemeralBound nativeEncapsBound encapsBound
      qPre qOne qPhase1Write qMain preBound oneBound phase1WriteBound mainBound hash pair.1)
      (fun state _ => (isQueryBoundP_map_iff _
        (fun encapsulated => (⟨pair.1, pair.2, state, encapsulated.1⟩ :
          PqxdhSourceSharedPreparation.Packet (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK)) _).mpr
          (coins _ qEncaps (encapsBound pair.1) hash)))
  convert whole using 1
  · simp only [PqxdhSourceSharedPreparation.prepare, bind_pure_comp]
  · cases hash <;> simp [coinsCost, generatedCost, registrationCost, postCost, uniformCost, Nat.add_mul] <;> omega

end BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.coins

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.completed

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.afterEncapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.afterEncapsulation

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.common

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.dispatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.dispatch

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.run

/-- info: 'BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSourceSharedPreparationResources.prepare
