import BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix
import BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds

/-!
The full generated prefix charges source identity/prekey/one-time generation, actual Phase1 writing and every original scheduler request. The KEM challenger generator, candidate dispatch, common continuation and outer encapsulation are separate later charges. No evaluated program or local callback is declared free.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca
open PqxdhInitializerSecrecy CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qWrite qCalls qSelector qLocal : Nat)
    (writeBound : ∀ candidate state, ((callbacks.phase1Write candidate).run state).IsTotalQueryBound qWrite)
    (mainBound : ∀ published, (program.main published).IsTotalQueryBound qCalls)
    (selectorBound : ∀ query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives count query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives count env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)

include writeBound mainBound selectorBound localBound in
/-- Actual optional Phase1 publication and all later ordinary requests retain a complete shared-hash and uniform-call ledger. -/
theorem generated_bills (index : Nat) (publicIdentity : PublicIdentity) (generated : Generated setup Unit)
    (transcript : Phase1PublicTranscript setup.Context) (identities : BareState count) :
    (PqxdhGeneratedSharedPrefix.run setup env callbacks program attachedVerify primitives count baseImpl kem secret
      index publicIdentity generated transcript identities).IsQueryBoundP (HashClass true) (69 * qCalls) ∧
    (PqxdhGeneratedSharedPrefix.run setup env callbacks program attachedVerify primitives count baseImpl kem secret
      index publicIdentity generated transcript identities).IsQueryBoundP (HashClass false)
        (qWrite + qCalls * (1 + qSelector + 69 * qLocal)) := by
  have writer : ∀ candidate auxiliary,
      ((PqxdhSourceAuxiliary.phase1 callbacks candidate).run auxiliary).IsTotalQueryBound qWrite := by
    intro candidate auxiliary
    exact PqxdhSourceAuxiliary.phase1_uniform callbacks candidate auxiliary qWrite (writeBound candidate auxiliary.1)
  have startBound := PqxdhGeneratedBeaconState.start_uniform setup (PqxdhSourceAuxiliary.phase1 callbacks) qWrite writer
    index publicIdentity generated env.binding (PqxdhGeneratedBeaconSelector.bundle transcript)
    (PqxdhGeneratedSharedPrefix.withCache setup env.initial ∅)
  have tail := fun started : Option Pqxdh.Bytes × State setup M P I K A S (B + 1) =>
    PqxdhOrdinarySharedSchedulerBounds.program_bills attachedVerify primitives count env.source env.recordWriter
      env.senderId env.route env.decode env.localImpl baseImpl kem secret qSelector qLocal selectorBound localBound
      (program.main (started.1.map (fun bytes => ⟨transcript, bytes⟩)))
      (PqxdhOrdinarySharedScheduler.separate (PqxdhPhase2OldSource.packState started.2 identities)) qCalls
      (mainBound _)
  simp only [PqxdhGeneratedSharedPrefix.run, bind_pure_comp]
  constructor
  · simpa only [Nat.zero_add] using isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _)
      (fun started _ => by simpa only [isQueryBoundP_map_iff] using (tail started).1)
  · exact isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_bound _ qWrite startBound)
      (fun started _ => by simpa only [isQueryBoundP_map_iff] using (tail started).2)

include writeBound mainBound in
/-- The full source identity/prekey/one-time generation, three real signatures, publication and original scheduler retain explicit hash and uniform counts. -/
theorem borrowed_bills (qPre qOne : Nat)
    (preBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPre)
    (oneBound : ∀ identity before target, (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOne)
    (selectorOneBound : ∀ query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives 1 query).run state)).IsTotalQueryBound qSelector)
    (localOneBound : ∀ query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives 1 env.source env.localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)
    (target : TargetKemPublicKey) :
    (PqxdhBorrowedSharedPrefix.run setup env callbacks program attachedVerify primitives baseImpl kem secret target).IsQueryBoundP (HashClass true) (69 * qCalls) ∧
    (PqxdhBorrowedSharedPrefix.run setup env callbacks program attachedVerify primitives baseImpl kem secret target).IsQueryBoundP (HashClass false)
      (32 + qPre + qOne + qWrite + qCalls * (1 + qSelector + 69 * qLocal)) := by
  have tail := fun seed before after => generated_bills setup env callbacks program attachedVerify primitives 1 baseImpl kem secret
    qWrite qCalls qSelector qLocal writeBound mainBound selectorOneBound localOneBound
    0 (primitives.publicKeys seed) (⟨before, target, (), after⟩ : Generated setup Unit)
    (PqxdhPrivatePhase1Prefix.transcript
      (PqxdhJointPhase1SourceWriter.signedCandidate primitives seed (primitives.publicKeys seed).ed25519
        (PqxdhPrivateKemSource.publicMaterial setup (primitives.publicKeys seed).ed25519 ⟨before, target, (), after⟩).keyTuple)
      (PqxdhPrivateKemSource.publicMaterial setup (primitives.publicKeys seed).ed25519 ⟨before, target, (), after⟩).context)
    (PqxdhJointPhase1SourceWriter.signedGlobalState primitives seed 1 0
      (PqxdhPrivateKemSource.publicMaterial setup (primitives.publicKeys seed).ed25519 ⟨before, target, (), after⟩).keyTuple
      (PqxdhJointPhase1AcceptanceComposition.singletonState primitives 1 seed).1,
     PqxdhJointPhase1SourceWriter.signedState primitives seed 0
      (PqxdhPrivateKemSource.publicMaterial setup (primitives.publicKeys seed).ed25519 ⟨before, target, (), after⟩).keyTuple
      (PqxdhJointPhase1AcceptanceComposition.singletonState primitives 1 seed).2)
  simp only [PqxdhBorrowedSharedPrefix.run, bind_pure_comp]
  constructor
  · apply (isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) (m := 69 * qCalls) ?_).mono (by omega)
    intro seed _
    apply (isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) (m := 69 * qCalls) ?_).mono (by omega)
    intro before _
    apply (isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_no_hash _) (m := 69 * qCalls) ?_).mono (by omega)
    intro after _
    simpa only [isQueryBoundP_map_iff] using (tail seed before after).1
  · simp only [Nat.add_assoc]
    apply isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_bound _ 32 sampleSeed_uniform_bound)
    intro seed _
    apply isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_bound _ qPre (preBound (primitives.publicKeys seed).ed25519))
    intro before _
    apply isQueryBoundP_bind (RawCtxSelectiveSharedRom.coins_bound _ qOne (oneBound (primitives.publicKeys seed).ed25519 before target))
    intro after _
    simpa only [isQueryBoundP_map_iff, Nat.add_assoc] using (tail seed before after).2

end BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds


/-- info: 'BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds.generated_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds.generated_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds.borrowed_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhGeneratedSharedPrefixBounds.borrowed_bills
