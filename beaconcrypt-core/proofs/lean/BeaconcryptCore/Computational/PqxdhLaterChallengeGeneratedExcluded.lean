import BeaconcryptCore.Computational.PqxdhLaterChallengeSampleExcluded

/-! Preserve the complete generated sampler while excluding an inside challenge phase for the original retained source continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (adversary : program.Selection → PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : U64) (bit : Bool)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (ancestors disclosed : List RatchetChain)
local notation "post" => PqxdhRecordConfidentialityChallenge.post adversary owner number bit
local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem owner number ancestors disclosed
abbrev Details := PqxdhLaterChallengeCapture.Details (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) Bool S (B + 1)

local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

local notation "Pending" => PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

local notation "Front" => PqxdhInitialPostContext.NativeFront M P (IdentityHandle I) (DhPair setup) (KemHandle K) S (B + 1)
local notation "Trace" => PqxdhInitialOriginPost.Trace Bool S (B + 1)
local notation "Base" => PqxdhInitialPostContext.Base (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
  (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared S (B + 1)

/-- The actual prepared packet retains its source callback and complete real retained resume; its target event excludes an inside cut. -/
theorem prepared_not_inside {OtherA OtherN OtherC : Type} (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (selected : start.selected = owner) (output : HmacBlock) (depth : Nat)
    (position : number.val = depth + 2)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (supported : ((Sum.inr (stored, Sum.inr pending), some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secret challenge start output depth continuation)).run cache))
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained env.source env.recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1
        (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  simp only [PqxdhLaterChallengeSampler.prepared, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨value, current⟩, sampled, same⟩ := supported
  rcases value with decision | ⟨returned, captured⟩
  · cases same
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at same
    obtain ⟨⟨⟨storedEq, rfl⟩, rfl⟩, rfl⟩ := same
    subst stored owner
    exact PqxdhLaterChallengeSampleExcluded.cache_not_inside env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth number position bit continuation pending details cache after sampled
      prior entry target full external atParent before result completed accepted published

/-- The actual generated selection supplies the owner and original continuation used by the retained inside-event exclusion. -/
theorem after_not_inside {OtherA OtherN OtherC : Type} (packet : Packet) (output : HmacBlock) (depth : Nat)
    (position : number.val = depth + 2)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (supported : ((Sum.inr (stored, Sum.inr pending), some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem
        ancestors disclosed packet output depth)).run cache))
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained env.source env.recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1
        (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode,
        map_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | pending prefixOutput ephemeral =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode] at supported
      exact prepared_not_inside setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secretKey ciphertext _ rfl output depth position (adversary prefixOutput.context.selection.1)
        stored pending details cache after supported prior entry target full external atParent before result completed accepted published

/-- The complete generated sampler retains preparation and every initial, parent, nonce and next-chain draw while excluding an inside cut for the same real retained target event. -/
theorem run_not_inside {OtherA OtherN OtherC : Type} (depth : Nat) (position : number.val = depth + 2)
    (carrier : PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (carrier, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : carrier.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : carrier.2 = some details)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : RootOutput) (full : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain (IdentityHandle I)
      (DhPair setup) (KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (PqxdhInitialBeaconAmbient.Ambient OtherA OtherN OtherC))
    (atParent : PqxdhInitialBuilderContext.address pending.1.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (result : (Bool × (Front × Trace)) × PqxdhInitialNativeRetained.RetainedState OtherA OtherN OtherC)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained env.source env.recordWriter
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target full) external)
      (PqxdhInitialOriginContext.resume (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1
        (PqxdhInitialParentBuilderContext.reply env.senderId env.route env.decode pending.1.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    PqxdhLaterChallengeSavedClassification.phase (some details) ≠ .inside := by
  simp only [PqxdhLaterChallengeSampler.run, simulateQ_bind, StateT.run_bind,
    RawCtxSelectiveSharedRom.coins_complete, bind_map_left, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨packet, cache⟩, _, output, _, ⟨⟨localPacket, metadata⟩, current⟩, reached, parent, _, nonce, _, chain, _, same⟩ := supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  change metadata = some details at captured
  rw [shape, captured] at reached
  exact after_not_inside setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    packet output depth position stored pending details cache after reached prior entry target full external atParent before result completed accepted published

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.prepared_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.prepared_not_inside

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.after_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.after_not_inside

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.run_not_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedExcluded.run_not_inside
