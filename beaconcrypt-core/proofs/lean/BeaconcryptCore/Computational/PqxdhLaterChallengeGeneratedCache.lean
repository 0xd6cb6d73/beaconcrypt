import BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedCache

/-! The complete generated later-record sampler excludes an already-used wrapper at a missing-parent cut whenever its full saved remainder returns the unchanged true target-publication event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache
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

/-- Normalizing the prepared packet's old initial cache retains the actual callback and its complete arbitrary-backend resume. The literal target-publication event excludes a challenge already used before that callback. -/
theorem prepared_not_used {Other : Type} (secret : KemSK) (challenge : MlKem768Ciphertext)
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
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1).2 reply)).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    ¬ details.request.before.pair.isSome := by
  simp only [PqxdhLaterChallengeSampler.prepared, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨value, current⟩, sampled, same⟩ := supported
  rcases value with decision | ⟨returned, captured⟩
  · cases same
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at same
    obtain ⟨⟨⟨storedEq, rfl⟩, rfl⟩, rfl⟩ := same
    subst stored
    subst owner
    exact PqxdhLaterChallengeCapturedCache.cache_not_used env0 callbacks baseImpl kem attachedVerify primitives secret challenge
      start output depth number position bit continuation pending details cache after sampled
      afterImpl before reply result completed accepted published

/-- The actual generated selection supplies the original challenge continuation and selected owner; neither is assumed from an arbitrary saved descriptor. Common preparation and collected decisions remain unchanged. -/
theorem after_not_used {Other : Type} (packet : Packet) (output : HmacBlock) (depth : Nat)
    (position : number.val = depth + 2)
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (cache after : CtxRO.QueryCache)
    (supported : ((Sum.inr (stored, Sum.inr pending), some details), after) ∈ support
      ((simulateQ hashImpl (PqxdhLaterChallengeSampler.after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem
        ancestors disclosed packet output depth)).run cache))
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1).2 reply)).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    ¬ details.request.before.pair.isSome := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode,
        map_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | pending prefixOutput ephemeral =>
      simp only [PqxdhLaterChallengeSampler.after, PqxdhSourceSharedInput.input,
        PqxdhInitialPreparedSourceInput.input, PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode] at supported
      exact prepared_not_used setup env callbacks owner number bit attachedVerify primitives baseImpl kem
        secretKey ciphertext _ rfl output depth position (adversary prefixOutput.context.selection.1)
        stored pending details cache after supported afterImpl before reply result completed accepted published

/-- The complete actual generated sampler, including preparation, initial64, parent76, nonce12 and next-chain32, excludes an already-used wrapper at its captured callback whenever the full saved resume returns the unchanged true marked publication. No sampler draw, common Boolean or backend effect is removed. -/
theorem run_not_used {Other : Type} (depth : Nat) (position : number.val = depth + 2)
    (carrier : PqxdhLaterChallengeSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (stored : Input × HmacBlock) (pending : Pending)
    (details : Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))
    (after : CtxRO.QueryCache)
    (supported : (carrier, after) ∈ support ((simulateQ hashImpl
      (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)).run ∅))
    (shape : carrier.1.2.1.1.1 = Sum.inr (stored, Sum.inr pending))
    (captured : carrier.2 = some details)
    (afterImpl : QueryImpl Base (StateT Other ProbComp)) (before : Other)
    (reply : (Base).Range (PqxdhInitialOriginContext.frame
      (PqxdhInitialSampledParent.marker env.source stored) env.senderId env.route env.decode pending.1).1)
    (result : (Bool × (Front × Trace)) × Other)
    (completed : result ∈ support ((simulateQ afterImpl
      ((PqxdhInitialOriginContext.frame (PqxdhInitialSampledParent.marker env.source stored)
        env.senderId env.route env.decode pending.1).2 reply)).run before))
    (accepted : result.1.1 = true)
    (published : ((owner, number), true) ∈ result.1.2.2.published) :
    ¬ details.request.before.pair.isSome := by
  simp only [PqxdhLaterChallengeSampler.run, simulateQ_bind, StateT.run_bind,
    RawCtxSelectiveSharedRom.coins_complete, bind_map_left, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨⟨packet, cache⟩, _, output, _, ⟨⟨localPacket, metadata⟩, current⟩, reached, parent, _, nonce, _, chain, _, same⟩ := supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  change localPacket = Sum.inr (stored, Sum.inr pending) at shape
  change metadata = some details at captured
  subst localPacket metadata
  exact after_not_used setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed
    packet output depth position stored pending details cache after reached afterImpl before reply result completed accepted published

end BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.prepared_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.prepared_not_used
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.after_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.after_not_used
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.run_not_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeGeneratedCache.run_not_used
