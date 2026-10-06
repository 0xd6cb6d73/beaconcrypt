-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengePreparedFits

/-! Derive continuation allowances in the actual generated source sampler, retaining completed branches and all correlated material draws. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits
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

open PqxdhLaterChallengeSampler

/-- Only an actual pending descriptor is required to carry the source all-reply continuation allowance; original outer and inner common decisions remain unrestricted. -/
noncomputable def PacketFits (q : Nat)
    (packet : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B))) : Prop :=
  match packet.1 with
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhLaterChallengeCapturedFits.BothFits owner number q (pending.1, packet.2)

/-- The complete prepared packet carries the exact descriptor/remainder certificate of its own source callback. -/
theorem prepared_fits (secret : KemSK) (challenge : MlKem768Ciphertext)
    (start : Input) (output : HmacBlock) (depth : Nat)
    (continuation : PqxdhInitialBuilderContext.BuildResult → OracleComp
      (PqxdhFirstRecordConfidentiality.AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (q : Nat) (bounded : ∀ reply, (continuation reply).IsTotalQueryBound q)
    (result : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : result ∈ support (prepared setup env callbacks owner number bit attachedVerify primitives baseImpl kem secret challenge start output depth continuation)) :
    PacketFits setup owner number q result := by
  simp only [prepared, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, reached, rfl⟩ := supported
  cases value with
  | inl decision => trivial
  | inr pending =>
      exact PqxdhLaterChallengePreparedFits.run_fits env0 callbacks baseImpl kem attachedVerify primitives secret challenge start output depth owner number bit continuation q bounded pending.1 pending.2 reached

/-- The actual generated selection supplies the same all-reply continuation allowance; neither completed preparation nor cached completion imposes a new condition on its Boolean. -/
theorem after_fits (packet : Packet) (output : HmacBlock) (depth : Nat)
    (q : Nat) (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound q)
    (result : LocalPacket × Option (Details (setup := setup) (M := M) (P := P) (I := I) (K := K) (S := S) (B := B)))
    (supported : result ∈ support (after setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth)) :
    PacketFits setup owner number q result := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision =>
      simp only [after, PqxdhLaterSharedParent.after, PqxdhSourceSharedInput.input, PqxdhInitialPreparedSourceInput.input,
        PqxdhSourceSharedPreparation.restore, PqxdhCommonSharedDispatch.restoreMode, map_pure, mem_support_pure_iff] at supported
      subst result
      trivial
  | pending prefixOutput ephemeral =>
      simp only [after] at supported
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        trivial
      · exact prepared_fits setup env callbacks owner number bit attachedVerify primitives baseImpl kem _ _ _ _ _ _ q (bounded prefixOutput.context.selection.1) _ supported

/-- Every actual supported full sampler retains the both complete source continuation allowances of its pending descriptor. All material draws and original completed outcomes remain present. -/
theorem run_fits (depth : Nat)
    (q : Nat) (bounded : ∀ selection reply, (adversary selection reply).IsTotalQueryBound q)
    (result : Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (supported : result ∈ support (PqxdhLaterChallengeSampler.run setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed depth)) :
    PacketFits setup owner number q (result.1.2.1.1.1, result.2) := by
  simp only [PqxdhLaterChallengeSampler.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, localPacket, reached, parent, _, nonce, _, chain, _, rfl⟩ := supported
  exact after_fits setup env callbacks program adversary owner number bit attachedVerify primitives baseImpl kem ancestors disclosed packet output depth q bounded localPacket reached

end BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.prepared_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.prepared_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.after_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.after_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.run_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeSamplerFits.run_fits
