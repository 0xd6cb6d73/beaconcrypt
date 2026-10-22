import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps
import BeaconcryptCore.Computational.PqxdhInitialRootEventSecrecy
import BeaconcryptCore.Computational.PqxdhEvolvingChainComposition
import BeaconcryptCore.Computational.PqxdhInitialAliasPrepared

/-!
The authenticated source root, shared initial64 value and ordered complete76 chain derivations have one final source event. Its owner and positive record position are fixed before execution; the source schedule remains adaptive and retains all other owners and both directions. Freshness excludes byte-level disclosures that recover the target, including current-chain ancestors and retained skipped keys. All reductions, statistical charges and callback budgets are explicit. Replicated symbolic composition and adaptive raw-record forgery security are separate stages.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy
open PqxdhChallengeSecretRouting
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
local notation "actualPrior" => PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed

/-- Every pending outcome of the actual preparation retains the original target record position, without conditioning the sampler. -/
theorem prior_position (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup))
    (supported : Sum.inr input ∈ support actualPrior) : input.number = number := by
  rw [PqxdhInitialPreparedSourceInput.prior, support_map, Set.mem_image] at supported
  obtain ⟨context, _, same⟩ := supported
  cases mode : context.state with
  | completed decision => simp [PqxdhInitialPreparedSourceInput.input, mode] at same
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, mode, Sum.inr.injEq] at same
    subst input
    rfl

variable (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post)
local notation "q" => PqxdhInitialPreparedSourceCaps.postCap env baseImpl kem program post c
local notation "u" => PqxdhInitialPreparedSourceCaps.callbackCap env baseImpl kem program post c
local notation "v" => PqxdhInitialPreparedSourceCaps.selectorCap env baseImpl kem program post c
local notation "k" => PqxdhInitialPreparedSourceCaps.knownCap env baseImpl kem program post c disclosed

noncomputable def ideal : ProbComp Bool :=
  PqxdhInitialSourceAliases.consistent env.source env.recordWriter env.senderId env.route env.decode actualPrior number.val

noncomputable def loss (hmac : HmacSha512) (fallback : PqxdhDynamicIdentityRouting.DynamicForgery)
    (ordinaryFallback : PqxdhJointIdentity.Forgery) : ℝ :=
  PqxdhInitialRootEventSecrecy.loss env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed q hmac fallback ordinaryFallback +
    PqxdhEvolvingChainComposition.initialLoss env.source env.recordWriter env.senderId env.route env.decode actualPrior hmac +
    PqxdhEvolvingChainComposition.chainLoss env.source env.recordWriter env.senderId env.route env.decode actualPrior q k (number.val - 1) hmac +
    ((1 + (7 + q * 67) : Nat) : ENNReal).toReal / (2 ^ 256 : ℝ)

/-- The actual authenticated source event reaches the ordered selected chain experiment using only primitive/interface contracts and the original source caller certificate. Every observer resource premise and input distribution is discharged by actual preparation. -/
theorem coordinate_bound (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed).boolDistance
      (PqxdhInitialSourceSampled.game env.source env.recordWriter env.senderId env.route env.decode actualPrior number.val) ≤
    PqxdhInitialRootEventSecrecy.loss env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed q hmac fallback ordinaryFallback +
      PqxdhEvolvingChainComposition.initialLoss env.source env.recordWriter env.senderId env.route env.decode actualPrior hmac +
      PqxdhEvolvingChainComposition.chainLoss env.source env.recordWriter env.senderId env.route env.decode actualPrior q k (number.val - 1) hmac := by
  have rootBound := PqxdhInitialRootEventSecrecy.bound env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
    c q (PqxdhInitialPreparedSourceCaps.post_total env baseImpl kem program post c) compatible adapter functional hmac correct.root fallback ordinaryFallback
  have chainBound := PqxdhEvolvingChainComposition.initial_evolving_bound env.source env.recordWriter env.senderId env.route env.decode actualPrior
    q u u v c.qAux k
    (PqxdhInitialPreparedSourceCaps.supported_caps env baseImpl kem attachedVerify primitives program post c selected number ancestors disclosed)
    (number.val - 1) hmac correct (by
      intro input supported
      rw [prior_position env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed input supported]
      omega)
  have order : number.val - 1 + 1 = number.val := by omega
  rw [order] at chainBound
  have result := (ProbComp.boolDistance_triangle
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
    (PqxdhInitialPreparedSourceInput.uniformRoot env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
    (PqxdhInitialSourceSampled.game env.source env.recordWriter env.senderId env.route env.decode actualPrior number.val)).trans
      (add_le_add rootBound chainBound)
  simpa only [add_assoc] using result

/-- The authenticated source root, shared64 initializer and all ordered complete76 chain hops reach the value-consistent selected-chain ideal at the identical source publication/freshness event. The explicit loss includes every constructed primitive reduction and every collision/cache/alias term, with no honest-target, source-simulation or whole-observer-budget premise. -/
theorem bound (positive : 0 < number.val)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (correct : SourceFullCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed).boolDistance
      (ideal env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) ≤
    loss env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c hmac fallback ordinaryFallback := by
  have sourceBound := coordinate_bound env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c
    positive compatible adapter functional hmac correct fallback ordinaryFallback
  have aliasBound := PqxdhInitialAliasPrepared.bound env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
    number.val q (PqxdhInitialPreparedSourceCaps.post_total env baseImpl kem program post c)
  exact (ProbComp.boolDistance_triangle
    (PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
    (PqxdhInitialSourceSampled.game env.source env.recordWriter env.senderId env.route env.decode actualPrior number.val)
    (ideal env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)).trans
      (add_le_add sourceBound aliasBound)

end BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy
/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.prior_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.prior_position

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.coordinate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.coordinate_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy.bound
