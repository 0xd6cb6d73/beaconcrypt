import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceInput
import BeaconcryptCore.Computational.PqxdhInitialSourceAliases

/-!
The actual authenticated-root preparation supplies root-cache-free original callbacks to the initializer alias compiler. The complete shared and identity state is retained, including adaptive public decapsulation; only the separately threaded initializer root cache is held unchanged by these callbacks. The prepared input starts with an empty initializer cache as an exact source definition, not a freshness assumption.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialAliasPrepared
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhSourceAuthenticatedRoot PqxdhPrivateAcceptedRoot PqxdhPrivateKemSource PqxdhGeneratedBeaconState
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))


noncomputable def plain (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain
      (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (RawCtxSharedPrimitive.SharedState A × BareState 1) ProbComp) :=
  fun query state => Prod.fst <$> ((PqxdhInitialPreparedSourceInput.other env baseImpl kem attachedVerify primitives secret challenge query).run state).run ∅

/-- Every original noninitializer callback and the unused initializer branch leave the full initializer root cache unchanged; the complete shared/private computation is retained. -/
theorem cache_free (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhInitialNativeLog.External (SelectorSpec baseSpec) RatchetChain
      (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup) (PqxdhGeneratedBeaconState.KemHandle K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : RawCtxSharedPrimitive.SharedState A × BareState 1) (cache : RootOracle.QueryCache) :
    ((PqxdhInitialPreparedSourceInput.other env baseImpl kem attachedVerify primitives secret challenge query).run state).run cache =
      (fun result => (result, cache)) <$> (plain env baseImpl kem attachedVerify primitives secret challenge query).run state := by
  rcases query with query | (reply | (secrets | (query | query)))
  all_goals dsimp only [plain, PqxdhInitialPreparedSourceInput.other, PqxdhInitialCurrentBeacon.preparation,
    PqxdhInitialCurrentBeacon.application, PqxdhInitialPendingAmbient.selectorLift,
    PqxdhInitialPendingCurrent.selector, PqxdhInitialBeaconAmbient.lift, StateT.run]
  all_goals simp only [Functor.map_map]
  · rfl
  · let work := simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
      (PqxdhPhase2PostScheduler.publicWork ((borrowedSelector attachedVerify primitives 1 query).run state.2))
    change (fun result => ((result.1.1, state.1, result.1.2), result.2)) <$> ((fun result => (result, cache)) <$> work) =
      (fun a => (a.1, cache)) <$> ((fun result => ((result.1.1, state.1, result.1.2), result.2)) <$> ((fun result => (result, ∅)) <$> work))
    simp only [Functor.map_map]

variable (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
local notation "SourceInput" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

/-- Every pending input constructed by the actual preparation has an empty initial root cache and the literal original cache-free callbacks. -/
theorem input_admissible (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (input : SourceInput)
    (same : PqxdhInitialPreparedSourceInput.input env baseImpl kem attachedVerify primitives program post context selected number ancestors disclosed = .inr input) :
    PqxdhInitialSourceAliases.Admissible input := by
  cases state : context.state with
  | completed decision => simp [PqxdhInitialPreparedSourceInput.input, state] at same
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, state, Sum.inr.injEq] at same
    subst input
    constructor
    · rfl
    · funext query state cache
      exact cache_free env baseImpl kem attachedVerify primitives context.secretKey context.ciphertext query state cache

/-- Support of the actual original preparation carries these implementation facts without conditioning or any additional acceptance/freshness premise. -/
theorem prior_admissible (input : SourceInput)
    (reached : Sum.inr input ∈ support (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)) :
    PqxdhInitialSourceAliases.Admissible input := by
  rw [PqxdhInitialPreparedSourceInput.prior, support_map, Set.mem_image] at reached
  obtain ⟨context, _, same⟩ := reached
  exact input_admissible env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed context input same

/-- The source initializer alias allowance is paid by the original adaptive post budget on the exact preparation support. -/
theorem prior_post (qPost : Nat) (bounded : ∀ selection reply, (post selection reply).IsTotalQueryBound qPost)
    (input : SourceInput)
    (reached : Sum.inr input ∈ support (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)) :
    ∀ reply, (input.post reply).IsTotalQueryBound qPost := by
  rw [PqxdhInitialPreparedSourceInput.prior, support_map, Set.mem_image] at reached
  obtain ⟨context, _, same⟩ := reached
  cases state : context.state with
  | completed decision => simp [PqxdhInitialPreparedSourceInput.input, state] at same
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, state, Sum.inr.injEq] at same
    subst input
    exact bounded prepared.1.context.selection.1

/-- The actual authenticated-root preparation and original adaptive schedule discharge every operational premise of the full-source value-consistency correction. -/
theorem bound (stage qPost : Nat) (bounded : ∀ selection reply, (post selection reply).IsTotalQueryBound qPost) :
    (PqxdhInitialSourceSampled.game env.source env.recordWriter env.senderId env.route env.decode
      (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) stage).boolDistAdvantage
    (PqxdhInitialSourceAliases.consistent env.source env.recordWriter env.senderId env.route env.decode
      (PqxdhInitialPreparedSourceInput.prior env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) stage) ≤
      ((1 + (7 + qPost * 67) : Nat) : ENNReal).toReal / (2 ^ 256 : ℝ) :=
  PqxdhInitialSourceAliases.bound env.source env.recordWriter env.senderId env.route env.decode _ stage qPost
    (prior_admissible env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed)
    (prior_post env baseImpl kem attachedVerify primitives program post selected number ancestors disclosed qPost bounded)

end BeaconcryptCore.Computational.PqxdhInitialAliasPrepared

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.cache_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.cache_free

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.input_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.input_admissible

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.prior_admissible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.prior_admissible

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.prior_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.prior_post

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialAliasPrepared.bound
