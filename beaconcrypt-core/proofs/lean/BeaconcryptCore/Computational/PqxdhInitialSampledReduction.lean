import BeaconcryptCore.Computational.PqxdhInitialSampledResources

/-!
The constructed main and candidate reductions include the original preparation, shared initializer response, actual stopped source prefix, one full parent draw and the complete adaptive source/checker continuation. The candidate tester evaluates the real fixed HKDF at every returned candidate. The freshness factor multiplies advantages, not the individual reduction query caps.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledReduction
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSourcePreparedSecrecy
open RawCtxSelectedParentEntry PqxdhInitialSampledParent PqxdhInitialSampledResources
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat) (prior : ProbComp (Context extra M P I D K X Response A N S B))

local notation "globalSample" => PqxdhInitialSampledParent.sample source writer sender route decode depth prior
local notation "globalAddress" => PqxdhInitialSampledParent.address (prior := prior) source writer sender route decode depth
local notation "mainObserver" => PqxdhInitialSampledParent.observer (prior := prior) source writer sender route decode depth remaining
local notation "testObserver" => PqxdhInitialSampledParentSecrecy.aliasTester (prior := prior) source writer sender route decode depth remaining
local notation "actualGame" => PqxdhInitialSampledParentSecrecy.actual source writer sender route decode depth remaining globalSample globalAddress
local notation "randomGame" => PqxdhInitialSampledParentSecrecy.random source writer sender route decode depth remaining globalSample globalAddress

variable (qPost qPre qApplication qSelector qAux qKnown : Nat)
local notation "Q" => candidateCap remaining qPost qKnown

noncomputable def loss (hmac : HmacSha512) : ℝ :=
  RawCtxSelectedParentHop.extractLoss hmac globalSample globalAddress mainObserver +
    RawCtxSelectedParentHop.hmacLoss hmac globalSample globalAddress mainObserver +
    3 * (RawCtxSelectedParentHop.extractLoss hmac globalSample globalAddress testObserver +
      RawCtxSelectedParentHop.hmacLoss hmac globalSample globalAddress testObserver +
      (2 ^ 352 : ℝ)⁻¹ + (Q : ℝ) / (2 ^ 256 : ℝ))

variable (sourceCaps : ∀ input, Sum.inr input ∈ support prior → Caps input qPost qPre qApplication qSelector qAux qKnown)

include sourceCaps in
/-- One global parent-child reduction uses the exact original preparation and source distribution, with the complete candidate allowance derived from actual supported source inputs. -/
theorem bound (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) :
    (actualGame).boolDistAdvantage randomGame ≤
      loss source writer sender route decode depth remaining prior qPost qKnown hmac := by
  exact PqxdhInitialSampledParentSecrecy.bound source writer sender route decode depth remaining hmac correct
    globalSample globalAddress Q (fun context output result supported =>
      (PqxdhInitialSampledResources.observed_bounds source writer sender route decode depth remaining
        qPost qPre qApplication qSelector qAux qKnown prior sourceCaps context output).2 result supported)

noncomputable def reductionObserver (forTester : Bool) :
    FullObserver (Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) :=
  if forTester then testObserver else mainObserver

variable (qPrior : Nat)
local notation "V" => qPrior + (64 + sampleBudget qPost qPre qApplication qSelector qAux)
local notation "U" => observerBudget remaining qPost qPre qApplication qSelector qAux

include sourceCaps in
/-- Each constructed reduction uses two HMAC challenge queries and pays all preparation, initializer, parent and observer coins. Its separate candidate tester retains up to Q real fixed-HKDF evaluations. -/
theorem reduction_queries (priorBound : prior.IsTotalQueryBound qPrior) :
    (∀ forTester, let observe := reductionObserver source writer sender route decode depth remaining prior forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint globalSample globalAddress) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint globalSample globalAddress) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((V + 76) + U)) ∧
      (∀ (context : Packet (extra := extra) (M := M) (P := P) (I := I) (D := D) (K := K) (X := X) (Response := Response) (A := A) (N := N) (S := S) (B := B) source writer sender route decode depth prior × Entry) output result, result ∈ support (PqxdhInitialSampledParent.observed source writer sender route decode depth remaining context output) →
        (RawCtxFullPreimageTester.evaluate output (PqxdhInitialCommonSecrecy.candidates result)).IsTotalQueryBound Q) := by
  have sampledBound := PqxdhInitialSampledResources.sample_uniform source writer sender route decode depth
    qPost qPre qApplication qSelector qAux qKnown prior sourceCaps qPrior priorBound
  have observers := PqxdhInitialSampledResources.observer_bounds source writer sender route decode depth remaining
    qPost qPre qApplication qSelector qAux qKnown prior sourceCaps
  refine ⟨?_, ?_⟩
  · intro forTester
    apply RawCtxSelectedParentSecrecy.reduction_bounds globalSample globalAddress _ V U sampledBound
    cases forTester
    · exact observers.1
    · exact observers.2
  · exact RawCtxFullPreimageTester.tester_evaluation_bound _ _
      (fun context output result supported =>
        (PqxdhInitialSampledResources.observed_bounds source writer sender route decode depth remaining
          qPost qPre qApplication qSelector qAux qKnown prior sourceCaps context output).2 result supported)

include sourceCaps in
/-- Ordinary-game challenger totals retain the extra Extract key, HMAC key and random HMAC blocks, and the independent full76 child, in addition to the same complete source bill. -/
theorem challenger_queries (priorBound : prior.IsTotalQueryBound qPrior) (hmac : HmacSha512) (forTester : Bool) :
    let observe := reductionObserver source writer sender route decode depth remaining prior forTester
    let joint := RawCtxSelectedParentSecrecy.joint globalSample globalAddress
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + U) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound ((V + 76) + (64 + U)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound (64 + ((V + 76) + U)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound ((V + 76) + (64 + (64 + U))) ∧
      (RawCtxSelectedParentSecrecy.random globalSample globalAddress observe).IsTotalQueryBound ((V + 76) + (76 + U)) := by
  have sampledBound := PqxdhInitialSampledResources.sample_uniform source writer sender route decode depth
    qPost qPre qApplication qSelector qAux qKnown prior sourceCaps qPrior priorBound
  have observers := PqxdhInitialSampledResources.observer_bounds source writer sender route decode depth remaining
    qPost qPre qApplication qSelector qAux qKnown prior sourceCaps
  apply RawCtxSelectedParentSecrecy.challenger_bounds hmac globalSample globalAddress _ V U sampledBound
  cases forTester
  · exact observers.1
  · exact observers.2

end BeaconcryptCore.Computational.PqxdhInitialSampledReduction

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledReduction.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledReduction.bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledReduction.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledReduction.reduction_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledReduction.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledReduction.challenger_queries
