import BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler

/-! The same saved-source continuation is compared to its full ordinary CTX execution with an explicit original nonce-refusal event. Hidden disclosure is retained in the event, and no freshness or nonce-uniqueness premise is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord PqxdhFirstRecordConfidentiality
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (monitor : Fin B) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C))
local notation "parent" => Entry.mk (PqxdhInitialBuilderContext.address context.original) material

noncomputable def staged :=
  (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
    (PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux fixed writer prior target nonce next sender read
      qPost context material fits state.1)).run state.2

noncomputable def original := do
  let prepared ← staged pre application initial selector aux fixed writer prior key target nonce next sender read qPost context material fits state
  (simulateQ (traced pre application initial selector aux fixed writer prior (some parent) key target nonce next sender route read mark)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient prepared.1.1)).run (insProject (prepared.1.2, prepared.2))

noncomputable def augmented := do
  let prepared ← staged pre application initial selector aux fixed writer prior key target nonce next sender read qPost context material fits state
  (simulateQ (insAugmented pre application initial selector aux fixed writer prior (some parent) key target nonce next sender route read mark monitor)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient prepared.1.1)).run (prepared.1.2, prepared.2)

noncomputable def compiled :=
  PqxdhSelectedStateInterpreter.pair <$>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
      (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read
        monitor qPost context material fits state.1)).run state.2

noncomputable def flagged := do
  let prepared ← staged pre application initial selector aux fixed writer prior key target nonce next sender read qPost context material fits state
  (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (insAugmented pre application initial selector aux fixed writer prior (some parent) key target nonce next sender route read mark monitor)
      (insStops (extra := extra) prior (some parent) target nonce next sender))
    (RawCtxSelectedFamilyNonceCoupling.optionalClient prepared.1.1)).run ((prepared.1.2, prepared.2), false)

/-- With its original hidden-disclosure event retained, the complete source execution equals the augmented execution of the same actual saved request and every later request. -/
theorem original_good (event : Option Bool × Traced M P I D K A N C S B → Prop) :
    𝒟[(fun result => (by classical exact decide (event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1))) <$>
      original pre application initial selector aux fixed writer prior key target nonce next mark sender route read
        qPost context material fits state] {true} =
    𝒟[(fun result => (by classical exact decide (event (result.1, insProject result.2) ∧
      PqxdhSelectedPostDisclosure.Good (insProject result.2).1))) <$>
      augmented pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
        qPost context material fits state] {true} := by
  classical
  simp only [original, augmented, map_bind, evalDist_apply_singleton, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro prepared
  congr 1
  have equality := post_source_augmented_vcvioLegacy pre application initial selector aux fixed writer prior (some parent) key target nonce next
    sender route read mark monitor prepared.1.1 (prepared.1.2, prepared.2) event
  rw [← true_mass_eq_vcvioLegacy, ← true_mass_eq_vcvioLegacy, evalDist_apply_singleton, evalDist_apply_singleton] at equality
  exact equality

/-- The sole operational difference at this hop is the actual sticky nonce refusal in the same full continuation. Its mass is explicit rather than assumed zero. -/
theorem augmented_bound (event : Option Bool × InsFull M P I D K A N C S B → Bool) :
    𝒟[event <$> augmented pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
      qPost context material fits state] {true} ≤
    𝒟[event <$> compiled pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
      qPost context material fits state] {true} +
    𝒟[(fun result => result.2.2 && event (result.1, result.2.1)) <$>
      flagged pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
        qPost context material fits state] {true} := by
  rw [compiled, PqxdhLaterSavedPostCompiler.complete_evaluated]
  simp only [augmented, flagged, staged, map_bind, evalDist_apply_singleton, probOutput_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro prepared
  rw [← mul_add]
  apply mul_le_mul_right
  simpa only [evalDist_apply_singleton] using
    augmented_le_evaluated pre application initial selector aux fixed writer prior (some parent) key target nonce next
      sender route read mark monitor prepared.1.1 (prepared.1.2, prepared.2) event

/-- Interpreting material and erasing only the auxiliary ledger recovers the already established complete saved-source experiment, including its original Boolean decision. -/
theorem original_source :
    (fun result => (result.1, tracedProj key result.2)) <$>
      original pre application initial selector aux fixed writer prior key target nonce next mark sender route read
        qPost context material fits state =
    (fun result => (some result.1, result.2)) <$>
      PqxdhLaterSavedContext.complete pre application initial selector aux fixed writer prior key target nonce next mark
        sender route read qPost context material fits state := by
  rw [← PqxdhLaterSavedPostCompiler.source_complete pre application initial selector aux fixed writer prior key target nonce next mark
    sender route read qPost context material fits state]
  simp only [original, staged, map_bind, traced_total, Functor.map_map, Prod.map_def, id_eq]

/-- Every source event retaining hidden-disclosure freshness is bounded by the complete executable event plus the actual nonce-refusal event of the same reached continuation. -/
theorem source_bound (event : Option Bool × Traced M P I D K A N C S B → Prop) :
    𝒟[(fun result => (by classical exact decide (event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1))) <$>
      original pre application initial selector aux fixed writer prior key target nonce next mark sender route read
        qPost context material fits state] {true} ≤
    𝒟[(fun result => (by classical exact decide (event (result.1, insProject result.2) ∧
      PqxdhSelectedPostDisclosure.Good (insProject result.2).1))) <$>
      compiled pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
        qPost context material fits state] {true} +
    𝒟[(fun result => result.2.2 && (by classical exact decide (event (result.1, insProject result.2.1) ∧ PqxdhSelectedPostDisclosure.Good (insProject result.2.1).1))) <$>
      flagged pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
        qPost context material fits state] {true} := by
  classical
  rw [original_good pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor]
  exact augmented_bound pre application initial selector aux fixed writer prior key target nonce next mark sender route read monitor
    qPost context material fits state (fun result => decide (event (result.1, insProject result.2) ∧
      PqxdhSelectedPostDisclosure.Good (insProject result.2).1))

end BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.original_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.original_good
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.augmented_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.augmented_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.original_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.original_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostComparison.source_bound
