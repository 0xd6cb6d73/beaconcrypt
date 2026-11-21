import BeaconcryptCore.Computational.PqxdhServerAuthPublicationObservedCompiler
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationOwnerFamily
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrefixSource
import BeaconcryptCore.Computational.PqxdhServerAuthPublicationPrivacyResources
import BeaconcryptCore.Computational.PqxdhServerAuthentication

/-! Concrete authentication and unpublished-response losses for the original owner-indexed source experiment. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthPublicationComposition
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthSourceCosts
open PqxdhServerAuthBodyCosts PqxdhServerAuthGapDh PqxdhServerAuthAssumptions
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf CtxNonceAeadIntCtxt
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Recording the source journal and changing only its terminal observation retains the same constructed ordinary authentication reductions, with coefficient one. -/
theorem observer_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (Q : Nat) (j : Fin (Q + 1))
    (observer : PqxdhServerAuthObservedEntry.Observer) (fallback : ModifiedNonceAeadForgery)
    (H : Nat) (hashBound : (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute H) :
    (𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (RawCtxSelectedAuthenticationObserver.decision (RawCtxUniversalDecoder.decoder codec.frameRead)
        (PqxdhServerAuthPublicationObservedCompiler.client setup codec checks adversary Q j observer))] {true}).toReal ≤
      PqxdhServerAuthCtxObserverEvent.ctxLoss setup codec checks adversary Q j fallback H := by
  rw [PqxdhServerAuthPublicationObservedCompiler.client_authentication]
  apply ENNReal.toReal_mono
    (PqxdhServerAuthCtxObserverEvent.ctxLoss_finite setup codec checks adversary Q j fallback H)
  have records := PqxdhServerAuthCtxExperiment.client_record_bills setup codec checks adversary Q j
  simpa only [Finset.sum_range_one, Nat.cast_one, PqxdhServerAuthCtxObserverEvent.ctxLossENN,
    PqxdhServerAuthCtxObserverEvent.validation, PqxdhServerAuthCtxObserverEvent.integrity] using
    RawCtxSelectedAuthenticationObserver.authentication_bound
      (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (PqxdhServerAuthCtxExperiment.client setup codec checks adversary Q j) H 1 1
      hashBound records.1 records.2 (by norm_num)

end BeaconcryptCore.Computational.PqxdhServerAuthPublicationComposition

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthPublicationComposition.observer_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthPublicationComposition.observer_bound
