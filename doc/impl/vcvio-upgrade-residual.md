# VCVio upgrade residual after the deprecation migration (2026-10-21)

The VCVio deprecation migration ([plan](vcvio-deprecation-migration-plan.md), stages S0 to S9, 2026-10-19 to 2026-10-21) followed the deprecation warnings of the pinned VCVio `98dc1089` without changing VCVio, Lean, Mathlib or any other Lake package. Its final acceptance check (plan section 9, with item 4 of amendment A2, which the owner accepted on 2026-10-20) holds on the whole project at the end of stage S9: no VCVio deprecation warning, no deprecated notation or deprecation suppression outside the allowlisted `VCVioLegacyBridge`, no hand-written statement or definition body with a deprecated probability head outside the bridge, every change of a statement since the plan's base certified, no name that the plan forbids, and the backported laws of the shim modules replayed against the upstream VCVio build `afa6593f`. This report lists what the migration leaves for the actual VCVio upgrade (plan section 14). The record of the final check is [the staged verification record](staged-verification-record.md#vcvio-deprecation-migration-final-sweep-and-acceptance-check-2026-10-21) and the receipt `proof-receipts/vcvio-deprecations-s9.json`.

## Steps of the upgrade

The upgrade bumps the two manifest revisions of VCVio and its dependencies, deletes the bodies of the shim modules `VCVioForwardEvalDist`, `VCVioForwardOracleComp`, `VCVioForwardProbabilityTheory` and `VCVioForwardProgramLogic` (their statements carry upstream's names, so the upstream declarations take their place) and the bridge `VCVioLegacyBridge` with every use of it, replaces the dependencies listed below, and updates the control files, the inventory and the trust boundary. Statement text written in the forward vocabulary (`Pr{…}[…]`, `EvalDistEq`, `𝒟[…]`) is expected to stay unchanged. Every replacement name of the survey of the pin that the project uses, 51 VCVio constants, exists at upstream `afa6593f` (closing checks of phase B, [record](staged-verification-record.md#vcvio-deprecation-migration-closing-checks-of-phase-b-stage-pb-2026-10-21)), so no forward name needs renaming. The names carry over, not necessarily their statements: 27 of the 51 have a different type upstream, and ten of these also different binders, nine only in instance binders and `OracleComp.evalDist_query_uniform` by one more implicit binder after its explicit argument, so all 51 keep the number and order of their explicit arguments; the upgrade build rechecks every use ([review fixes](staged-verification-record.md#vcvio-deprecation-migration-closing-checks-of-phase-b-stage-pb-review-fixes-2026-10-21)).

## Recorded dependencies on the deprecated layer

A probe of the constants used by every declaration of the project finds 321 declarations outside the bridge that still reference deprecated constants (2020 uses): deprecated VCVio constants, VCVio constants stated in the deprecated form, or deprecated Lean core lemmas. 40 of them are in the Lean model and refinement modules and use only the Lean core lemmas `if_pos`, `if_neg`, `if_true` and `if_false`, whose deprecation is not VCVio's and is outside the migration. Each of the other 281 is recorded in the exception list of its stage (the stage receipts in `proof-receipts/`) or of the final sweep, because the dependency or the semantics it needs exists at the pin only in the deprecated form; the proofs reach the deprecated statements through the bridge. By class:

| Class | Declarations | Modules |
| --- | ---: | ---: |
| total variation | 134 | 76 |
| expectation | 90 | 5 |
| relational | 29 | 26 |
| adapter | 14 | 6 |
| total variation + relational | 12 | 11 |
| facade-stated dependency | 2 | 1 |

- Expectation: `OracleComp.EvalDist.expectedValue`, the pin's expectation of a function of a computation, is defined from the deprecated subprobability distributions, has no forward counterpart at the pin and is removed upstream; its laws relating it to probabilities are stated in the deprecated form.
- Total variation: `tvDist` is defined at the pin from the deprecated output distributions and has no forward counterpart there; the laws relating it to probabilities, VCVio's identical-until-bad bounds and the Boolean advantage bound are stated only in the deprecated form.
- Relational: the coupling laws of VCVio's relational program logic (`RelTriple`) relate a coupling only to the deprecated output distributions or event probabilities, and the pin defines a coupling over the deprecated subprobability distributions.
- Adapter: the stateful good-event theorem `StatefulGoodEvent.event_good` and its users are stated with the pin's subprobability adapter semantics for an arbitrary uniform oracle specification, the only semantics the pin has there (amendment A2 items 1 and 3). The three random-oracle bounds of `CtxRomAuth` (`ctxAliasGameProbability_le_cacheHit_add_inv`, `ctxFreshAliasGame_le_inv` and `ctxFreshAliasVerifier_le_inv`) rest on the same adapter semantics for the CTX random oracle `CtxRO`, whose answers carry no measurable structure at the pin (amendment A2 item 1).
- Facade-stated dependency: VCVio's binding bounds `binding_bound` and `binding_bound_via_cr_chain` (examples library) are stated in the deprecated form; `VCVioFeasibility` derives its forward statements from them through the bridge.

The declarations, by module:

- `AdaptiveCtxAliasCoupling` (relational, total variation): `canonical_replay_distance_bound`, `flagged_bad_eq`, `flagged_distance_bound`, `retained_distance_bound`, `source_distance_bound`
- `AdaptiveCtxIndependent` (total variation): `uniformIndependentGame_bound_and_query_accounting`, `uniformIndependentGame_distance_le_intctxt_sum`
- `AdaptiveCtxPrefix` (relational, total variation): `canonicalGame_distance_le_prefix`, `flaggedGame_bad_eq`, `flaggedGame_distance_le_prefix`, `retainedRoutedGame_distance_le_prefix`, `retainedRoutedGame_distance_le_prefix_add_intctxt`
- `AdaptiveCtxPrefixValidation` (total variation): `canonical_distance_le_indDollar_add_two_intctxt`, `independent_prefix_le_indDollar_add_intctxt`, `probEvent_le_add_ofReal_tvDist`, `routed_distance_le_indDollar_add_two_intctxt`
- `AdaptiveCtxPrivacyGuard` (total variation): `canonical_replay_advantage_bound`
- `AdaptiveCtxReceive` (total variation): `uniformLinkedGame_distance_le_intctxt_sum`
- `AdaptiveCtxRetainedKey` (total variation): `retainedAdaptiveGame_distance_le_bad`, `retainedAdaptiveGame_distance_le_intctxt_sum`, `retainedIndependentGame_distance_le_intctxt_sum`, `retainedLinkedGame_distance_le_intctxt_sum`
- `AdaptiveRawKeyFamily` (total variation): `selected_integrity_bound`
- `AdaptiveRawKeyPreparation` (total variation): `prepared_integrity_bound`
- `AdaptiveRawKeySelection` (total variation): `selected_integrity`
- `AdaptiveRawMultiKeyIntegrity` (total variation): `hop_bound`, `hop_distance`
- `AdaptiveRawNonceAead` (relational, total variation): `adaptiveGame_bad_eq`, `adaptiveGame_distance_le_discrepancy`, `uniformAdaptiveGame_distance_le_bad`, `uniformAdaptiveGame_distance_le_intctxt_sum`, `uniformAdaptiveGame_distance_le_raw_count`
- `CtxComputationalPrivacy` (relational, total variation): `ctxPrivacyIndependent_badProbability_eq_secretPrefix`, `ofReal_ctxPrivacyAdvantage_le_viewAdvantage_add_secretPrefix`, `tvDist_ctxPrivacyRealExpInner_directSample_le_secretPrefix`, `tvDist_ctxPrivacyRealGame_directSample_le_secretPrefix`, `tvDist_ctxPrivacySplitRouted_independentTag_le_secretPrefix`
- `CtxComputationalSecurity` (total variation): `ctxClassifiedForgeryGame_le_direct_add_prefix`, `ctxTypedFullFreshForgeryGame_le_direct_add_prefix`
- `CtxHonestTagSampling` (total variation): `tvDist_ctxSplitBeforeVerifyGame_directSampleIndependentTagGame_le_secretPrefixQueried`
- `CtxIndependentTags` (relational, total variation): `tvDist_ctxSplitBeforeVerifyGame_independentTagGame_le_secretPrefixQueried`, `tvDist_ctxSplitBeforeVerifyInner_independentTag_le_secretPrefixQueried`, `tvDist_ctxSplitRoutedBeforeVerifyInner_independentTag_le_secretPrefixQueried`, `tvDist_ctxSplitRouted_independentTag_le_prefixBad`, `tvDist_ctxSplitRouted_independentTag_le_prefixBad_of_main`
- `CtxNonceAeadIndDollar` (relational): `ctxIndependent_badProbability_eq_prefixBad`
- `CtxPrefixIsolation` (relational, total variation): `tvDist_ctxBeforeVerifyGame_prefixIsolatedGame_le_secretPrefixQueried`, `tvDist_ctxBeforeVerifyInner_prefixIsolated_le_secretPrefixQueried`, `tvDist_ctxReal_prefixIsolated_le_prefixBad`, `tvDist_ctxReal_prefixIsolated_le_secretPrefixQueried`
- `CtxRomAuth` (adapter): `ctxAliasGameProbability_le_cacheHit_add_inv`, `ctxFreshAliasGame_le_inv`, `ctxFreshAliasVerifier_le_inv`
- `CtxUnclaimedAcceptance` (total variation): `acceptedGame_le_direct_add_prefix`
- `PqxdhAuthenticatedRootCorrectness` (total variation): `after_bound`, `main_bound`, `prepared_bound`, `average_supported`
- `PqxdhAuthenticatedRootEndpoint` (total variation): `actual_routed_bound`
- `PqxdhAuthenticatedRootSource` (total variation): `authentication_hop`
- `PqxdhCorrelatedRootSource` (total variation): `authentication_hop`
- `PqxdhDeploymentHeadlineCtColl` (expectation): `ct_collision_game`, `triple_expect`
- `PqxdhDeploymentHeadlineCtGhost` (expectation): `acceptEnc_expect`, `create_expect`, `expectedValue_const_mul`, `expectedValue_point`, `expectedValue_zero`, `expected_run_le`, `handlerG_expect`, `keyMass_pairHit_le`, `mass`, `mass.eq_1`, `pairHit`, `pairHit.eq_1`, `pairHit_mean`, `pairHit_raw`, `phi_enc`, `phi_key`, `point_le`, `prefixEnc_expect`, `triple_le`
- `PqxdhDeploymentHeadlineDctHash` (expectation): `beaconStep_coll`, `coll_world`, `draw_step`, `expected_countCoin`, `primitiveRun_step`, `primitive_step`, `quiet_step`, `serverStep_coll`, `world_step_coll`
- `PqxdhDeploymentHeadlineDctTable` (expectation): `ChargedD`, `ChargedG`, `ChargedN`, `ChargedR`, `ChargedX`, `chargedD_frame`, `chargedD_onNative`, `chargedG_acceptActive`, `chargedG_acceptStep`, `chargedG_bind`, `chargedG_buildHiddenC`, `chargedG_buildStepC`, `chargedG_coins`, `chargedG_finishChallenge`, `chargedG_finishStepC`, `chargedG_groupCE`, `chargedG_lift`, `chargedG_mono`, `chargedG_native`, `chargedG_nativeMap`, `chargedG_pure`, `chargedG_read`, `chargedG_run`, `chargedG_tailCE`, `chargedN_acceptLogged`, `chargedN_bind`, `chargedN_familyHmac`, `chargedN_frame`, `chargedN_mono`, `chargedN_pure`, `chargedN_romRootBytes`, `chargedN_run`, `chargedN_sourceRoot`, `chargedR_finish`, `chargedR_frame`, `chargedR_mono`, `chargedR_onShared`, `chargedX_onBase`, `chargedX_slotRunX`, `expected_frame`, `handler_charged`, `install_le`, `material_read`, `realRegAt_charged`, `ro_table`, `slot_read`, `split_keyHit`
- `PqxdhDeploymentHeadlineDctTools` (expectation): `average_mass`, `chance_le_expected`, `equalTo_draw`, `expected_fst`, `expected_run_bounded`, `hits_draw`, `hits_miss`, `mass`, `mass.eq_1`, `material_marginal`, `ro_coll`, `ro_hits`, `ro_size`
- `PqxdhDeploymentIdealGuess` (relational): `lawEq_until_stop`
- `PqxdhDeploymentLaterServerKemHop` (total variation): `advantage_error`, `real_error`
- `PqxdhExtractRomHiddenSuffix` (relational, total variation): `boolDistAdvantage_le_tvDist`, `flagged_tvDist`, `hidden_suffix_bound`, `prefix_tvDist`, `secret_tvDist`, `tvDist_bind_le_probEvent`
- `PqxdhFirstBeaconRecordIntegrity` (total variation): `map_le_tvDist`, `post_le_full`
- `PqxdhFirstRecordFinishBound` (relational): `aug_hit`
- `PqxdhFirstRecordNonceStop` (total variation): `source_history_distance`, `source_input_distance`
- `PqxdhFirstRecordStopTagged` (relational): `bind_event_le`, `coupled_bound`, `post_bound`, `support_right`
- `PqxdhGeneratedPhase1Prefix` (total variation): `authentication_continuation_bound`
- `PqxdhGeneratedRootSource` (total variation): `authentication_hop`
- `PqxdhHiddenRoot` (relational, total variation): `hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add`, `hiddenRootProgrammed_tracking_tvDist_le_bad`, `hiddenRootProgrammed_tracking_tvDist_le_programmedBad`, `jointKdfSingletonProgrammed_tracking_probEvent_bad_eq`, `jointKdfSingletonProgrammed_tracking_tvDist_le_bad`, `tvDist_bind_left_le_probEvent_bind`, `tvDist_hiddenRootSharedRandomGame_independentGame_le`
- `PqxdhInitialAliasBound` (total variation): `cut_bound`, `cut_distance`, `pointwise`
- `PqxdhInitialAliasEvent` (total variation): `bound`
- `PqxdhInitialCurrentAliases` (total variation): `random_bound`
- `PqxdhInitialHalfCheckedFreshness` (total variation): `proxy_bound`
- `PqxdhInitialHalfPrivateObserver` (total variation): `distance`
- `PqxdhInitialNativeAdjacent` (total variation): `adjacent_bound`, `normalization`, `normalization_after`
- `PqxdhInitialParentObserverAliases` (total variation): `distance`
- `PqxdhInitialParentPrivateObserver` (total variation): `distance`
- `PqxdhInitialParentStoppedHop` (total variation): `local_bound`
- `PqxdhInitialPrivateCheckedFreshness` (total variation): `proxy_bound`
- `PqxdhInitialRootAliases` (total variation): `distance`
- `PqxdhInitialRootEventSource` (total variation): `authentication_hop`
- `PqxdhInitialSampledSourceEndpoints` (total variation): `local_random`
- `PqxdhInitialSourceExperiment` (total variation): `normalization`
- `PqxdhInitialSourceLaterMixture` (total variation): `supported_event_bound`
- `PqxdhInitializerSecrecy` (total variation): `initializerSharedRoot_independentRoot_advantage_le`, `tvDist_initializerSharedRoot_independentRoot_le`
- `PqxdhKemCorrectnessError` (total variation): `continuation_bound`, `routed_bound`
- `PqxdhKemCorrectnessStopped` (total variation): `after_bound`, `prepared_bound`, `stopped_bound`
- `PqxdhLaterChallengeEarlyConsumer` (relational): `same_continuation`
- `PqxdhLaterChallengeGeneratedBeforeObservation` (relational): `observed`
- `PqxdhLaterChallengePrefixMass` (relational): `prepared_before`
- `PqxdhLaterChallengeRandomConsumer` (relational): `same_continuation`
- `PqxdhPhase2GeneratedDriverBounds` (total variation): `authentication_continuation_bound`
- `PqxdhPrivateAcceptedRoot` (total variation): `authentication_hop`
- `PqxdhPrivatePhase1Prefix` (total variation): `authentication_continuation_bound`
- `PqxdhPrivateRootSource` (total variation): `authentication_hop`
- `PqxdhRecordFactsOriginMuteAdaptive` (adapter, relational, total variation): `bad_probability`, `complete_distance`, `event_good`, `marked_distance`, `source_distance`
- `PqxdhRegistrationJointKemRawGame` (total variation): `advantageRaw_error`, `branchRaw_real_error`
- `PqxdhSelectedPostCompiler` (total variation): `source_distance`
- `PqxdhServerAuthEntryBound` (relational): `bool_probability_le`
- `PqxdhServerAuthEntryFlat` (relational): `gameState_le_real`
- `PqxdhServerAuthEntrySimulation` (relational): `probEvent_le_until_bad`
- `PqxdhServerAuthEntryState` (relational): `relTriple_with_support`
- `PqxdhServerAuthEntryTable` (relational): `flat_step_projection`
- `PqxdhServerAuthObservedExecution` (relational): `native_flat`
- `PqxdhServerAuthObservedGame` (relational): `observed_flat`
- `PqxdhServerAuthObservedNative` (relational): `native_game_source`
- `PqxdhServerAuthObservedSchedule` (relational): `source_real_coupling`
- `PqxdhServerAuthPublicationObservedCompiler` (relational): `client_event`
- `PqxdhServerAuthStopMonitor` (relational): `client_event`
- `PqxdhStatefulPhase1Authentication` (total variation): `continuationAdvantage_le_bad`, `privateContinuationAdvantage_le_eufCma`
- `RawCtxAdjacentCacheNormalization` (total variation): `adjacent_bound`, `normalization`, `normalization_after`
- `RawCtxFlaggedQueryAgreement` (adapter): `event_good`
- `RawCtxFlaggedQueryTrace` (total variation): `distance`
- `RawCtxSelectedAliasCompiler` (total variation): `source_distance`
- `RawCtxSelectedAliasCoupling` (relational, total variation): `marked_distance`, `recorded_distance`
- `RawCtxSelectedAliasCut` (total variation): `cut_bound`, `cut_distance`, `pointwise`
- `RawCtxSelectedAliasInitial` (total variation): `marked_distance_initial`, `recorded_distance_initial`
- `RawCtxSelectedAliasPrimitives` (total variation): `recorded_distance`
- `RawCtxSelectedConfidentialityObserver` (total variation): `stopped_distance`
- `RawCtxSelectedFamilyNonceCoupling` (relational, total variation): `executable_distance`, `marked_distance`, `source_distance`, `unmarked_distance`
- `RawCtxSelectedInitialMask` (total variation): `distance`
- `RawCtxSelectedKeyProbes` (total variation): `canonical_prefix_bound`
- `RawCtxSelectedLiveAliases` (total variation): `exposure_alias_distance`, `exposure_distance_initial`, `native_distance`, `source_distance`
- `RawCtxSelectedLiveEvents` (adapter, total variation): `event_good`, `good_alias_bound`
- `RawCtxSelectedLiveSource` (total variation): `source_exposure_distance`
- `RawCtxSelectedLiveTrace` (relational, total variation): `exposure_distance`, `exposure_probability`
- `RawCtxSelectedNativeFreshLift` (total variation): `mass_tv`, `native_event_bound`
- `RawCtxSelectedNonceSourceEvent` (total variation): `executable_distance`
- `RawCtxSelectedParentAliases` (total variation): `distance`
- `RawCtxSelectedParentLive` (adapter): `event_good`
- `RawCtxSelectedParentPrivate` (total variation): `distance`
- `RawCtxSelectedParentPrivateEvents` (total variation): `local_bound`
- `RawCtxSelectedParentReadMask` (total variation): `alias_distance`
- `RawCtxSelectedSourceSendInputs` (total variation): `executable_distance`
- `StatefulGoodEvent` (adapter): `event_good`, `event_good._simp_1_1`, `event_good._simp_1_2`, `output_good`, `output_bad_zero`, `output_good_false`, `output_good_false._simp_1_1`
- `VCVioFeasibility` (facade-stated dependency): `ctx_binding_bound`, `ctx_binding_bound_tight`

## Statements that use the subprobability layer without a deprecated head

Amendment A2 item 4 counts deprecated statement heads in the final check and lists the statements that reference `SPMF` only through the pin's non-deprecated subprobability API (total variation, which also bounds the Boolean advantage, and expectations) or through the adapter instance. There are 163 such hand-written declarations; by module: `AdaptiveCtxAliasCoupling` 4, `AdaptiveCtxIndependent` 2, `AdaptiveCtxPrefix` 4, `AdaptiveCtxPrefixValidation` 3, `AdaptiveCtxReceive` 1, `AdaptiveCtxRetainedKey` 4, `AdaptiveRawKeyFamily` 1, `AdaptiveRawKeyPreparation` 1, `AdaptiveRawKeySelection` 1, `AdaptiveRawMultiKeyIntegrity` 1, `AdaptiveRawNonceAead` 4, `CtxComputationalPrivacy` 3, `CtxHonestTagSampling` 1, `CtxIndependentTags` 5, `CtxPrefixIsolation` 4, `CtxRomAuth` 1, `PqxdhAuthenticatedRootCorrectness` 4, `PqxdhDeploymentHeadlineCtColl` 1, `PqxdhDeploymentHeadlineCtGhost` 15, `PqxdhDeploymentHeadlineDctHash` 8, `PqxdhDeploymentHeadlineDctTable` 12, `PqxdhDeploymentHeadlineDctTools` 12, `PqxdhDeploymentLaterServerKemHop` 1, `PqxdhExtractRomHiddenSuffix` 5, `PqxdhFirstBeaconRecordIntegrity` 1, `PqxdhFirstRecordNonceStop` 2, `PqxdhGeneratedPhase1Prefix` 1, `PqxdhHiddenRoot` 5, `PqxdhInitialAliasBound` 3, `PqxdhInitialHalfPrivateObserver` 1, `PqxdhInitialNativeAdjacent` 2, `PqxdhInitialParentObserverAliases` 1, `PqxdhInitialParentPrivateObserver` 1, `PqxdhInitialRootAliases` 1, `PqxdhInitialSourceExperiment` 1, `PqxdhInitializerSecrecy` 1, `PqxdhKemCorrectnessError` 2, `PqxdhKemCorrectnessStopped` 3, `PqxdhPhase2GeneratedDriverBounds` 1, `PqxdhPrivatePhase1Prefix` 1, `PqxdhRecordFactsOriginMuteAdaptive` 3, `PqxdhRegistrationJointKemRawGame` 1, `PqxdhSelectedPostCompiler` 1, `RawCtxAdjacentCacheNormalization` 2, `RawCtxFlaggedQueryTrace` 1, `RawCtxSelectedAliasCompiler` 1, `RawCtxSelectedAliasCoupling` 2, `RawCtxSelectedAliasCut` 3, `RawCtxSelectedAliasInitial` 2, `RawCtxSelectedAliasPrimitives` 1, `RawCtxSelectedFamilyNonceCoupling` 4, `RawCtxSelectedInitialMask` 1, `RawCtxSelectedLiveAliases` 4, `RawCtxSelectedLiveSource` 1, `RawCtxSelectedLiveTrace` 1, `RawCtxSelectedNativeFreshLift` 1, `RawCtxSelectedNonceSourceEvent` 1, `RawCtxSelectedParentAliases` 1, `RawCtxSelectedParentPrivate` 1, `RawCtxSelectedParentReadMask` 1, `RawCtxSelectedSourceSendInputs` 1, `StatefulGoodEvent` 4. The full list is in the S9 receipt (`final_acceptance.G3.spmf_only`). Three helpers that Lean generated for the `simp` steps of the recorded adapter proofs in `StatefulGoodEvent` (`event_good._simp_1_1`, `event_good._simp_1_2` and `output_good_false._simp_1_1`) state the bridge's equations and so mention the deprecated heads; they disappear with the bridge. The Boolean advantage `ProbComp.boolDistAdvantage` itself is defined at the pin from the measure-valued interface; it is upgrade residual because upstream removes it (table below), not because of the subprobability layer.

## VCVio names in statements that upstream removed or changed

The statements and definition bodies of the project outside the shim and bridge modules use 41 VCVio or PolyFun names that upstream `afa6593f` no longer has, and 12 whose upstream type differs from the pin's. They are not deprecated at the pin, so following the warnings does not reach them (plan section 10). Number of declarations that use each:

| Name | Declarations | Upstream |
| --- | ---: | --- |
| `OracleSpec.IsUniformMeasureSpec.toIsMeasureSpec` | 1887 | removed |
| `OracleSpec.IsUniformMeasureSpec.unifSpec` | 1883 | removed |
| `ProbComp.boolDistAdvantage` | 379 | removed |
| `OracleSpec.instIsUniformSpecNatUnifSpec` | 281 | removed |
| `OracleSpec.IsUniformSpec.toIsProbabilitySpec` | 169 | removed |
| `PFunctor.FreeM.instMonadLiftTPMF` | 169 | removed |
| `SPMF` | 169 | removed |
| `SPMF.instMonadLiftPMF` | 169 | removed |
| `tvDist` | 110 | removed |
| `OracleComp.EvalDist.expectedValue` | 51 | removed |
| `OracleSpec.instDecidableEqOfFnOfDecidableEq` | 18 | removed |
| `OracleSpec.IsUniformSpec` | 14 | removed |
| `OracleSpec.instDecidableEqRangeOfDecidableEq` | 13 | removed |
| `SignatureAlg.unforgeableAdv.advantage` | 9 | removed |
| `OracleSpec.instFintypeOfFnOfFintype` | 8 | removed |
| `instEvalDistSemanticsOfMonadLiftTSPMF` | 8 | removed |
| `SignatureAlg.unforgeableExp` | 6 | removed |
| `OracleSpec.instFintypeRangeOfFintype` | 5 | removed |
| `SignatureAlg.unforgeableAdv` | 5 | removed |
| `instIsUniformSpecProdCMOracle` | 5 | removed |
| `OracleSpec.IsUniformSpec.ofFintypeInhabited` | 4 | removed |
| `OracleSpec.instInhabitedOfFnOfInhabited` | 4 | removed |
| `OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec` | 4 | removed |
| `SignatureAlg.unforgeableAdv.main` | 4 | removed |
| `SignatureAlg.unforgeableAdv.mk` | 3 | removed |
| `KEMScheme.CorrectExp` | 2 | removed |
| `MeasureSemanticsVia.mk` | 2 | removed |
| `OracleSpec.DecidableEq` | 2 | removed |
| `OracleSpec.instDecidableEqSumHAdd` | 2 | removed |
| `probOutput` | 2 | removed |
| `CollisionResistance.crExp` | 1 | removed |
| `CollisionResistance.crExp.match_1` | 1 | removed |
| `KEMScheme.CorrectExp.match_1` | 1 | removed |
| `KEMScheme.CorrectExp.match_3` | 1 | removed |
| `MeasureSemanticsVia.evalDist` | 1 | removed |
| `OracleSpec.Inhabited` | 1 | removed |
| `OracleSpec.Inhabited.mk` | 1 | removed |
| `OracleSpec.IsUniformSpec.fintype` | 1 | removed |
| `SignatureAlg.unforgeableExp.match_1` | 1 | removed |
| `bindingGame` | 1 | removed |
| `probEvent` | 1 | removed |
| `PFunctor.FreeM.instEvalDistSemanticsFreeM` | 1887 | type changed |
| `OracleComp.ProgramLogic.Relational.RelTriple` | 116 | type changed |
| `KEMScheme.IND_CCA_Advantage` | 90 | type changed |
| `OracleSpec.QueryLog.wasQueried` | 5 | type changed |
| `QueryImpl.StateOrnament` | 5 | type changed |
| `QueryImpl.StateOrnament.mk` | 5 | type changed |
| `MeasureTheory.Measure.boolDist` | 2 | type changed |
| `QueryImpl.withCachingTrackingPolicy` | 2 | type changed |
| `QueryImpl.withProgramming` | 2 | type changed |
| `KEMScheme.IND_CCA_Game` | 1 | type changed |
| `MeasureTheory.Measure.boolBias` | 1 | type changed |
| `ProbCompRuntime.mk` | 1 | type changed |

## Proof steps that depend on the pin's event notation

At the pin `Pr{let x ← mx}[p x]` is a macro for the point mass `𝒟[mx >>= fun x => pure (p x)] {True}`; upstream elaborates the same text to `prEvent ((fun x => p x) <$> mx)`. A proof step that rewrites the pin's expansion (a bind law such as `bind_assoc`, `pure_bind` or `bind_pure_comp` applied to the bind that the macro adds, a flattened law such as `OracleComp.prEvent_bind_mono_of_support` applied after that, or a full simplification that reaches it) passes at the pin and fails upstream, and since it names no removed constant, gate G5 and the proof residual below do not see it. The confirming review of stage S9 found such steps; its fixes added a probe of the elaborated proof terms (every application, in a declaration outside the shim and bridge modules, of a monad or functor law at the result type `Prop`, and every use of a law stated for `Prop`-valued computations). On the build of the S9 review fixes it found 56 such declarations, 19 in modules of stage S9 and 37 in modules of stages S2 and S4 to S8 (the same 37 at the base of stage S9); all were rewritten with the named laws on the computation, the point-mass forms or the event laws after a common draw, each replacement step shape compiles against the pin and against the upstream build `afa6593f`, and the probe of the final build finds none. What the probe cannot see stays for the upgrade build: a rewrite with a map law (`map_bind`, `Functor.map_map`) that upstream's final map of the event would also match, a full simplification whose upstream simp set differs, and a law about measures or about values in ℝ≥0∞ applied at `Prop`, whose conclusion is not an equation of computations. A broader probe run by the second confirming review of stage S9, which reports every law applied with a type argument instantiated at `Prop`, found, apart from four unrelated uses of vector lemmas at `Prop`, one step of the last kind: the bridge rewrite `VCVioLegacy.evalDist_singleton_eq_probOutput` in the final `simpa` of `PqxdhInitialSourceLaterMixture.supported_event_bound`, a declaration already recorded in the total-variation class above, which the upgrade rewrites anyway because the bridge is deleted. The record is [the staged verification record](staged-verification-record.md#vcvio-deprecation-migration-stage-s9-and-final-sweep-confirming-review-fixes-2026-10-21).

## Proof residual

Proofs of the project reference 90 VCVio or PolyFun constants that upstream no longer has, in 935 pairs of a module and a constant (gate G5 of the plan, which reports them without a pass criterion; driving them to zero is the upgrade's work). The most used are `ProbComp.boolDistAdvantage` (172 modules), `SPMF` (107 modules), `ProbComp.boolBiasAdvantage._proof_1` (99 modules), `tvDist` (77 modules), `ProbComp.boolDistAdvantage_triangle` (58 modules), `probOutput` (47 modules), `tvDist_map_le` (35 modules), `probEvent` (34 modules), `abs_probOutput_toReal_sub_le_tvDist` (31 modules), `evalSPMF` (28 modules), `tvDist_le_one` (12 modules), `ProbComp.boolDistAdvantage.eq_1` (11 modules), `OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad` (11 modules), `tvDist_nonneg` (10 modules), `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage` (10 modules). The full list is in the S9 receipt (`final_acceptance.G5_proofs`).

## Non-deprecated API removed upstream

Plan section 10 lists the API that upstream also removed without a deprecation at the pin: `ProbComp.boolDistAdvantage`, `OracleSpec.QueryCache` as a function, the discrete `tvDist`, `expectedValue`, the KEM advantage moving from ℝ to ℝ≥0∞, the binder changes of the relational program logic, 61 names renamed without aliases in upstream `967fdf2e` and five removed imported modules. The tables above show which of them reach statements; the rest is in the proof residual.

Twelve instances that the project's elaborated declarations use have no upstream declaration of the same name and are named neither above nor in the S9 receipt: `instDiscreteEvalDistCompatible`, `OracleSpec.IsUniformMeasureSpec.fintype`, `OracleSpec.IsUniformMeasureSpec.instCompatible`, `OracleSpec.IsUniformSpec.inhabited`, `OracleSpec.instDecidableEqDomainOfDecidableEq`, `OracleSpec.instIsUniformSpecAdd`, `PFunctor.FreeM.instLawfulMonadLiftTPMF`, `PFunctor.FreeM.instLawfulMonadLiftTSetM`, `PFunctor.FreeM.instMonadLiftTSetM`, `SampleableType.instFinite`, `SampleableType.instNonempty` and `SignatureAlg.instIsSubprobabilityMeasureBoolUnforgeableExp`. No Lean source of the project names them; Lean finds them by instance search, so the upgrade build either finds upstream instances in their place or reports the declarations where none applies ([review fixes of the closing checks](staged-verification-record.md#vcvio-deprecation-migration-closing-checks-of-phase-b-stage-pb-review-fixes-2026-10-21)).
