import BeaconcryptCore.Computational.RawCtxFreshChainCut

/-!
The actual complete established-owner continuation factors through the existing full-output secret-input game at exactly the supplied typed stopped sampler. The observer keeps the private rebased owner and shared primitive state and receives only the full challenge response; it does not receive the selected input or recursive root map. Its original API result is projected only after whole-state source equality.

The bound reuses the existing fixed-salt Extract experiment and ordinary two-query HMAC PRF game. No new primitive or protocol conclusion assumption is introduced. Its Extract term is measured at the stated joint sampler; an arbitrary sampler does not establish a small term or a reached native fresh-cut law. The random branch reuses one hidden full response while known inputs retain the actual function. Consistent aliases/public guesses, live reveal freshness and source selection accounting remain separate until explicitly linked. All optional source state effects remain, and source work versus challenger sampling needs separate accounting. Snapshot/persistence/restore services are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedChainGame
open RawCtxSelectedChain RawCtxFreshChainCut
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement

abbrev Context (Metadata Auxiliary : Type) :=
  RawCtxChainOwner.State Kernel Metadata × RawCtxSharedPrimitive.SharedState Auxiliary

def secretSampler {State : Type} (sample : ProbComp (State × RootOutput)) : ProbComp (State × Pqxdh.Bytes) :=
  (fun pair => (pair.1, pair.2.toList)) <$> sample

/-- The original owner starts at exactly the native interpretation of this stopped private state. -/
noncomputable def actualGame {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Bool)
    (sample : ProbComp (Context Metadata Auxiliary × RootOutput)) : ProbComp Bool := do
  let (context, target) ← sample
  let result ← (simulateQ (RawCtxMixedOwner.sourceImpl (RawCtxSourceMaterialLabels.nativeImpl source writer)
    senderId decode) client).run
      (RawCtxChainOwner.nativeState (nativeKernel (concreteChain target)) context.1, context.2)
  pure result.1

/-- Only the private rebased state and supplied full expansion enter the observer; no target input or recursive root interpretation is an argument. -/
noncomputable def observer {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Bool)
    (context : Context Metadata Auxiliary) (output : FullOutput) : ProbComp Bool := do
  let result ← (simulateQ (RawCtxChainOwner.sourceImpl
    (calls source writer (RawCtxKdfRequestTable.fullResponse output)) senderId decode) client).run context
  pure result.1

/-- Source byte conversion keeps the existing fixed ratchet label and every target input byte. -/
theorem source_address (target : RootOutput) :
    RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest (concreteChain target)) =
      FixedHkdfDomain.ratchet.address target.toList := by
  have info : absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
    simpa only [pqxdh.SYM_RATCHET_INFO] using absBytes_SYM_RATCHET_INFO
  simp [RawCtxKdfRequestTable.address, RawCtxChainSend.nativeRequest, FixedHkdfDomain.address,
    concreteChain, absBytes, List.map_map, Function.comp_def]
  exact info

/-- The actual full source continuation is exactly the existing secret-input experiment at this same stopped sampler. -/
theorem actual_eq_source {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Bool)
    (sample : ProbComp (Context Metadata Auxiliary × RootOutput)) :
    actualGame source writer senderId decode client sample =
      sourceFullGame source .ratchet (secretSampler sample) (observer source writer senderId decode client) := by
  simp only [actualGame, sourceFullGame, secretSampler, bind_map_left]
  refine bind_congr (fun pair => ?_)
  rw [RawCtxSelectedChain.source_schedule, bind_map_left]
  rw [← RawCtxKdfRequestTable.fullResponse_source source, source_address]
  rfl

/-- One full challenge response is reused for the selected private input; known-input evaluations still execute the fixed source. -/
noncomputable def randomGame {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Bool)
    (sample : ProbComp (Context Metadata Auxiliary × RootOutput)) : ProbComp Bool :=
  independentFullGame (secretSampler sample) (observer source writer senderId decode client)

/-- The same stopped source experiment uses the existing fixed-salt Extract endpoint and ordinary two-query HMAC PRF game. -/
theorem selected_bound {Metadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (senderId : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Bool)
    (sample : ProbComp (Context Metadata Auxiliary × RootOutput)) :
    (actualGame source writer senderId decode client sample).boolDistAdvantage
      (randomGame source writer senderId decode client sample) ≤
      (extractRealGame hmac (secretSampler sample)
        (fullExtractReduction hmac .ratchet (observer source writer senderId decode client))).boolDistAdvantage
        (extractUniformGame (secretSampler sample)
          (fullExtractReduction hmac .ratchet (observer source writer senderId decode client))) +
      (hmacPrfRealGame hmac
        (fullExpandReduction .ratchet (secretSampler sample) (observer source writer senderId decode client))).boolDistAdvantage
        (hmacPrfRandomGame
          (fullExpandReduction .ratchet (secretSampler sample) (observer source writer senderId decode client))) := by
  simpa only [actual_eq_source, randomGame] using sourceFullAdvantage_le_extract_add_hmac
    source hmac correct .ratchet (secretSampler sample) (observer source writer senderId decode client)

end BeaconcryptCore.Computational.RawCtxSelectedChainGame

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChainGame.source_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChainGame.source_address

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChainGame.actual_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChainGame.actual_eq_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChainGame.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChainGame.selected_bound
