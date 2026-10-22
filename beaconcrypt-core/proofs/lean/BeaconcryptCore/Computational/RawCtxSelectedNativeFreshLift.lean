import BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

/-!
The selected CTX comparison retains the original native event and original byte-based freshness predicate in the retained selected-KDF hybrid. The complete source distribution bound charges nonce refusal once; hidden disclosure is handled by the existing exact stopped-source theorem, not by changing the event or assuming the adversary's decision is false.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedFamilyNonceCoupling (Full SourceFull project optionalClient marked augmented nonceBad)
open RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals
variable {A M P I D K Result : Type} {S B : Nat}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def mass {X : Type} (event : X → Prop) (run : ProbComp X) : ENNReal :=
  𝒟[(fun result => decide (event result)) <$> run] {true}

/-- Every complete terminal decision is transported by the full-distribution bound, without a condition on the decision after compromise. -/
theorem mass_tv {X : Type} (event : X → Prop) (left right : ProbComp X) :
    mass event left ≤ mass event right + ENNReal.ofReal (discreteDistance left right) := by
  unfold mass
  repeat rw [← prEvent_eq_evalDist_singleton _ true]
  simp only [prEvent_map, decide_eq_true_eq]
  exact AdaptiveCtxPrefixValidation.probEvent_le_add_ofReal_tvDist left right event

noncomputable def nativeGame (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :=
  (simulateQ (RawCtxFunctionalFamily.backend source writer
      (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
    ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route read) client).run (nativeState key state.1))).run (project state).2

noncomputable def stoppedGame (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :=
  ((simulateQ (RawCtxSelectedMessageStopping.stopping
    (RawCtxSelectedMessageStopping.sourceRecord source writer prior parent key target nonce next sender route read)) client).run).run (project state)

def nativeFresh (key : RootOutput) (remaining disclosed : List RatchetChain)
    (event : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A → Prop)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A) : Prop :=
  event result ∧ RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) disclosed result.1.2.2

def stoppedFresh (key : RootOutput) (remaining disclosed : List RatchetChain)
    (event : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A → Prop) :
    Option Result × SourceFull M P I D K A S B → Prop :=
  RawCtxSelectedMessageStopping.completed (fun result => event (RawCtxSelectedMessageStopping.nativeOutput key result) ∧
    RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain key :: remaining) disclosed (interpretHistory key result.2.1.2))

/-- The unchanged native event and byte freshness have exactly the existing stopped-source probability, with every original private and public field retained. -/
theorem native_fresh (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (remaining disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B)
    (event : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A → Prop) :
    mass (nativeFresh key remaining disclosed event) (nativeGame source writer prior parent key target nonce next sender route read client state) =
      mass (stoppedFresh key remaining disclosed event) (stoppedGame source writer prior parent key target nonce next sender route read client state) := by
  unfold mass nativeGame nativeFresh stoppedGame stoppedFresh
  repeat rw [← prEvent_eq_evalDist_singleton _ true]
  simp only [prEvent_map, decide_eq_true_eq]
  exact RawCtxSelectedMessageStopping.native_event source writer prior parent key target nonce next remaining disclosed sender route read client (project state) event

noncomputable def compiledGame (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) :=
  RawCtxSelectedFamilyLiveCompiler.output <$>
    (RawCtxSelectedReceiveCompiler.evaluated source key read
      (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client state.1)).run state.2

noncomputable def nonceGame (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B) : ProbComp Bool :=
  (fun result => result.2.2) <$>
    (simulateQ (marked (augmented source writer prior parent key target nonce next sender route read)
      (nonceBad prior parent target nonce next sender)) (optionalClient client)).run (state, false)

/-- The unchanged original native event and byte freshness cost exactly the compiled event plus the same source run's selected-nonce refusal probability. There is no honest-session, no-compromise or nonce-freshness premise. -/
theorem native_event_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (remaining disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : Full M P I D K A S B)
    (event : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A → Prop) :
    mass (nativeFresh key remaining disclosed event) (nativeGame source writer prior parent key target nonce next sender route read client state) ≤
      mass (stoppedFresh key remaining disclosed event) (compiledGame source writer prior parent key target nonce next sender route read client state) +
        𝒟[nonceGame source writer prior parent key target nonce next sender route read client state] {true} := by
  rw [native_fresh]
  have cost : ENNReal.ofReal (discreteDistance
      (stoppedGame source writer prior parent key target nonce next sender route read client state)
      (compiledGame source writer prior parent key target nonce next sender route read client state)) ≤
      𝒟[nonceGame source writer prior parent key target nonce next sender route read client state] {true} :=
    (ENNReal.ofReal_le_ofReal (RawCtxSelectedFamilyNonceCoupling.executable_distance source writer prior parent key target nonce next sender route read client state)).trans ENNReal.ofReal_toReal_le
  exact (mass_tv (stoppedFresh key remaining disclosed event) _ _).trans (add_le_add le_rfl cost)

end BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.mass_tv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.mass_tv
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.native_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.native_fresh
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.native_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift.native_event_bound
