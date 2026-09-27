import BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks
import BeaconcryptCore.Computational.RawCtxPrefixKeyOrder

/-!
The saved source continuation uses an explicit sum of its original external callbacks and the dynamic CTX interface. External effects retain complete private state, root cache, chronological audit and unused private-table fields. Only the evaluated CTX interpreter receives the selected message key. The actual source callback instantiation is supplied separately; this generic wiring alone is not an independence or security assumption.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient
open PqxdhJointKdfGame PqxdhSecretInputKdf CtxRomAuth AdaptiveCtxSharedHash
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}

abbrev External (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  PqxdhInitialPendingPost.External extra RatchetChain I D K X Response Shared

abbrev Spec (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  External extra I D K X Response Shared + AdaptiveCtxDynamicKnownKeys.Spec

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

noncomputable def callback : QueryImpl (External extra I D K X Response Shared)
    (StateT (Local A N C) (OracleComp HashSpec))
  | .inr (.inr (.inl secrets)) => initialCall (initial secrets)
  | query => localCall (external pre application initial selector aux query)

noncomputable def lower : QueryImpl (Spec extra I D K X Response Shared)
    (StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
  | .inl query => fun state => simulateQ RawCtxSourceSharedRom.forward ((callback pre application initial selector aux query).run state)
  | .inr query => fun state => (fun reply => (reply, state)) <$> AdaptiveCtxDynamicKnownKeys.Spec.query query

/-- Local callbacks are exactly the original audited native callbacks, including the initializer's complete candidate append. -/
theorem local_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage S B : Nat)
    (query : (External extra I D K X Response Shared).Domain) :
    callback pre application initial selector aux query =
      compiler (S := S) (B := B) source writer stage pre application initial selector aux (.inr query) := by
  rcases query with query | (reply | (secrets | (query | query))) <;> rfl

/-- Interpreting the explicit local service retains the actual optional reply, full source state and initializer audit, while erasing only added CTX bookkeeping. -/
theorem callback_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage S B : Nat)
    (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (key : CtxKey)
    (query : (External extra I D K X Response Shared).Domain)
    (state : Local A N C) (before : AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result => (result.1.1, attach result.1.2 result.2.cache)) <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decode source.crypto key)
        ((lower pre application initial selector aux (.inl query)).run state)).run before =
      (PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage (fun request => localLift (pre request))
        (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
        (fun request => localLift (selector request)) (fun request => localLift (aux request)) (.inr query)).run
          (attach state before.cache) := by
  have original := PqxdhNativeSharedPrefix.step (S := S) (B := B) source writer stage pre application initial selector aux
    (.inr query) state before.cache
  rw [← local_native pre application initial selector aux source writer stage S B query] at original
  have forwarded := congrArg (Functor.map (fun result => (result.1.1, attach result.1.2 result.2)))
    (RawCtxSourceSharedRom.forward_cache real decode source.crypto key
      ((callback pre application initial selector aux query).run state) before)
  convert forwarded.trans original using 1
  simp only [lower, StateT.run, Functor.map_map]
  rfl

/-- Source-local callbacks cannot inspect or query the commitment ROM; their complete randomness remains explicit. -/
theorem callback_no_hash (query : (External extra I D K X Response Shared).Domain) (state : Local A N C) :
    ((callback pre application initial selector aux query).run state).IsQueryBoundP (HashClass true) 0 := by
  rcases query with query | (reply | (secrets | (query | query))) <;>
    simp only [callback, external, localCall, initialCall, StateT.run, isQueryBoundP_map_iff]
  all_goals exact RawCtxSelectiveSharedRom.coins_no_hash _

def cost (qPre qApplication qInitial qSelector qAux : Nat) : (External extra I D K X Response Shared).Domain → Nat
  | .inl _ => qPre
  | .inr (.inl _) => qApplication
  | .inr (.inr (.inl _)) => qInitial
  | .inr (.inr (.inr (.inl _))) => qSelector
  | .inr (.inr (.inr (.inr _))) => qAux

/-- Each external request pays its own complete source-local random-call allowance; the initializer audit adds no draw. -/
theorem callback_uniform (qPre qApplication qInitial qSelector qAux : Nat)
    (preBound : ∀ query state, ((pre query).run state).IsTotalQueryBound qPre)
    (applicationBound : ∀ reply state, ((application reply).run state).IsTotalQueryBound qApplication)
    (initialBound : ∀ secrets state, ((initial secrets).run state).IsTotalQueryBound qInitial)
    (selectorBound : ∀ query state, ((selector query).run state).IsTotalQueryBound qSelector)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (query : (External extra I D K X Response Shared).Domain) (state : Local A N C) :
    ((callback pre application initial selector aux query).run state).IsQueryBoundP (HashClass false)
      (cost qPre qApplication qInitial qSelector qAux query) := by
  rcases query with query | (reply | (secrets | (query | query))) <;>
    simp only [callback, external, localCall, initialCall, StateT.run, isQueryBoundP_map_iff, cost]
  all_goals apply RawCtxSelectiveSharedRom.coins_bound
  all_goals first | exact preBound _ _ | exact applicationBound _ _ | exact initialBound _ _ | exact selectorBound _ _ | exact auxBound _ _

/-- Lowering a source callback to the component pays its source coins and makes no hash, selected seal or raw-opening request. -/
theorem callback_bills (qPre qApplication qInitial qSelector qAux : Nat)
    (preBound : ∀ query state, ((pre query).run state).IsTotalQueryBound qPre)
    (applicationBound : ∀ reply state, ((application reply).run state).IsTotalQueryBound qApplication)
    (initialBound : ∀ secrets state, ((initial secrets).run state).IsTotalQueryBound qInitial)
    (selectorBound : ∀ query state, ((selector query).run state).IsTotalQueryBound qSelector)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (query : (External extra I D K X Response Shared).Domain) (state : Local A N C) :
    ((lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute 0 ∧
    ((lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute
      (cost qPre qApplication qInitial qSelector qAux query) ∧
    ((lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    ((lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  have bounded := callback_uniform pre application initial selector aux qPre qApplication qInitial qSelector qAux
    preBound applicationBound initialBound selectorBound auxBound query state
  exact RawCtxPrefixKeyOrder.forward_bills _ 0 _
    (callback_no_hash pre application initial selector aux query state) bounded

end BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.local_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.local_native

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_no_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_no_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedCallbackCompiler.callback_bills
