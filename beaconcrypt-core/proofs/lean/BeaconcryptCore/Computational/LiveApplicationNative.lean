import BeaconcryptCore.Computational.LiveApplicationObservation
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The public honest-application service is instantiated with the actual replicated Server/Beacon record, public fixed-HKDF, shared CTX and live-reveal interpreter. A private application has its own state and uniform oracle work. The complete joint initial sampler may correlate all states and its public context. The exact observation equality retains that sampler and every adaptive optional reply.

The native uniform ledger derives the source callback cap from the existing real-source bound and charges the private application separately. These equations do not supply registration/session creation, freshness, application-message secrecy or a symbolic trace simulation; those remain consuming interfaces. No snapshot or persistence operation occurs.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.LiveApplicationNative
open LiveApplicationObservation

abbrev NativeState (M P I D K A AppState : Type) (S B : Nat) :=
  SharedState (RawCtxProtocolReveals.State M P I D K S B) AppState
    (RawCtxSharedPrimitive.SharedState A)

variable {M P I D K A AppRequest AppState : Type} {S B : Nat}

noncomputable def impl
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp)) :
    QueryImpl (PublicSpec AppRequest S B) (StateT (NativeState M P I D K A AppState S B) ProbComp) :=
  publicImpl (sourceLift (RawCtxProtocolReveals.sourceImpl source writer S B sender route decode))
    (applicationLift application)

noncomputable def compiled
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp)) :
    QueryImpl (PublicSpec AppRequest S B) (StateT (NativeState M P I D K A AppState S B) ProbComp) :=
  let native : QueryImpl (SourceSpec S B) (StateT (NativeState M P I D K A AppState S B) ProbComp) :=
    sourceLift (RawCtxProtocolReveals.sourceImpl source writer S B sender route decode)
  let privateApplication : QueryImpl (ApplicationSpec AppRequest S B)
      (StateT (NativeState M P I D K A AppState S B) ProbComp) := applicationLift application
  (native + privateApplication) ∘ₛ lower

/-- Both presentations are exactly the same full-state native interface for every original, honest-application and network-delivery request. -/
theorem native_query
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp))
    (request : (PublicSpec AppRequest S B).Domain) :
    compiled (P := P) (I := I) (D := D) (K := K) (A := A) source writer sender route decode application request =
      impl source writer sender route decode application request :=
  lower_query _ _ request

/-- The same joint initial sampler, public initial context, adaptive decision and chronological observation log are preserved as complete evaluated distributions. -/
theorem native_observation {PublicContext Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp))
    (initial : ProbComp (PublicContext × NativeState M P I D K A AppState S B))
    (client : PublicContext → OracleComp (PublicSpec AppRequest S B) Result) :
    𝒮[(do let selected ← initial
           let observed ← publicObservation (compiled source writer sender route decode application)
             (client selected.1) selected.2
           pure (selected.1, observed))] =
      𝒮[(do let selected ← initial
             let observed ← publicObservation (impl source writer sender route decode application)
               (client selected.1) selected.2
             pure (selected.1, observed))] := by
  have exactImpl : compiled (P := P) (I := I) (D := D) (K := K) (A := A)
      source writer sender route decode application = impl source writer sender route decode application :=
    funext (native_query source writer sender route decode application)
  rw [exactImpl]

/-- Every actual source operation needs at most one 64-byte commitment miss; real public HKDF and reveal work retain their own source requests. -/
theorem source_uniform
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (request : (SourceSpec S B).Domain)
    (state : RawCtxProtocolReveals.State M P I D K S B × RawCtxSharedPrimitive.SharedState A) :
    ((RawCtxProtocolReveals.sourceImpl source writer S B sender route decode request).run state).IsTotalQueryBound 64 := by
  apply (RawCtxRevealBudgets.source_uniform_step source writer S B sender route decode request state).mono
  cases request with
  | inr request => simp [RawCtxRevealBudgets.weight]
  | inl request =>
      change RawCtxServerServiceBounds.uniformWeight 0 (RawCtxProtocolBudgets.sourceKind request) ≤ 64
      cases RawCtxProtocolBudgets.sourceKind request <;> decide

/-- The actual native public schedule charges at most 64 uniform calls per source request and the full private callback cap per honest request; logging and all rejection paths are included. -/
theorem observation_uniform {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp))
    (qApplication : Nat)
    (applicationBound : ∀ request state, ((application request).run state).IsTotalQueryBound qApplication)
    (client : OracleComp (PublicSpec AppRequest S B) Result)
    (qPublic qHonest : Nat) (bounded : client.IsTotalQueryBound qPublic)
    (honestBound : client.IsQueryBoundP AsksApplication qHonest)
    (state : NativeState M P I D K A AppState S B) :
    (publicObservation (impl source writer sender route decode application) client state).IsTotalQueryBound
      (qPublic * 64 + qHonest * qApplication) := by
  have bound := public_schedule_bound
    (RawCtxProtocolReveals.sourceImpl source writer S B sender route decode) application
    (fun _ => True) 64 qApplication
    (fun request state => (source_uniform source writer sender route decode request state).isQueryBoundP)
    (fun request state => (applicationBound request state).isQueryBoundP)
    client qPublic qHonest bounded honestBound state
  have logged := (public_observation_bound (impl source writer sender route decode application)
    client state (fun _ => True) (qPublic * 64 + qHonest * qApplication)).mpr bound
  simpa only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, if_true] using logged

/-- The complete experiment additionally pays every query of its actual joint initial sampler; no ambient role, application or primitive preparation is free. -/
theorem initial_uniform {PublicContext Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (application : QueryImpl (ApplicationSpec AppRequest S B) (StateT AppState ProbComp))
    (initial : ProbComp (PublicContext × NativeState M P I D K A AppState S B))
    (qInitial qApplication qPublic qHonest : Nat) (initialBound : initial.IsTotalQueryBound qInitial)
    (applicationBound : ∀ request state, ((application request).run state).IsTotalQueryBound qApplication)
    (client : PublicContext → OracleComp (PublicSpec AppRequest S B) Result)
    (bounded : ∀ context, (client context).IsTotalQueryBound qPublic)
    (honestBound : ∀ context, (client context).IsQueryBoundP AsksApplication qHonest) :
    (do let selected ← initial
        let observed ← publicObservation (impl source writer sender route decode application)
          (client selected.1) selected.2
        pure (selected.1, observed)).IsTotalQueryBound (qInitial + (qPublic * 64 + qHonest * qApplication)) := by
  apply isTotalQueryBound_bind initialBound
  intro selected
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    observation_uniform source writer sender route decode application qApplication applicationBound
      (client selected.1) qPublic qHonest (bounded selected.1) (honestBound selected.1) selected.2

end BeaconcryptCore.Computational.LiveApplicationNative

/-- info: 'BeaconcryptCore.Computational.LiveApplicationNative.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationNative.native_query
/-- info: 'BeaconcryptCore.Computational.LiveApplicationNative.native_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationNative.native_observation
/-- info: 'BeaconcryptCore.Computational.LiveApplicationNative.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationNative.source_uniform
/-- info: 'BeaconcryptCore.Computational.LiveApplicationNative.observation_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationNative.observation_uniform
/-- info: 'BeaconcryptCore.Computational.LiveApplicationNative.initial_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationNative.initial_uniform
