-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTaggedBuild
import BeaconcryptCore.Computational.CborTaggedOther
import BeaconcryptCore.Computational.CborPublicClient
/-! The normalized shared-writer handler equals fixed tagged-codec execution after local input tagging and response stripping, for every command and complete state. The actual raw registration build is a separate boundary. This wrapper still selects a pin from native state; the public client invariant is a separate join. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTaggedSimulation
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def boundaryWire (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) : Codec Reader Response :=
  PqxdhBoundaryRecordPrelude.withReader (CborProductionBoundary.wireCodec wire parse)
    (CborProductionBoundary.nativeReader parse)

noncomputable def fixed (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborCommandFilter.handler CborProductionBoundary.allowed CborProductionBoundary.reject
    (PqxdhDeploymentNative.handler setup (CborTaggedCodec.codec (boundaryWire wire parse)) checks
      (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed)

/-- A pure command adapter; its implementation stays opaque to the command partition proof. -/
noncomputable def adapt {State : Type}
    (next : QueryImpl Spec (StateT State ProbComp))
    (sender : Spec.Domain → State → Std.U64) : QueryImpl Spec (StateT State ProbComp)
  | .inr (.finish index raw) => CborCommandFilter.atState fun state =>
      next (.inr (.finish index (CborTaggedCodec.tag (sender (.inr (.finish index raw)) state) raw)))
  | .inr (.build index payload) => Option.map CborPublicClient.strip <$>
      next (.inr (.build index payload))
  | query => next query

noncomputable def handler (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  adapt (fixed setup wire parse checks seed) CborProductionBoundary.normalizationSender

theorem base_other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (other : CborTaggedOther.Other query) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup (CborTaggedCodec.codec (boundaryWire wire parse)) checks
      (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed query).run state =
      (CborProductionBoundary.normalizedBaseHandler setup wire parse checks seed query).run state := by
  have original := CborTaggedBuild.base_at setup wire parse checks seed query state
  have changed := congrArg (fun selected : Codec Reader Response =>
      (PqxdhDeploymentNative.handler setup selected checks
        (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed query).run state)
    (CborTaggedBuild.reader_codec (CborProductionBoundary.wireCodec wire parse)
      (CborProductionBoundary.nativeReader parse) (funext (CborProductionBoundary.decode_native parse))
      (CborProductionBoundary.normalizationSender query state)).symm
  have nativeSame := congrArg (fun work => work.run state)
    (CborTaggedOther.native_other setup (boundaryWire wire parse) checks
      (RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model) seed
      (CborProductionBoundary.normalizationSender query state) query other)
  exact nativeSame.trans (changed.trans original.symm)

theorem filter_congr {κ S : Type} {spec : OracleSpec κ}
    (allow : spec.Domain → S → Bool)
    (reject : (query : spec.Domain) → S → spec.Range query × S)
    (left right : QueryImpl spec (StateT S ProbComp)) (query : spec.Domain) (state : S)
    (same : (left query).run state = (right query).run state) :
    (CborCommandFilter.handler allow reject left query).run state =
      (CborCommandFilter.handler allow reject right query).run state := by
  cases admitted : allow query state <;>
    simp only [CborCommandFilter.handler, StateT.run, admitted, Bool.false_eq_true,
      ite_false, ite_true]
  exact same

theorem other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (other : CborTaggedOther.Other query) (state : PqxdhDeploymentNative.State KemSK) :
    (fixed setup wire parse checks seed query).run state =
      (CborProductionBoundary.normalizedHandler setup wire parse checks seed query).run state :=
  filter_congr CborProductionBoundary.allowed CborProductionBoundary.reject _ _ query state
    (base_other setup wire parse checks seed query other state)

theorem strip_mapped {S : Type} (sender : Std.U64)
    (work : ProbComp (Option PqxdhServerRegistrationPublication.Response × S)) :
    (fun result => (Option.map CborPublicClient.strip result.1, result.2)) <$>
      (fun result => ((CborResponseWriterMap.response (CborTaggedCodec.tag sender)) <$> result.1, result.2)) <$> work = work := by
  have inverse : (fun result : Option PqxdhServerRegistrationPublication.Response × S =>
      (Option.map CborPublicClient.strip ((CborResponseWriterMap.response (CborTaggedCodec.tag sender)) <$> result.1), result.2)) = id := by
    funext result
    rcases result with ⟨reply, state⟩
    cases reply <;> simp [CborPublicClient.strip_tag]
  simp only [Functor.map_map, inverse, id_map]

theorem build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (index : Nat) (payload : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (handler setup wire parse checks seed (.inr (.build index payload))).run state =
      (CborProductionBoundary.normalizedHandler setup wire parse checks seed (.inr (.build index payload))).run state := by
  simp only [handler, adapt, StateT.run_map]
  rw [show (fixed setup wire parse checks seed (.inr (.build index payload))).run state = _ from
    CborTaggedBuild.production_build setup wire parse checks seed readBack index payload state]
  exact strip_mapped _ _

theorem finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (index : Nat) (raw : Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (handler setup wire parse checks seed (.inr (.finish index raw))).run state =
      (CborProductionBoundary.normalizedHandler setup wire parse checks seed (.inr (.finish index raw))).run state := by
  simp only [handler, adapt, CborCommandFilter.atState_run]
  exact (CborCommandFilter.admitted_run CborProductionBoundary.allowed CborProductionBoundary.reject _ _ state rfl).trans
    (CborTaggedFinish.production_finish setup wire parse checks seed index raw state).symm

/-- Pointwise command laws determine the complete adapted handler without unfolding its implementation. -/
theorem adapt_exact {State : Type}
    (next target : QueryImpl Spec (StateT State ProbComp)) (sender : Spec.Domain → State → Std.U64)
    (built : ∀ index payload state,
      (adapt next sender (.inr (.build index payload))).run state =
        (target (.inr (.build index payload))).run state)
    (finished : ∀ index raw state,
      (adapt next sender (.inr (.finish index raw))).run state =
        (target (.inr (.finish index raw))).run state)
    (remaining : ∀ query, CborTaggedOther.Other query → ∀ state,
      (next query).run state = (target query).run state) : adapt next sender = target := by
  funext query state
  cases query
  case inl coin => exact remaining (.inl coin) True.intro state
  case inr command =>
    cases command
    case build index payload => exact built index payload state
    case finish index raw => exact finished index raw state
    all_goals apply remaining
    all_goals trivial

theorem handler_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse)) :
    handler setup wire parse checks seed = CborProductionBoundary.normalizedHandler setup wire parse checks seed := by
  exact adapt_exact (fixed setup wire parse checks seed)
    (CborProductionBoundary.normalizedHandler setup wire parse checks seed)
    CborProductionBoundary.normalizationSender
    (build setup wire parse checks seed readBack) (finish setup wire parse checks seed)
    (other setup wire parse checks seed)

theorem adaptive_exact {X : Type} (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack (boundaryWire wire parse))
    (work : OracleComp Spec X) (state : PqxdhDeploymentNative.State KemSK) :
    (simulateQ (handler setup wire parse checks seed) work).run state =
      (simulateQ (CborProductionBoundary.normalizedHandler setup wire parse checks seed) work).run state := by
  rw [handler_exact setup wire parse checks seed readBack]

end BeaconcryptCore.Computational.CborTaggedSimulation

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.base_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.base_other

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.filter_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.filter_congr

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.other

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.strip_mapped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.strip_mapped

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.build

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.finish

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.adapt_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.adapt_exact

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.handler_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.handler_exact

/-- info: 'BeaconcryptCore.Computational.CborTaggedSimulation.adaptive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedSimulation.adaptive_exact
