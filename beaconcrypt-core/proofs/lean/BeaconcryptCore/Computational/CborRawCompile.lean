-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborSplitCompiler
import BeaconcryptCore.Computational.CborRawCanonicalBuild
import BeaconcryptCore.Computational.CborTaggedSimulation
import BeaconcryptCore.Computational.CborPublicPin

/-! The raw registration source handler uses a fixed tagged logical codec for registration and the original optional codec for established records. The eight-byte tags are public proof representations, never native writes or additional oracle calls. The equations retain the existing source-model trust boundary and explicitly require canonical parser read-back and the existing AEAD body-length law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawCompile
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open CborRawCanonicalBuild (canonical CanonicalReadBack)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

noncomputable def sourceCodec (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) : Codec Reader (Std.U64 × Response) :=
  CborTaggedCodec.codec (canonical (boundaryWire wire parse))

theorem source_phase1 (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (native : PqxdhServerAuthNegativeControl.Phase1ReadBack (boundaryWire wire parse)) :
    PqxdhServerAuthNegativeControl.Phase1ReadBack (sourceCodec wire parse) := native

/-- The source codec's read-back law is derived from the native outer codec and canonical parsing, rather than supplied as a new representation-simulation premise. -/
theorem source_phase2 (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (native : PqxdhServerAuthNegativeControl.Phase2ReadBack (boundaryWire wire parse))
    (stable : CborRegistrationCodec.Stable (boundaryWire wire parse)) :
    PqxdhServerAuthNegativeControl.Phase2ReadBack (sourceCodec wire parse) :=
  CborTaggedCodec.phase2_readBack (canonical (boundaryWire wire parse)) native stable

def route (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) :
    RawCtxServerRouting.SenderDecoder :=
  RawCtxFrameDecoding.sender (CborProductionBoundary.nativeReader parse).model

noncomputable def fixed (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborSplitCompiler.nativeHandler setup (sourceCodec wire parse)
    (boundaryWire wire parse).frameRead wire.frameWrite checks (route parse) seed

noncomputable def stateful (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  CborTaggedSimulation.adapt (fixed setup wire parse checks seed) CborProductionBoundary.normalizationSender

theorem deployment_build_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto) (parser : CanonicalReadBack wire)
    (decoder : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (payload : Option Pqxdh.Bytes) (assigned : Nat)
    (admitted : CborSizing.responseLen ((payload.getD [0xff]).length + 88) assigned ≤ CborSizing.maxMessageSize)
    (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.handler setup
      (CborRegistrationCodec.normalize (canonical wire) state.native.shared.2.server.identityKeyId)
      checks decoder seed (.inr (.build session payload))).run state =
      (PqxdhDeploymentNative.handler setup (CborRegistrationCodec.raw wire)
        checks decoder seed (.inr (.build session payload))).run state := by
  change (fun result => (result.1, { state with native := result.2 })) <$>
    (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeBuild setup
      (CborRegistrationCodec.normalize (canonical wire) state.native.shared.2.server.identityKeyId)
      checks session payload)).run state.native =
    (fun result => (result.1, { state with native := result.2 })) <$>
      (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeBuild setup
        (CborRegistrationCodec.raw wire) checks session payload)).run state.native
  simp only [PqxdhRegistrationSchedule.onShared_run,
    CborRawCanonicalBuild.native_build_raw setup wire checks lengths parser session payload assigned admitted]

theorem filter_congr_when_allowed {κ S : Type} {spec : OracleSpec κ}
    (allow : spec.Domain → S → Bool)
    (reject : (query : spec.Domain) → S → spec.Range query × S)
    (left right : QueryImpl spec (StateT S ProbComp)) (query : spec.Domain) (state : S)
    (same : allow query state = true → (left query).run state = (right query).run state) :
    (CborCommandFilter.handler allow reject left query).run state =
      (CborCommandFilter.handler allow reject right query).run state := by
  cases admitted : allow query state <;>
    simp only [CborCommandFilter.handler, StateT.run, admitted, Bool.false_eq_true, ite_false, ite_true]
  exact same admitted

theorem normalized_build_raw (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (CborProductionBoundary.normalizedHandler setup (canonical wire) parse checks seed
      (.inr (.build session payload))).run state =
      (CborProductionBoundary.handler setup wire parse checks seed (.inr (.build session payload))).run state := by
  apply filter_congr_when_allowed CborProductionBoundary.allowed CborProductionBoundary.reject
    (CborProductionBoundary.normalizedBaseHandler setup (canonical wire) parse checks seed)
    (CborProductionBoundary.baseHandler setup wire parse checks seed) (.inr (.build session payload)) state
  intro admitted
  have fits : CborSizing.responseLen ((payload.getD [0xff]).length + 88)
      (state.native.shared.2.server.control.last_key_id.val + 1) ≤ CborSizing.maxMessageSize :=
    of_decide_eq_true admitted
  rw [CborTaggedBuild.base_at]
  simp only [CborProductionBoundary.codec]
  rw [CborTaggedBuild.reader_codec (CborProductionBoundary.wireCodec (canonical wire) parse)
    (CborProductionBoundary.nativeReader parse) (funext (CborProductionBoundary.decode_native parse))]
  simp only [CborProductionBoundary.baseHandler, CborCommandFilter.atState_run,
    CborProductionBoundary.commandCodec, CborProductionBoundary.normalizationSender]
  exact deployment_build_raw setup (boundaryWire wire parse) checks lengths parser (route parse) seed session
    payload (state.native.shared.2.server.control.last_key_id.val + 1) fits state

/-- A raw build makes the optional real outer write once and retains every failure poststate; the proof envelope is then removed before replying to the native caller. -/
theorem build (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : PqxdhDeploymentNative.State KemSK) :
    (stateful setup wire parse checks seed (.inr (.build session payload))).run state =
      (CborProductionBoundary.handler setup wire parse checks seed (.inr (.build session payload))).run state := by
  simp only [stateful, CborTaggedSimulation.adapt, StateT.run_map]
  rw [show (fixed setup wire parse checks seed (.inr (.build session payload))).run state = _ from
    CborTaggedBuild.production_build setup (canonical wire) parse checks seed
      (CborRawCanonicalBuild.frame_readBack (boundaryWire wire parse) parser) session payload state]
  exact (CborTaggedSimulation.strip_mapped state.native.shared.2.server.identityKeyId
    ((CborProductionBoundary.normalizedHandler setup (canonical wire) parse checks seed
      (.inr (.build session payload))).run state)).trans
      (normalized_build_raw setup wire parse checks lengths parser seed session payload state)

theorem finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhDeploymentNative.State KemSK) :
    (stateful setup wire parse checks seed (.inr (.finish index raw))).run state =
      (CborProductionBoundary.handler setup wire parse checks seed (.inr (.finish index raw))).run state := by
  exact CborTaggedSimulation.finish setup (canonical wire) parse checks seed index raw state

theorem other (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : Spec.Domain) (other : CborTaggedOther.Other query)
    (state : PqxdhDeploymentNative.State KemSK) :
    (fixed setup wire parse checks seed query).run state =
      (CborProductionBoundary.handler setup wire parse checks seed query).run state := by
  apply CborTaggedSimulation.filter_congr CborProductionBoundary.allowed CborProductionBoundary.reject
  cases query
  case inl coin => rfl
  case inr command =>
    cases command
    all_goals simp only [CborTaggedOther.Other] at other
    all_goals rfl

/-- Actual command-dependent raw registration and genuine fallible ordinary records form one adaptive native handler, on every complete state. -/
theorem stateful_exact (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed) :
    stateful setup wire parse checks seed = CborProductionBoundary.handler setup wire parse checks seed :=
  CborTaggedSimulation.adapt_exact (fixed setup wire parse checks seed)
    (CborProductionBoundary.handler setup wire parse checks seed) CborProductionBoundary.normalizationSender
    (build setup wire parse checks lengths parser seed) (finish setup wire parse checks seed)
    (other setup wire parse checks seed)

/-- The compiler chooses each finish tag from its own public creation log. Build replies are stripped after the source compiler has retained its logical response in the reconstruction log. -/
noncomputable def compileImpl (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) :
    QueryImpl Spec (StateT CborAdmissionCompiler.Local
      (OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK)))
  | .inr (.finish index raw) => fun memory =>
      (CborSplitCompiler.compileImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead wire.frameWrite
        (route parse) (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw)))).run memory
  | .inr (.build index payload) => Option.map CborPublicClient.strip <$>
      CborSplitCompiler.compileImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead wire.frameWrite
        (route parse) (.inr (.build index payload))
  | query => CborSplitCompiler.compileImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
      wire.frameWrite (route parse) query

noncomputable def compiledImpl (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (CborAdmissionCompiler.Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((PqxdhRegistrationJointRevealSchedule.native setup (sourceCodec wire parse) checks seed).mapStateTBase
    (compileImpl setup wire parse)).flattenStateT

theorem public_finish (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (memory : CborAdmissionCompiler.Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (sourceCodec wire parse) memory native)
    (index : Nat) (raw : Pqxdh.Bytes) :
    (fixed setup wire parse checks seed
      (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw)))).run
        (CborAdmissionCompiler.merge memory native) =
      (stateful setup wire parse checks seed (.inr (.finish index raw))).run
        (CborAdmissionCompiler.merge memory native) := by
  simp only [stateful, CborTaggedSimulation.adapt]
  rw [CborCommandFilter.atState_run]
  simpa only [fixed, CborSplitCompiler.nativeHandler, CborSplitCompiler.selected,
    CborSplitCompiler.recordCommand, Bool.false_eq_true, ite_false, CborAdmissionCompiler.nativeHandler,
    CborCommandFilter.handler, StateT.run, CborProductionBoundary.allowed, ite_true,
    ] using
    CborPublicPin.finish_tag setup (sourceCodec wire parse) checks (route parse) seed memory native good index raw

/-- The public compiler has the actual raw response and every complete native failure state, including differently pinned Beacons. -/
theorem public_step_merge (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (sourceCodec wire parse) memory native) :
    (fun result => (result.1.1, CborAdmissionCompiler.merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (sourceCodec wire parse) checks seed)
        ((compileImpl setup wire parse query).run memory)).run native =
      (CborProductionBoundary.handler setup wire parse checks seed query).run
        (CborAdmissionCompiler.merge memory native) := by
  rw [← stateful_exact setup wire parse checks lengths parser seed]
  cases query with
  | inl coin =>
    exact CborSplitCompiler.step_merge setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
      wire.frameWrite checks (route parse) seed (.inl coin) memory native good
  | inr command =>
    cases command with
    | finish index raw =>
      exact (CborSplitCompiler.step_merge setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed
        (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw))) memory native good).trans
          (public_finish setup wire parse checks seed memory native good index raw)
    | build index payload =>
      convert congrArg
        (fun work => (fun result => (Option.map CborPublicClient.strip result.1, result.2)) <$> work)
        (CborSplitCompiler.step_merge setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
          wire.frameWrite checks (route parse) seed (.inr (.build index payload)) memory native good) using 1 <;>
        (try simp only [compileImpl, StateT.run_map, simulateQ_map, Functor.map_map,
          stateful, CborTaggedSimulation.adapt, fixed]) <;> rfl
    | _ =>
      exact CborSplitCompiler.step_merge setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed _ memory native good

theorem compiled_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : Spec.Domain) (memory : CborAdmissionCompiler.Local)
    (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup wire parse checks seed query).run (memory, native) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (sourceCodec wire parse) checks seed)
          ((compileImpl setup wire parse query).run memory)).run native := rfl

theorem build_compiled_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (payload : Option Pqxdh.Bytes)
    (memory : CborAdmissionCompiler.Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup wire parse checks seed (.inr (.build index payload))).run (memory, native) =
      (fun result => (Option.map CborPublicClient.strip result.1, result.2)) <$>
        (CborSplitCompiler.compiledImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
          wire.frameWrite checks (route parse) seed (.inr (.build index payload))).run (memory, native) := by
  rw [compiled_run, CborSplitCompiler.compiledImpl_source_run]
  simp only [compileImpl, StateT.run_map, simulateQ_map, Functor.map_map]
  rfl

theorem finish_compiled_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (index : Nat) (raw : Pqxdh.Bytes)
    (memory : CborAdmissionCompiler.Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup wire parse checks seed (.inr (.finish index raw))).run (memory, native) =
      (CborSplitCompiler.compiledImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed
        (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw)))).run
          (memory, native) := by
  rw [compiled_run, CborSplitCompiler.compiledImpl_source_run]
  rfl

theorem other_compiled_run (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (query : Spec.Domain) (other : CborTaggedOther.Other query)
    (memory : CborAdmissionCompiler.Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup wire parse checks seed query).run (memory, native) =
      (CborSplitCompiler.compiledImpl setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed query).run (memory, native) := by
  rw [compiled_run, CborSplitCompiler.compiledImpl_source_run]
  rcases query with coin | command
  · rfl
  · cases command
    all_goals try simp [CborTaggedOther.Other] at other
    all_goals rfl

theorem good_step (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (sourceCodec wire parse))
    (query : Spec.Domain) (memory : CborAdmissionCompiler.Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (sourceCodec wire parse) memory native)
    (result : Spec.Range query × (CborAdmissionCompiler.Local × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledImpl setup wire parse checks seed query).run (memory, native))) :
    CborAdmissionCompiler.Good setup (sourceCodec wire parse) result.2.1 result.2.2 := by
  cases query with
  | inl coin =>
    rw [other_compiled_run setup wire parse checks seed (.inl coin) trivial memory native] at supported
    exact CborSplitCompiler.good_step setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
      wire.frameWrite checks (route parse) seed phase1 phase2 (.inl coin) memory native good result supported
  | inr command =>
    cases command with
    | finish index raw =>
      rw [finish_compiled_run] at supported
      exact CborSplitCompiler.good_step setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed phase1 phase2
        (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw)))
        memory native good result supported
    | build index payload =>
      rw [build_compiled_run, support_map] at supported
      obtain ⟨prior, member, rfl⟩ := supported
      exact CborSplitCompiler.good_step setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed phase1 phase2 (.inr (.build index payload))
        memory native good prior member
    | _ =>
      rw [other_compiled_run setup wire parse checks seed _ (by trivial) memory native] at supported
      exact CborSplitCompiler.good_step setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite checks (route parse) seed phase1 phase2 _ memory native good result supported

/-- The public source14 compiler exactly implements every adaptive raw-CBOR client, jointly over its complete output and native state. It reads no owner pin. -/
theorem compile_simulation (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (sourceCodec wire parse))
    (work : OracleComp Spec X) (memory : CborAdmissionCompiler.Local)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (sourceCodec wire parse) memory native) :
    (fun result => (result.1.1, CborAdmissionCompiler.merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (sourceCodec wire parse) checks seed)
        ((simulateQ (compileImpl setup wire parse) work).run memory)).run native =
      (simulateQ (CborProductionBoundary.handler setup wire parse checks seed) work).run
        (CborAdmissionCompiler.merge memory native) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledImpl setup wire parse checks seed) (CborProductionBoundary.handler setup wire parse checks seed)
    (fun state => CborAdmissionCompiler.Good setup (sourceCodec wire parse) state.1 state.2)
    (fun state => CborAdmissionCompiler.merge state.1 state.2)
    (fun query state valid result supported =>
      good_step setup wire parse checks seed phase1 phase2 query state.1 state.2 valid result supported)
    (fun query state valid => by
      rw [compiled_run, Functor.map_map]
      exact public_step_merge setup wire parse checks lengths parser seed query state.1 state.2 valid)
    work (memory, native) good
  rw [← simulated]
  rfl

/-- Tags and stripping are pure and preserve every source-query cost coordinate. -/
theorem step_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (kind : PqxdhRegistrationJointRevealCosts.SourceKind) (query : Spec.Domain)
    (memory : CborAdmissionCompiler.Local) :
    ((compileImpl setup wire parse query).run memory).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = kind)
      (PqxdhDeploymentCompileBudget.cost kind (PqxdhDeploymentCompileBudget.commandKind query)) := by
  cases query with
  | inl coin =>
    exact CborSplitCompiler.step_bound setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
      wire.frameWrite (route parse) kind (.inl coin) memory
  | inr command =>
    cases command with
    | finish index raw =>
      exact CborSplitCompiler.step_bound setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite (route parse) kind
        (.inr (.finish index (CborTaggedCodec.tag (CborPublicPin.pin memory index) raw))) memory
    | build index payload =>
      simpa only [compileImpl, StateT.run_map, isQueryBoundP_map_iff] using
        CborSplitCompiler.step_bound setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
          wire.frameWrite (route parse) kind (.inr (.build index payload)) memory
    | _ =>
      exact CborSplitCompiler.step_bound setup (sourceCodec wire parse) (boundaryWire wire parse).frameRead
        wire.frameWrite (route parse) kind _ memory

noncomputable def compile (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (work : OracleComp Spec X) :
    OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) (X × CborAdmissionCompiler.Local) :=
  (simulateQ (compileImpl setup wire parse) work).run (CborAdmissionCompiler.Local.empty setup.serverKeyId)

theorem compile_native (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CanonicalReadBack (boundaryWire wire parse)) (seed : PqxdhJointIdentity.IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (sourceCodec wire parse))
    (work : OracleComp Spec X) (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (lastId : native.shared.2.server.control.last_key_id = setup.serverKeyId)
    (peers : ∀ keyId, native.shared.2.server.server.peers keyId = none)
    (owners : native.owners = []) (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, CborAdmissionCompiler.merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (sourceCodec wire parse) checks seed)
        (compile setup wire parse work)).run native =
      (simulateQ (CborProductionBoundary.handler setup wire parse checks seed) work).run
        ⟨native, 0, fun _ => 0, []⟩ := by
  simpa only [compile, CborAdmissionCompiler.merge, CborAdmissionCompiler.Local.empty,
    PqxdhDeploymentCompile.merge_empty] using
    compile_simulation setup wire parse checks lengths parser seed phase1 phase2 work
      (CborAdmissionCompiler.Local.empty setup.serverKeyId) native
      (CborAdmissionCompileStep.good_initial setup (sourceCodec wire parse) native keyId lastId peers owners pending)

theorem compile_bound (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (work : OracleComp Spec X)
    (budget : Fin 12 → Nat)
    (bounded : ∀ command, work.IsQueryBoundP
      (fun query => PqxdhDeploymentCompileBudget.commandKind query = command) (budget command))
    (kind : PqxdhRegistrationJointRevealCosts.SourceKind) :
    (compile setup wire parse work).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = kind)
      (∑ command, PqxdhDeploymentCompileBudget.cost kind command * budget command) :=
  FinitePartitionQueryBounds.weighted_bound PqxdhDeploymentCompileBudget.commandKind
    (PqxdhDeploymentCompileBudget.cost kind) budget (compileImpl setup wire parse)
    (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = kind)
    work bounded (fun query memory => step_bound setup wire parse kind query memory)
    (CborAdmissionCompiler.Local.empty setup.serverKeyId)

end BeaconcryptCore.Computational.CborRawCompile

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.compile_simulation

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.compile_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.compile_bound

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.source_phase1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.source_phase1

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.source_phase2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.source_phase2

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.deployment_build_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.deployment_build_raw

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.filter_congr_when_allowed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.filter_congr_when_allowed

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.normalized_build_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.normalized_build_raw

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.build

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.finish

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.other

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.stateful_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.stateful_exact

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.public_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.public_finish

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.public_step_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.public_step_merge

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.compiled_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.build_compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.build_compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.finish_compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.finish_compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.other_compiled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.other_compiled_run

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.good_step

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.step_bound

/-- info: 'BeaconcryptCore.Computational.CborRawCompile.compile_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCompile.compile_native
