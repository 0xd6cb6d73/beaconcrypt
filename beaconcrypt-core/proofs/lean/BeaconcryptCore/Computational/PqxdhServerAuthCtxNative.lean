import BeaconcryptCore.Computational.PqxdhServerAuthCtxAmbient
import BeaconcryptCore.Computational.PqxdhServerAuthExperiment
import BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter

/-! Concrete ordinary Server and Beacon tail callbacks run against the same selected-component cache. The compiler keeps the actual optional writer/opening replies and the successful-seal log. No selected-key argument is required by the executable definitions; known-byte aliases remain allowed. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxNative
open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RawCtxSelectedReceiveCompiler (State project)

abbrev Local (A : Type) := StateT A (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)

noncomputable def evaluate {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (work : Local A Result) :
    StateT (State A) ProbComp Result :=
  PqxdhSelectedStateInterpreter.evaluate
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key) work

/-- Lifting a concrete component callback preserves the full local state and is exactly the existing component evaluation. -/
theorem lift_evaluate {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    evaluate source key read (StateT.lift work : Local A Result) =
      RawCtxSelectedReceiveCompiler.evaluated source key read work := by
  funext state
  simp only [evaluate, PqxdhSelectedStateInterpreter.evaluate, StateT.run_lift, bind_pure_comp,
    simulateQ_map, StateT.run_map, Functor.map_map, PqxdhSelectedStateInterpreter.pair,
    RawCtxSelectedReceiveCompiler.evaluated]


noncomputable def native {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxMixedOwner.NativeSpec (Local A) :=
  fun query => StateT.lift (PqxdhServerAuthCtxAmbient.native source writer query)

/-- The literal known native callback preserves the complete original auxiliary/cache projection. -/
theorem native_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.NativeSpec.Domain)
    (state : State A) :
    (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source) query).run (project state) =
      Prod.map id project <$> (evaluate source key read (native source writer query)).run state := by
  rw [native, lift_evaluate]
  exact PqxdhServerAuthCtxAmbient.native_source source writer key read query state

private theorem program {ι A Result : Type} {spec : OracleSpec ι}
    (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (compiler : QueryImpl spec (Local A))
    (original : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (step : ∀ query state, (original query).run (project state) =
      Prod.map id project <$> (evaluate source key read (compiler query)).run state)
    (work : OracleComp spec Result) (state : State A) :
    (simulateQ original work).run (project state) =
      Prod.map id project <$> (evaluate source key read (simulateQ compiler work)).run state := by
  unfold evaluate
  rw [PqxdhSelectedStateInterpreter.program]
  exact (map_run_simulateQ_eq_of_query_map_eq _ original project
    (fun query before => (step query before).symm) work state).symm

variable {Reader Response : Type}

/-- The actual stateless Server tail callbacks retain their source codec/check outcomes. -/
def aux {A : Type} (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Local A)
  | .checkIdentity identity => pure (checks.beaconIdentity identity)
  | .reservePeer => pure checks.reservePeer
  | .reservePlaintext length => pure (checks.reservePlaintext length)
  | .erase _ => pure ()
  | .write fields => pure (codec.write2 fields)

/-- These are the exact original auxiliary callbacks, including failed allocation/check/write outcomes. -/
theorem aux_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (query : PqxdhServerRegistrationPublication.AuxSpec.Domain)
    (state : State A) :
    (PqxdhServerAuthExperiment.tailAux codec checks query).run (project state) =
      Prod.map id project <$> (evaluate source key read (aux codec checks query)).run state := by
  cases query <;> simp [aux, PqxdhServerAuthExperiment.tailAux, evaluate,
    PqxdhSelectedStateInterpreter.pure_evaluate, StateT.run_pure]

noncomputable def registration {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.NativeSpec (Local A)
  | .inl query => simulateQ (native source codec.frameWrite) (RawCtxMixedOwner.sendLift query)
  | .inr query => aux codec checks query

/-- The original registration adapter and every auxiliary callback execute on exactly the same shared cache and retained local state. -/
theorem registration_source {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (state : State A) :
    (PqxdhRegistrationProtocolState.registrationImpl source codec.frameWrite
      (PqxdhServerAuthExperiment.tailAux codec checks) query).run (project state) =
      Prod.map id project <$> (evaluate source key read (registration source codec checks query)).run state := by
  cases query with
  | inl query =>
      exact program source key read (native source codec.frameWrite)
        (RawCtxMixedShared.sharedImpl source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl source))
        (native_source source codec.frameWrite key read) (RawCtxMixedOwner.sendLift query) state
  | inr query => exact aux_source source codec checks key read query state

noncomputable def nativeTail {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.TailSpec (Local A) :=
  registration source codec checks ∘ₛ PqxdhServerRegistrationPublication.nativeAdapter

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Concrete primitive expansion of the original Server response tail preserves all optional outcomes and the shared auxiliary/cache state. -/
theorem nativeTail_source {A : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : State A) :
    (PqxdhServerAuthExperiment.nativeTail setup codec checks query).run (project state) =
      Prod.map id project <$> (evaluate setup.source key read (nativeTail setup.source codec checks query)).run state := by
  exact program setup.source key read (registration setup.source codec checks)
    (PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite
      (PqxdhServerAuthExperiment.tailAux codec checks))
    (registration_source setup.source codec checks key read)
    (PqxdhServerRegistrationPublication.nativeAdapter query) state

/-- Exact successful-seal logging: a failed inner frame writer emits no log entry; later Phase 2 writer failure does not remove an existing entry. -/
noncomputable def tail (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks) :
    QueryImpl PqxdhServerRegistrationPublication.TailSpec (Local (List RawCtxSourceSend.SealContext))
  | .inl (.inl request) => nativeTail source codec checks (.inl (.inl request))
  | .inl (.inr input) => do
      let sealed ← nativeTail source codec checks (.inl (.inr input))
      if sealed.isSome then modify fun contexts => contexts ++ [input.context]
      pure sealed
  | .inr query => nativeTail source codec checks (.inr query)

private theorem evaluate_run {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (work : Local A Result) (state : State A) :
    (evaluate source key read work).run state = PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (work.run state.1)).run state.2 := rfl

/-- The actual tail log and the complete cache survive every optional callback outcome, including inner writer failure and later response failure. -/
theorem tail_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (state : State (List RawCtxSourceSend.SealContext)) :
    (PqxdhServerAuthExperiment.tailImpl setup codec checks query).run (project state) =
      Prod.map id project <$> (evaluate setup.source key read (tail setup.source codec checks query)).run state := by
  rcases query with (request | input) | request
  · exact nativeTail_source setup codec checks key read _ state
  · have exactTail := congrArg (fun work =>
        (fun result => (result.1, (if result.1.isSome then result.2.1 ++ [input.context] else result.2.1, result.2.2))) <$> work)
        (nativeTail_source setup codec checks key read (.inl (.inr input)) state)
    have left : (PqxdhServerAuthExperiment.tailImpl setup codec checks (.inl (.inr input))).run (project state) =
        (fun result => (result.1, (if result.1.isSome then result.2.1 ++ [input.context] else result.2.1, result.2.2))) <$>
          (PqxdhServerAuthExperiment.nativeTail setup codec checks (.inl (.inr input))).run (project state) := by
      simp only [PqxdhServerAuthExperiment.tailImpl, StateT.run_bind]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      rintro ⟨result, after⟩
      cases result <;> simp [StateT.run_modify, StateT.run_pure]
    rw [left, exactTail]
    simp only [evaluate_run, tail, StateT.run_bind, simulateQ_bind, map_bind, Functor.map_map]
    rw [map_eq_bind_pure_comp]
    apply bind_congr
    rintro ⟨⟨result, after⟩, component⟩
    cases result <;> simp [StateT.run_modify, StateT.run_pure,
      PqxdhSelectedStateInterpreter.pair, project]
  · exact nativeTail_source setup codec checks key read _ state

/-- The complete actual unmarked build retains its full Server response/state, successful seal log and common cache under the concrete dynamic-component compiler. -/
theorem build_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (pending : pqxdh.PendingServerRegistration) (root : RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : State (List RawCtxSourceSend.SealContext)) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run (project state) =
      Prod.map id project <$> (evaluate setup.source key read (simulateQ (tail setup.source codec checks)
        (PqxdhServerRegistrationPublication.build setup.source pending root payload () server))).run state :=
  program setup.source key read (tail setup.source codec checks) (PqxdhServerAuthExperiment.tailImpl setup codec checks)
    (tail_source setup codec checks key read) _ state

/-- The ordinary Beacon tail keeps the original initial HKDF/application getter and forwards every actual native hash/opening through the common cache. -/
noncomputable def beacon (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (Local Unit)
  | .inl query => simulateQ (native source codec.frameWrite) (RawCtxMixedOwner.receiveLift query)
  | .inr (.root _) => pure none
  | .inr (.initial request) => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .inr (.application response) => pure (codec.application response)

/-- Every ordinary Beacon callback agrees with its literal source interpretation, including rejected openings and missing application bytes. -/
theorem beacon_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (state : State Unit) :
    (PqxdhServerAuthExperiment.beaconNative setup codec query).run (project state) =
      Prod.map id project <$> (evaluate setup.source key read (beacon setup.source codec query)).run state := by
  rcases query with query | (input | request | response)
  · have exactNative := program setup.source key read (native setup.source codec.frameWrite)
      (RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source))
      (native_source setup.source codec.frameWrite key read) (RawCtxMixedOwner.receiveLift query) state
    simpa only [beacon, PqxdhServerAuthExperiment.beaconNative,
      ← QueryImpl.apply_compose, RawCtxMixedShared.shared_receive] using exactNative
  all_goals simp [beacon, PqxdhServerAuthExperiment.beaconNative, evaluate,
    PqxdhSelectedStateInterpreter.pure_evaluate, StateT.run_pure]

/-- The whole literal ordinary post-root receive retains arbitrary raw bytes, every parser/sequence/opening failure, actual optional plaintext and complete source/cache poststate. -/
theorem beacon_after_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (root : Std.Array Std.U8 32#usize) (state : State Unit) :
    (simulateQ (PqxdhServerAuthExperiment.beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead prepared root)).run (project state) =
      Prod.map id project <$> (evaluate setup.source key read (simulateQ (beacon setup.source codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead prepared root))).run state :=
  program setup.source key read (beacon setup.source codec) (PqxdhServerAuthExperiment.beaconNative setup codec)
    (beacon_source setup codec key read) _ state

end BeaconcryptCore.Computational.PqxdhServerAuthCtxNative

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.lift_evaluate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.lift_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.native_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.aux_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.aux_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.registration_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.registration_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.nativeTail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.nativeTail_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.tail_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.build_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.beacon_source

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.beacon_after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNative.beacon_after_source
