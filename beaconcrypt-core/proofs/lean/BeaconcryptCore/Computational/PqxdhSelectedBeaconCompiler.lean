import BeaconcryptCore.Computational.PqxdhSelectedMessageBeacon
import BeaconcryptCore.Computational.RawCtxSelectedReceiveCompiler

/-!
The actual first Beacon receive after its response getter is compiled to the selected CTX interface. The optional raw application, complete initialized kernel, sequence-one restriction, eight-byte registration binding and final pinned-server publication checks are preserved. The compiler has no selected key argument. Preparation and initialization remain earlier source operations, whose concrete descriptors must supply this exact continuation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedReceiveCompiler (State project evaluated)
open PqxdhInitialGenericBeacon
open PqxdhSelectedMessageBeacon (interpretKernel nativeCalls materialCalls)
variable {A I D K : Type}

noncomputable def stage {Kernel : Type} (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State Kernel Unit) : Option (Staged Kernel) :=
  afterOpening candidate result.2.kernel result.1

noncomputable def afterApplication (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (application : Option Pqxdh.Bytes) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option (Staged RawCtxSelectedMessageReveals.Kernel)) :=
  match application with
  | none => pure none
  | some raw =>
      (stage candidate) <$>
        RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read raw (localOwner candidate kernel)

noncomputable def finishApplication (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (application : Option Pqxdh.Bytes) :=
  finish control before <$> afterApplication prior parent target nonce next read candidate kernel application

/-- Exact source continuation after the original response getter. Both absent application data and every arbitrary raw string retain their actual result and full source state. -/
theorem after_application_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (application : Option Pqxdh.Bytes) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (afterApplication prior parent target nonce next read candidate kernel application)).run state =
      ((match application with
        | none => pure none
        | some raw => (stage candidate) <$>
            (RawCtxChainOwner.rawReceive (materialCalls source writer prior parent key target nonce next) read raw).run
              (localOwner candidate kernel))).run (project state) := by
  cases application with
  | none => rfl
  | some raw =>
    simp only [afterApplication, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map]
    rw [show materialCalls (A := A) source writer prior parent key target nonce next =
      RawCtxSelectedMessageFamily.calls
        (RawCtxSelectedMessageDriver.receiveServices source writer prior parent key target nonce next)
        (RawCtxSelectedMessageDriver.sendServices source writer prior parent key target nonce next) parent target nonce next from rfl]
    rw [RawCtxSelectedReceiveCompiler.raw_source]
    simp only [Functor.map_map, Prod.map_def, id_eq]

/-- The real Beacon finish keeps the same plaintext suffix, authentication gates and complete terminal role state, including abort. -/
theorem finish_application_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (application : Option Pqxdh.Bytes) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (finishApplication prior parent target nonce next read control before candidate kernel application)).run state =
      (finish control before <$>
        (match application with
        | none => pure none
        | some raw => (stage candidate) <$>
            (RawCtxChainOwner.rawReceive (materialCalls source writer prior parent key target nonce next) read raw).run
              (localOwner candidate kernel))).run (project state) := by
  have mapped := congrArg (fun work => (fun result => (finish control before result.1, result.2)) <$> work)
    (after_application_source source writer prior parent key target nonce next read candidate kernel application state)
  simpa only [finishApplication, RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map, Functor.map_map,
    Prod.map_def, id_eq] using mapped

/-- Native private-kernel interpretation leaves the real response-getter continuation unchanged, including the exact sequence and binding checks. -/
theorem native_after_application (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (application : Option Pqxdh.Bytes) :
    (match application with
      | none => pure none
      | some raw => (stage candidate) <$>
          (RawCtxChainOwner.rawReceive (nativeCalls (A := A) source writer prior parent key target nonce next) read raw).run
            (localOwner candidate (interpretKernel key kernel))) =
    Option.map (mapStaged (interpretKernel key)) <$>
      (match application with
      | none => pure none
      | some raw => (stage candidate) <$>
          (RawCtxChainOwner.rawReceive (materialCalls source writer prior parent key target nonce next) read raw).run
            (localOwner candidate kernel)) := by
  cases application with
  | none => simp only [map_pure, Option.map_none]
  | some raw =>
    simp only
    rw [show localOwner candidate (interpretKernel key kernel) =
      RawCtxGenericOwnerMap.mapOwner (interpretKernel key) (localOwner candidate kernel) from rfl]
    rw [RawCtxGenericOwnerMap.raw_map (interpretKernel key)
      (materialCalls source writer prior parent key target nonce next)
      (nativeCalls source writer prior parent key target nonce next)
      (PqxdhSelectedMessageBeacon.receive_map source writer prior parent key target nonce next)]
    simp only [Functor.map_map, Prod.map_def, id_eq, RawCtxGenericOwnerMap.mapOwner]
    unfold stage
    congr 1
    funext result
    exact opening_map (interpretKernel key) candidate result.2.kernel result.1


/-- The actual native Beacon continuation after preparation, initialization and the getter is exactly the key-free CTX continuation, with the original optional plaintext suffix and every native terminal state field. -/
theorem native_finish_application (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (application : Option Pqxdh.Bytes) (state : State A) :
    (fun result => (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (interpretKernel key)) result.1, project result.2)) <$>
      (evaluated source key read
        (finishApplication prior parent target nonce next read control before candidate kernel application)).run state =
      (finish control (RawCtxGenericRoleStorage.mapBeacon (interpretKernel key) before) <$>
        (match application with
        | none => pure none
        | some raw => stage candidate <$>
            (RawCtxChainOwner.rawReceive (nativeCalls source writer prior parent key target nonce next) read raw).run
              (localOwner candidate (interpretKernel key kernel)))).run (project state) := by
  rw [native_after_application, Functor.map_map]
  simp only [finish_map]
  have mapped := congrArg (fun work => (fun result =>
    (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (interpretKernel key)) result.1, result.2)) <$> work)
      (finish_application_source source writer prior parent key target nonce next read control before candidate kernel application state)
  simpa only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq] using mapped

/-- The complete first-receive finish pays for at most one raw CTX verification attempt; getter absence and all parser, sequence, binding or publication rejection paths can only reduce that count. -/
theorem finish_queries (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (application : Option Pqxdh.Bytes) :
    (finishApplication prior parent target nonce next read control before candidate kernel application).IsTotalQueryBound 1 := by
  simp only [finishApplication, IsTotalQueryBound, isQueryBound_map_iff]
  cases application with
  | none => trivial
  | some raw =>
    simp only [afterApplication, isQueryBound_map_iff]
    exact RawCtxSelectedReceiveCompiler.raw_queries prior parent target nonce next read raw (localOwner candidate kernel)

end BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.after_application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.after_application_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.finish_application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.finish_application_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.native_after_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.native_after_application

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.native_finish_application' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.native_finish_application

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.finish_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler.finish_queries
