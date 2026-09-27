import BeaconcryptCore.Computational.PqxdhSelectedStateInterpreter
import BeaconcryptCore.Computational.PqxdhSelectedBeaconCompiler

/-!
Actual attempted Beacon finishes retain their original preparation, audited initializer and optional application getter before the key-free first-receive continuation. An explicit service sum separates those source-local callbacks from the actual dynamic CTX computation. The selected key belongs only to the evaluated interpreter.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open PqxdhNativeSharedPrefix PqxdhInitialGenericBeacon
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open PqxdhSelectedStateInterpreter (evaluate pair)
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}

abbrev Kernel := RawCtxSelectedMessageReveals.Kernel
abbrev Beacon (I D K : Type) := RawCtxGenericRoleStorage.BeaconState Kernel I D K
abbrev Reply (I D K : Type) := Option Pqxdh.Bytes × Beacon I D K

structure Request (I D K : Type) where
  control : pqxdh.BeaconInitSent
  before : Beacon I D K
  candidate : pqxdh.BeaconRegistrationCandidate
  kernel : Kernel
  application : Option Pqxdh.Bytes

abbrev Spec (extra : OracleSpec ι) (I D K X Response Shared : Type) :=
  PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared + (Request I D K →ₒ Reply I D K)

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

noncomputable def lower (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Spec extra I D K X Response Shared)
      (StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))
  | .inl query => PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)
  | .inr request => fun state => (fun reply => (reply, state)) <$>
      PqxdhSelectedBeaconCompiler.finishApplication prior parent target nonce next read
        request.control request.before request.candidate request.kernel request.application

noncomputable def sourceExternal : QueryImpl (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared)
    (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp) :=
  fun query => evaluate AdaptiveCtxSharedHash.hashImpl
    (PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query)

noncomputable def source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Spec extra I D K X Response Shared)
      (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp)
  | .inl query => sourceExternal pre application initial selector aux query
  | .inr request => finish request.control request.before <$>
      (match request.application with
      | none => pure none
      | some raw => PqxdhSelectedBeaconCompiler.stage request.candidate <$>
          (RawCtxChainOwner.rawReceive
            (PqxdhSelectedMessageBeacon.materialCalls fixed writer prior parent key target nonce next) read raw).run
              (localOwner request.candidate request.kernel))

/-- The source-local service preserves its complete original reply, private state and audit through the same component state projection. -/
theorem external_project (fixed : FixedHkdfSha512NoSaltSource) (key : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id RawCtxSelectedReceiveCompiler.project <$>
      (evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
        (PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query))).run state =
      (sourceExternal pre application initial selector aux query).run (RawCtxSelectedReceiveCompiler.project state) := by
  have original := congrArg (Functor.map pair)
    (RawCtxSourceSharedRom.forward_cache true (RawCtxUniversalDecoder.decoder read) fixed.crypto key
      ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state.1) state.2)
  convert original using 1 <;> simp only [evaluate, sourceExternal, PqxdhSelectedCallbackCompiler.lower, StateT.run,
    RawCtxSelectedReceiveCompiler.project, Functor.map_map, Prod.map_def, id_eq, pair]
  rfl

/-- Each concrete source operation retains its optional result and whole local/cache state, including the actual first raw receive and final Beacon publication. -/
theorem step_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (query : (Spec extra I D K X Response Shared).Domain)
    (state : Local A N C × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id RawCtxSelectedReceiveCompiler.project <$>
      (evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
        (lower pre application initial selector aux prior parent target nonce next read query)).run state =
      (source pre application initial selector aux fixed writer prior parent key target nonce next read query).run
        (RawCtxSelectedReceiveCompiler.project state) := by
  cases query with
  | inl query => exact external_project pre application initial selector aux fixed key read query state
  | inr request =>
      have original := PqxdhSelectedBeaconCompiler.finish_application_source fixed writer prior parent key target nonce next read
        request.control request.before request.candidate request.kernel request.application state
      simp only [lower, PqxdhSelectedStateInterpreter.lift_evaluate]
      exact original

/-- The entire adaptive source program has the same complete output and retained state through the concrete callback and first-receive compiler. -/
theorem program_source {Result : Type} (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (Spec extra I D K X Response Shared) Result)
    (state : Local A N C × AdaptiveCtxDynamicKnownKeys.SourceState) :
    Prod.map id RawCtxSelectedReceiveCompiler.project <$>
      (evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
        (simulateQ (lower pre application initial selector aux prior parent target nonce next read) work)).run state =
      (simulateQ (source pre application initial selector aux fixed writer prior parent key target nonce next read) work).run
        (RawCtxSelectedReceiveCompiler.project state) := by
  rw [PqxdhSelectedStateInterpreter.program]
  exact map_run_simulateQ_eq_of_query_map_eq _ _ RawCtxSelectedReceiveCompiler.project
    (step_source pre application initial selector aux fixed writer prior parent key target nonce next read) work state

def preForward : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
    (OracleComp (Spec extra I D K X Response Shared)) :=
  fun query => (Spec extra I D K X Response Shared).query (.inl (.inl query))

noncomputable def owner (raw : Pqxdh.Bytes) (before : Beacon I D K) : OracleComp (Spec extra I D K X Response Shared) (Reply I D K) :=
  match before.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preForward
        (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (finish control before none)
      | some pending => do
          let kernel ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inr (.inl pending.root))))
          match kernel with
          | none => pure (finish control before none)
          | some kernel => do
              let application ← (Spec extra I D K X Response Shared).query (.inl (.inr (.inl pending.response)))
              (Spec extra I D K X Response Shared).query (.inr
                ⟨control, before, PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
                  PqxdhSelectedMessageBeacon.knownKernel kernel, application⟩)
  | _ => pure (none, before)

/-- Source preparation calls are precisely the original external requests, with their complete evaluated continuation. -/
theorem preparation_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) :
    source pre application initial selector aux fixed writer prior parent key target nonce next read ∘ₛ preForward =
      (fun query => sourceExternal pre application initial selector aux (.inl query)) := by
  funext query
  exact simulateQ_spec_query (source pre application initial selector aux fixed writer prior parent key target nonce next read) (.inl (.inl query))

/-- This compiler's attempted-finish client is the actual generic source owner, retaining preparation, audited initialization, the optional getter, raw receive and every terminal state. -/
theorem owner_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    simulateQ (source pre application initial selector aux fixed writer prior parent key target nonce next read) (owner raw before) =
      PqxdhInitialGenericBeacon.owner
        (fun query => sourceExternal pre application initial selector aux (.inl query))
        (PqxdhSelectedMessageBeacon.materialCalls fixed writer prior parent key target nonce next)
        (fun reply => sourceExternal pre application initial selector aux (.inr (.inl reply)))
        (fun secrets => Option.map PqxdhSelectedMessageBeacon.knownKernel <$>
          sourceExternal pre application initial selector aux (.inr (.inr (.inl secrets)))) read raw before := by
  unfold owner PqxdhInitialGenericBeacon.owner
  cases phase : before.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose, preparation_source]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => exact simulateQ_pure _ _
    | some pending =>
      simp only [simulateQ_bind, simulateQ_spec_query, source, tail, bind_map_left, bind_assoc]
      apply bind_congr
      intro kernel
      cases kernel with
      | none => simp only [simulateQ_pure, Option.map_none, pure_bind]
      | some kernel =>
        simp only [Option.map_some, simulateQ_bind, simulateQ_spec_query, source, afterInitial,
          bind_pure_comp, map_bind]
        rfl
  all_goals exact simulateQ_pure _ _

/-- Mapping only private selected message material back to native bytes gives the actual full Beacon owner with its original initializer, not an assumed callback relation. -/
theorem native_owner (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    PqxdhInitialGenericBeacon.owner
      (fun query => sourceExternal pre application initial selector aux (.inl query))
      (PqxdhSelectedMessageBeacon.nativeCalls fixed writer prior parent key target nonce next)
      (fun reply => sourceExternal pre application initial selector aux (.inr (.inl reply)))
      (fun secrets => sourceExternal pre application initial selector aux (.inr (.inr (.inl secrets)))) read raw
      (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) before) =
    Prod.map id (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key)) <$>
      simulateQ (source pre application initial selector aux fixed writer prior parent key target nonce next read) (owner raw before) := by
  rw [owner_source]
  apply PqxdhInitialGenericBeacon.owner_map
  · exact PqxdhSelectedMessageBeacon.receive_map fixed writer prior parent key target nonce next
  · intro secrets
    simp only [Functor.map_map, Option.map_map, Function.comp_def, PqxdhSelectedMessageBeacon.known_roundtrip]
    change _ = Option.map id <$> _
    simp only [Option.map_id, id_map]

/-- The actual attempted Beacon owner executes without a selected key in its compiled program and returns the same native optional suffix, full role state, source-local state and cache. -/
theorem compiled_owner (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : Beacon I D K)
    (state : Local A N C × AdaptiveCtxDynamicKnownKeys.SourceState) :
    (fun result =>
      (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key)) result.1,
        RawCtxSelectedReceiveCompiler.project result.2)) <$>
      (evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) fixed.crypto key)
        (simulateQ (lower pre application initial selector aux prior parent target nonce next read) (owner raw before))).run state =
      (PqxdhInitialGenericBeacon.owner
        (fun query => sourceExternal pre application initial selector aux (.inl query))
        (PqxdhSelectedMessageBeacon.nativeCalls fixed writer prior parent key target nonce next)
        (fun reply => sourceExternal pre application initial selector aux (.inr (.inl reply)))
        (fun secrets => sourceExternal pre application initial selector aux (.inr (.inr (.inl secrets)))) read raw
        (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key) before)).run
          (RawCtxSelectedReceiveCompiler.project state) := by
  have original := congrArg (fun work => (fun result =>
    (Prod.map id (RawCtxGenericRoleStorage.mapBeacon (PqxdhSelectedMessageBeacon.interpretKernel key)) result.1, result.2)) <$> work)
    (program_source pre application initial selector aux fixed writer prior parent key target nonce next read (owner raw before) state)
  rw [native_owner, StateT.run_map]
  simpa only [Functor.map_map, Prod.map_def, id_eq] using original

/-- Each original source callback on the complete audited state is exactly the external operation used by the native owner comparison; no new callback simulation premise is introduced. -/
theorem external_native (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage S B : Nat)
    (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C × CtxRomAuth.CtxRO.QueryCache) :
    (fun result => (result.1, attach result.2.1 result.2.2)) <$>
      (sourceExternal pre application initial selector aux query).run state =
      (PqxdhInitialNativeAudit.handler (S := S) (B := B) fixed writer stage
        (fun request => localLift (pre request)) (fun reply => localLift (application reply))
        (fun secrets => localLift (initial secrets)) (fun request => localLift (selector request))
        (fun request => localLift (aux request)) (.inr query)).run (attach state.1 state.2) := by
  have original := PqxdhNativeSharedPrefix.step (S := S) (B := B) fixed writer stage
    pre application initial selector aux (.inr query) state.1 state.2
  rw [← PqxdhSelectedCallbackCompiler.local_native pre application initial selector aux fixed writer stage S B query] at original
  convert original using 1; simp only [sourceExternal, evaluate, StateT.run, Functor.map_map, pair]
  rfl

/-- A full attempted Beacon finish uses at most thirteen preparation requests followed by one initializer, one getter and one whole raw-finish request. The actual callback and component costs remain separately charged. -/
theorem owner_queries (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    (owner (extra := extra) (X := X) (Response := Response) (Shared := Shared) raw before).IsTotalQueryBound 16 := by
  cases active : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [owner, active]
    apply isTotalQueryBound_bind (n₁ := 13) (n₂ := 3)
    · exact PqxdhBeaconPhase2Bounds.simulate_total preForward _ 13
        (PqxdhBeaconPhase2SharedBounds.prepare_bound _ _ _ _ _ _) (fun query => by
          exact (isQueryBoundP_true_iff _ _).mp ((isQueryBoundP_query_iff (spec := Spec extra I D K X Response Shared)
            (p := fun _ => True) (.inl (.inl query)) 1).mpr (by decide)))
    · intro prepared
      cases prepared with
      | none => trivial
      | some pending =>
        rw [isTotalQueryBound_query_bind_iff]
        refine ⟨by decide, fun kernel => ?_⟩
        cases kernel with
        | none => trivial
        | some kernel =>
          rw [isTotalQueryBound_query_bind_iff]
          exact ⟨by decide, fun _ => (isQueryBoundP_true_iff _ _).mp
            ((isQueryBoundP_query_iff (spec := Spec extra I D K X Response Shared) (p := fun _ => True) _ 1).mpr (by decide))⟩
  | _ => simp only [owner, active]; trivial

def IsFinish : (Spec extra I D K X Response Shared).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred (IsFinish (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)) :=
  fun query => match query with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

/-- Every complete attempted Beacon finish invokes at most one raw-finish service, regardless of arbitrary preparation replies, initializer failure or optional application data. -/
theorem owner_finish_queries (raw : Pqxdh.Bytes) (before : Beacon I D K) :
    (owner (extra := extra) (X := X) (Response := Response) (Shared := Shared) raw before).IsQueryBoundP (IsFinish (extra := extra)) 1 := by
  classical
  cases active : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [owner, active]
    apply isQueryBoundP_bind (n := 0) (m := 1)
    · exact (isQueryBoundP_false _ 0).simulateQ_of_step
        (impl := preForward) (q := IsFinish (extra := extra)) (fun _ impossible => False.elim impossible)
        (fun query _ => (isQueryBoundP_query_iff (spec := Spec extra I D K X Response Shared)
          (p := IsFinish (extra := extra)) (.inl (.inl query)) 0).mpr (by simp [IsFinish]))
    · intro prepared _
      cases prepared with
      | none => trivial
      | some pending =>
        rw [isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp [IsFinish]), fun kernel => ?_⟩
        cases kernel with
        | none => trivial
        | some kernel =>
          rw [isQueryBoundP_query_bind_iff]
          exact ⟨Or.inl (by simp [IsFinish]), fun _ =>
            (isQueryBoundP_query_iff (spec := Spec extra I D K X Response Shared) (p := IsFinish (extra := extra)) _ 1).mpr (by simp [IsFinish])⟩
  | _ => simp only [owner, active]; trivial

/-- The concrete source-local callbacks make no selected raw-opening request, regardless of their original uniform cost. -/
theorem external_no_open (query : (PqxdhSelectedCallbackCompiler.External extra I D K X Response Shared).Domain)
    (state : Local A N C) :
    ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run state).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  change (simulateQ RawCtxSourceSharedRom.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP _ 0
  simp only [RawCtxSourceSharedRom.forward, QueryImpl.simulateQ_compose]
  apply RawCtxSelectedSealConsumer.lifted_bound
  change (simulateQ AdaptiveCtxSharedTarget.forward
    ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run state)).IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 0
  apply AdaptiveCtxSharedTarget.forward_bound
  simp only [AdaptiveCtxSharedTarget.forward_raw_class]
  exact isQueryBoundP_false _ 0

/-- The compiled complete attempted Beacon owner makes at most one selected raw verification request. Actual callback randomness and known-key primitive costs retain their separate ledgers. -/
theorem compiled_opens (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (before : Beacon I D K) (state : Local A N C) :
    ((simulateQ (lower pre application initial selector aux prior parent target nonce next read)
      (owner raw before)).run state).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  apply (owner_finish_queries (extra := extra) (X := X) (Response := Response) (Shared := Shared) raw before).simulateQ_run_of_step
  · intro query selected state
    cases query with
    | inl query => exact False.elim selected
    | inr request =>
      simp only [lower, StateT.run, isQueryBoundP_map_iff]
      exact IsQueryBoundP.of_imp (fun _ _ => True.intro)
        ((isQueryBoundP_true_iff _ _).mpr (PqxdhSelectedBeaconCompiler.finish_queries prior parent target nonce next read
          request.control request.before request.candidate request.kernel request.application))
  · intro query excluded state
    cases query with
    | inl query => exact external_no_open pre application initial selector aux query state
    | inr request => exact False.elim (excluded True.intro)

end BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_project

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.preparation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.native_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.native_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.compiled_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.compiled_owner

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_native

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_finish_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.owner_finish_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_no_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.external_no_open

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.compiled_opens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedInitialOwnerCompiler.compiled_opens
