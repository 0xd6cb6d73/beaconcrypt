import BeaconcryptCore.Computational.PqxdhPreparedSelectedInitialOwner
import BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling

/-!
The original outer post schedule combines adaptive records, reveals, selector work and attempted Beacon finishes in one executable selected-message interface. It retains the complete role family, registration controls, consumed identifiers, original observation history and source-local state. Selected nonce stopping is explicit and separate from unavailable hidden-key disclosure.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhSelectedPostCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

private theorem state_map_apply {X Y σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = (fun result => (f result.1, result.2)) <$> work.run state
  rw [StateT.run_map]

structure Front (M P I D K : Type) (S B : Nat) where
  roles : RawCtxSelectedMessageReveals.State M P I D K S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes

abbrev State (M P I D K A N C : Type) (S B : Nat) := Front M P I D K S B × Local A N C
abbrev Full (M P I D K A N C : Type) (S B : Nat) := State M P I D K A N C S B × AdaptiveCtxDynamicKnownKeys.SourceState
abbrev SourceState (M P I D K A N C : Type) (S B : Nat) := Front M P I D K S B × RawCtxSharedPrimitive.SharedState (Local A N C)

abbrev Base := OracleComp AdaptiveCtxDynamicKnownKeys.Spec
abbrev Optional {κ : Type} (spec : OracleSpec κ) := RawCtxSelectedFamilyNonceCoupling.Optional spec

def project (state : Full M P I D K A N C S B) : SourceState M P I D K A N C S B :=
  (state.1.1, (state.1.2, state.2.cache))

def install (index : Fin B) (before : Front M P I D K S B)
    (updated : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) : Front M P I D K S B :=
  { before with roles := ((before.roles.1.1, Function.update before.roles.1.2 index updated),
      RawCtxSelectedMessageFamily.tick before.roles.2) }

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (OptionT (StateT (State M P I D K A N C S B) Base)) :=
  fun query => OptionT.mk fun before => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, ({ before.1 with roles := result.2 }, before.2))) <$>
        (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read request).run).run before.1.roles)
  | .inl (.inr request) =>
      (fun result => (some result.1, (before.1, result.2))) <$>
        ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux
          (.inl (.inr (.inr (.inr (.inl request)))))).run before.2)
  | .inr (.finish index raw) =>
      (fun result => (some result.1.1, (install index before.1 result.1.2, result.2))) <$>
        ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
          (PqxdhSelectedInitialOwnerCompiler.owner raw (before.1.roles.1.2 index))).run before.2)

noncomputable def client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : State M P I D K A N C S B) :
    Base (Option Result × State M P I D K A N C S B) :=
  ((simulateQ (impl pre application initial selector aux source writer prior parent target nonce next sender route read) original).run).run before

noncomputable def Stops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Full M P I D K A N C S B) : Prop :=
  match query with
  | .inl (.inl request) => RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender request before.1.1.roles before.2
  | _ => False

noncomputable def evaluated (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (Full M P I D K A N C S B) ProbComp) :=
  fun query => PqxdhSelectedStateInterpreter.evaluate
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      ((impl pre application initial selector aux source writer prior parent target nonce next sender route read query).run)

noncomputable def augmented (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (Full M P I D K A N C S B) ProbComp) :=
  fun query before => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, (({ before.1.1 with roles := result.2.1 }, result.2.2.1), result.2.2.2))) <$>
        (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read request).run
          (before.1.1.roles, (before.1.2, before.2))
  | query => (evaluated pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before

noncomputable def original (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (SourceState M P I D K A N C S B) ProbComp) :=
  fun query before => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, ({ before.1 with roles := result.2.1 }, result.2.2))) <$>
        (RawCtxSelectedFamilyNonceCoupling.original source writer prior parent key target nonce next sender route read request).run (before.1.roles, before.2)
  | .inl (.inr request) =>
      (fun result => (some result.1, (before.1, result.2))) <$>
        (PqxdhSelectedInitialOwnerCompiler.sourceExternal pre application initial selector aux
          (.inr (.inr (.inr (.inl request))))).run before.2
  | .inr (.finish index raw) =>
      (fun result => (some result.1.1, (install index before.1 result.1.2, result.2))) <$>
        (simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initial selector aux source writer prior parent key target nonce next read)
          (PqxdhSelectedInitialOwnerCompiler.owner raw (before.1.roles.1.2 index))).run before.2

/-- Projecting the exact augmented post callback preserves the original record/reveal service, selector or complete attempted finish and all retained source state. -/
theorem augmented_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Full M P I D K A N C S B) :
    Prod.map id project <$> (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before =
      (original pre application initial selector aux source writer prior parent key target nonce next sender route read query).run (project before) := by
  rcases query with (request | request) | request
  · have actual := RawCtxSelectedFamilyNonceCoupling.augmented_step source writer prior parent key target nonce next sender route read request
      (before.1.1.roles, (before.1.2, before.2))
    have mapped := congrArg (fun work => (fun result => (result.1, ({ before.1.1 with roles := result.2.1 }, result.2.2))) <$> work) actual
    simpa only [augmented, original, StateT.run, Functor.map_map, Prod.map_def, id_eq, project,
      RawCtxSelectedFamilyNonceCoupling.project, RawCtxSelectedReceiveCompiler.project] using mapped
  · have actual := PqxdhSelectedInitialOwnerCompiler.external_project pre application initial selector aux source key read
      (.inr (.inr (.inr (.inl request)))) (before.1.2, before.2)
    have mapped := congrArg (fun work => (fun result => (some result.1, (before.1.1, result.2))) <$> work) actual
    convert mapped using 1 <;> simp only [augmented, original, evaluated, impl, OptionT.run_mk, StateT.run, state_map_apply,
      PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair,
      simulateQ_map, Functor.map_map, Prod.map_def, id_eq, project,
      RawCtxSelectedReceiveCompiler.project]
    rfl
  · cases request with
    | finish index raw =>
      have actual := PqxdhSelectedInitialOwnerCompiler.program_source pre application initial selector aux source writer prior parent key target nonce next read
        (PqxdhSelectedInitialOwnerCompiler.owner raw (before.1.1.roles.1.2 index)) (before.1.2, before.2)
      have mapped := congrArg (fun work => (fun result => (some result.1.1, (install index before.1.1 result.1.2, result.2))) <$> work) actual
      convert mapped using 1 <;> simp only [augmented, original, evaluated, impl, OptionT.run_mk, StateT.run, state_map_apply,
        PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair,
        simulateQ_map, Functor.map_map, Prod.map_def, id_eq, project,
        RawCtxSelectedReceiveCompiler.project]

/-- Every adaptive original post schedule preserves its complete optional result and all source state under the same augmented ledger, including interleaved selectors and repeated attempted finishes. -/
theorem augmented_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Full M P I D K A N C S B) :
    Prod.map id project <$>
      (simulateQ (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before =
      (simulateQ (original pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (project before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ project
    (augmented_step pre application initial selector aux source writer prior parent key target nonce next sender route read)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient work) before

/-- The actual compiled and augmented post callbacks coincide until the exact selected-nonce stop, with the complete component ledger still present. -/
theorem augmented_nonstop (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (before : Full M P I D K A N C S B)
    (clear : ¬ Stops (extra := extra) prior parent target nonce next sender query before) :
    (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before =
      (evaluated pre application initial selector aux source writer prior parent key target nonce next sender route read query).run before := by
  rcases query with (request | request) | request
  · have actual := RawCtxSelectedFamilyNonceCoupling.augmented_nonstop source writer prior parent key target nonce next sender route read request
      (before.1.1.roles, (before.1.2, before.2)) clear
    have mapped := congrArg (fun work => (fun result => (result.1, (({ before.1.1 with roles := result.2.1 }, result.2.2.1), result.2.2.2))) <$> work) actual
    simpa only [augmented, evaluated, impl, OptionT.run_mk, StateT.run, state_map_apply,
      PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair,
      simulateQ_map, Functor.map_map, RawCtxSelectedFamilyNonceCoupling.compiled,
      RawCtxSelectedReceiveCompiler.evaluated] using mapped
  · rfl
  · cases request; rfl

/-- Evaluating the one executable post client equals its translated complete adaptive callback experiment, including internal stopping and both full states. -/
theorem evaluated_program (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) :
    PqxdhSelectedStateInterpreter.evaluate
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (simulateQ (impl (P := P) pre application initial selector aux source writer prior parent target nonce next sender route read) work).run =
      simulateQ (evaluated (P := P) pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work) := by
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client
    (impl (P := P) pre application initial selector aux source writer prior parent target nonce next sender route read) work]
  exact PqxdhSelectedStateInterpreter.program _ _ _

/-- The full interleaved post source and evaluated executable differ by at most the same augmented run's actual selected-nonce stop probability, with coefficient one and complete terminal output/state comparison. -/
theorem source_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (before : Full M P I D K A N C S B) :
    discreteDistance
      ((simulateQ (original pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (project before))
      (Prod.map id project <$> (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (simulateQ (impl pre application initial selector aux source writer prior parent target nonce next sender route read) work).run).run before) ≤
      (𝒟[(fun result => result.2.2) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
          (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read)
          (Stops (extra := extra) prior parent target nonce next sender))
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (before, false)] {true}).toReal := by
  have bound := (discreteDistance_map_le (Prod.map id project)
    ((simulateQ (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before)
    ((simulateQ (evaluated pre application initial selector aux source writer prior parent key target nonce next sender route read)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run before)).trans
      (RawCtxSelectedFamilyNonceCoupling.unmarked_distance
        (augmented pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (evaluated pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (Stops (extra := extra) prior parent target nonce next sender)
        (augmented_nonstop pre application initial selector aux source writer prior parent key target nonce next sender route read)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work) before)
  simpa only [augmented_program, evaluated_program] using bound

/-- Every outer source request makes at most one selected raw-opening attempt. Reveals and selectors make none; preparation and known-key primitive work retain their separate ledgers. -/
theorem step_opens (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : State M P I D K A N C S B) :
    (((impl pre application initial selector aux source writer prior parent target nonce next sender route read query).run).run before).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 1 := by
  rcases query with (request | request) | request
  · simp only [impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    have actual := RawCtxSelectedFamilyLiveCompiler.step_queries source writer prior parent target nonce next sender route read request before.1.roles
    exact (IsQueryBoundP.of_imp (fun _ _ => True.intro) ((isQueryBoundP_true_iff _ _).mpr actual)).mono
      (by cases request <;> simp only [RawCtxRevealBudgets.weight] <;> omega)
  · simp only [impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    exact (PqxdhSelectedInitialOwnerCompiler.external_no_open pre application initial selector aux
      (.inr (.inr (.inr (.inl request)))) before.2).mono (by omega)
  · cases request with
    | finish index raw =>
      simp only [impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
      exact PqxdhSelectedInitialOwnerCompiler.compiled_opens pre application initial selector aux prior parent target nonce next read raw (before.1.roles.1.2 index) before.2

/-- The actual adaptive outer query budget bounds every selected verification attempt, including rejected raw records and later attempted registrations. -/
theorem client_opens (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (qPost : Nat)
    (bounded : work.IsTotalQueryBound qPost) (before : State M P I D K A N C S B) :
    (client pre application initial selector aux source writer prior parent target nonce next sender route read work before).IsQueryBoundP
      (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) qPost := by
  induction work using OracleComp.inductionOn generalizing qPost before with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    simp only [client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    apply isQueryBoundP_bind (step_opens pre application initial selector aux source writer prior parent target nonce next sender route read query before)
    rintro ⟨none | answer, after⟩ _
    · trivial
    · exact ih answer remaining (by simpa using bounded.2 answer) after

end BeaconcryptCore.Computational.PqxdhSelectedPostCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_step
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_program
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_nonstop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.augmented_nonstop
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.evaluated_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.evaluated_program
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.source_distance
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.step_opens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.step_opens
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.client_opens' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedPostCompiler.client_opens
