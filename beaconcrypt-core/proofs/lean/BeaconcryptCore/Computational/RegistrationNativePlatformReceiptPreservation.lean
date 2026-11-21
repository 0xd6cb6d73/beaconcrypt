-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableHandler
import BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt

/-! Corrected incoming source callbacks preserve the literal chronological ML signing prefix and private ML pool. Pure pin selection, actual shared AD hashing, dynamic reservations, assigned-ID copy/install and all failed poststates remain in the same common state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeMldsaNoSign (Holds)
variable {n : Nat} {KemSK Auxiliary Platform Value Next Reader Response ι : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem pure_holds (value : Value) : Holds (pure value : M n KemSK source Auxiliary Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_holds (work : M n KemSK source Auxiliary Value) (next : Value → M n KemSK source Auxiliary Next)
    (first : Holds work) (rest : ∀ value, Holds (next value)) : Holds (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle reached)

private theorem get_holds : Holds (get : M n KemSK source Auxiliary (State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem modify_holds (change : State source → State source) :
    Holds (modify change : M n KemSK source Auxiliary Unit) := by
  intro owners env result supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem update_holds (change : EnvState Auxiliary → EnvState Auxiliary)
    (same : ∀ env, (change env).receipts = env.receipts) :
    Holds (updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) change) := by
  intro owners env result supported
  simp only [updateEnv, StateT.run_lift, StateT.run_modify, bind_pure_comp, StateT.run_map,
    map_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact same env

private theorem trusted_holds (query : (Trusted n KemSK).Domain) :
    Holds (StateT.lift (StateT.lift ((Trusted n KemSK).query query)) : M n KemSK source Auxiliary _) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem simulate_holds {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl spec (M n KemSK source Auxiliary))
    (law : ∀ query, Holds (implementation query)) (work : OracleComp spec Value) : Holds (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_holds value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_holds _ _ (law query) ih

private theorem effect_holds (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Holds (effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) := trusted_holds _
private theorem kem_holds (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Holds (kem (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) query) := trusted_holds _
private theorem sample_holds (draw : ProbComp Value) :
    Holds (sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) draw) :=
  simulate_holds (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => effect_holds _) draw
private theorem phase_holds (index : Nat) (phase : Phase) :
    Holds (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) index phase) := modify_holds _

private theorem authentication_holds (setup : Setup base KemSK) (query : RegistrationAuthenticationExecutor.Spec.Domain) :
    Holds (authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)
  | mldsa request | ed25519 request => exact pure_holds _

private theorem primitive_holds (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    Holds (primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) :=
  simulate_holds _ (fun lower => match lower with
    | .inl _ => sample_holds _
    | .inr _ => kem_holds _) _

private theorem agreement_holds (setup : Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Spec.Domain) :
    Holds (agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold agreement
  apply bind_holds _ _ (update_holds
    (fun env => { env with requests := env.requests ++ RegistrationWorldAgreement.recorded query }) (fun _ => rfl))
  intro ignored
  cases query with
  | root request => exact pure_holds _
  | _ => exact primitive_holds setup owner oneTime _

private theorem record_holds (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Spec.Domain) : Holds (record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query) := by
  unfold record
  apply bind_holds _ _ (update_holds
    (fun env => { env with recordRequests := env.recordRequests ++ [RegistrationWorldAgreement.recordCall query] }) (fun _ => rfl))
  intro ignored
  cases query with
  | adHash request => exact bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)
  | hash request => exact bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)
  | _ => exact sample_holds _

private theorem abort_holds (owner : Owner source) :
    Holds (abort (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) owner) :=
  bind_holds _ _ (effect_holds _) (fun _ => pure_holds _)

private theorem abort_pure (owner : Owner source) (value : Value) :
    Holds (RegistrationNativeBeaconFrontend.abort owner *> pure value : M n KemSK source Auxiliary Value) := by
  simp only [seqRight_eq_bind]
  exact bind_holds _ _ (abort_holds owner) (fun _ => pure_holds value)

private theorem install (index : Nat) (owner : Owner source) (completed : registration.CompletedBeacon) :
    Holds (RegistrationNativePlatformBeaconFinish.install (n := n) (KemSK := KemSK) (Auxiliary := Auxiliary) index owner completed) := by
  rw [RegistrationNativePlatformBeaconFinish.install_exact]
  apply bind_holds _ _ (effect_holds _)
  intro installed
  cases installed with
  | false => exact abort_pure owner _
  | true => exact bind_holds _ _ (phase_holds index _) (fun _ => pure_holds _)

private theorem after (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (accepted : registration.AuthenticatedResponse) :
    Holds (RegistrationNativePlatformBeaconFinish.afterAuthentication (n := n) (Auxiliary := Auxiliary) setup wire index owner oneTime accepted) := by
  unfold RegistrationNativePlatformBeaconFinish.afterAuthentication RegistrationNativePlatformBeaconFinish.afterAuthenticationWith
  apply bind_holds _ _ (simulate_holds _ (agreement_holds setup owner oneTime) _)
  intro agreed
  cases agreed with
  | fail error | div => exact abort_pure owner _
  | ok effect =>
    cases effect
    all_goals first
      | exact abort_pure owner _
      | apply bind_holds _ _ (simulate_holds _ (record_holds setup wire) _)
        intro opened
        cases opened with
        | fail error | div => exact abort_pure owner _
        | ok answer => cases answer with
          | Err prior => exact abort_pure owner _
          | Ok completed => exact install index owner completed

/-- Actual corrected source finish is independent of the separate local record-kind ledger, including assigned-ID installation. -/
theorem finish_holds (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (index : Nat)
    (packet : Option registration.ResponsePacket) :
    Holds (RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := Auxiliary) setup source wire index packet) := by
  unfold RegistrationNativePlatformBeaconFinish.finish RegistrationNativePlatformBeaconFinish.finishWith
  apply bind_holds _ _ get_holds
  intro owners
  cases owners[index]? with
  | none => exact pure_holds _
  | some owner =>
    dsimp only
    cases owner.phase with
    | fresh | freshWithCoins oneTime | established completed | aborted prior => exact pure_holds _
    | initSent pending oneTime =>
      dsimp only
      cases pending.aborted_state with
      | fail error | div => exact pure_holds _
      | ok aborted =>
        apply bind_holds _ _ (phase_holds index _)
        intro _changed
        apply bind_holds _ _ (simulate_holds _ (authentication_holds setup) _)
        intro authenticated
        cases authenticated with
        | fail error | div => exact abort_pure owner _
        | ok answer => cases answer with
          | Err prior => exact abort_pure owner _
          | Ok accepted => exact after setup wire index owner oneTime accepted



private def Quiet {S W : Type} (field : S → W) (work : StateT S (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → field result.1.2 = field before

private theorem quiet_pure {S W : Type} (field : S → W) (value : Value) :
    Quiet (Platform := Platform) field (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem quiet_bind {S W : Type} (field : S → W)
    (work : StateT S (StateT Platform ProbComp) Value) (next : Value → StateT S (StateT Platform ProbComp) Next)
    (first : Quiet field work) (rest : ∀ value, Quiet field (next value)) : Quiet field (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

private theorem quiet_get {S W : Type} (field : S → W) :
    Quiet (Platform := Platform) field (get : StateT S (StateT Platform ProbComp) S) := by
  intro before previous result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem quiet_external {S W : Type} (field : S → W) (work : StateT Platform ProbComp Value) :
    Quiet field (StateT.lift work : StateT S (StateT Platform ProbComp) Value) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem quiet_native {S W : Type} (field : S → W)
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (work : StateT S ProbComp Value)
    (keeps : ∀ before result, result ∈ support (work.run before) → field result.2 = field before) :
    Quiet field (fun before => simulateQ coins (work.run before)) := by
  intro before previous result supported
  exact keeps before result.1 (RegistrationNativePlatformHashReceipt.native_support coins _ _ _ _ supported)

private def frontReceipts (before : RegistrationServerFrontendCompiler.State n) := before.world.world.2

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _

attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin
  RegistrationServerNativeSource.agree RegistrationServerNativeSource.retain

private theorem pin_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Quiet (frontReceipts (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, state_map_apply, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem authenticate_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (verify : MldsaTranscriptAuth.Verify) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Quiet (frontReceipts (n := n)) (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run, state_map_apply, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem after_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Quiet (frontReceipts (n := n)) (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated) := by
  unfold RegistrationNativePlatformServerSdk.afterAuthentication
  apply quiet_bind frontReceipts _ _ (quiet_get _)
  intro before
  split
  · exact quiet_pure _ _
  · apply quiet_bind _ _ _ (quiet_external _ reserve)
    intro admitted
    cases admitted with
    | false => exact quiet_pure _ _
    | true =>
      apply quiet_bind _ _ _ (quiet_native frontReceipts coins _ (fun before result supported =>
        congrArg Prod.fst (RegistrationNativeInitFinal.agree setup checks representation created packet authenticated before result supported)))
      intro completed
      cases completed with
      | fail error | div => exact quiet_pure _ _
      | ok effect =>
        cases effect
        all_goals first
          | exact quiet_pure _ _
          | exact quiet_native frontReceipts coins _ (fun before result supported =>
              congrArg Prod.fst (RegistrationNativeInitFinal.retain created _ before result supported))

private theorem afterPin_quiet (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Quiet (frontReceipts (n := n)) (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve)
      route verify representation created packet pin) := by
  unfold RegistrationNativePlatformSourceAccept.afterPin
  cases pin with
  | fail error | div => exact quiet_pure _ _
  | ok optional => cases optional with
    | none => exact quiet_pure _ _
    | some pin =>
      apply quiet_bind _ _ _ (authenticate_quiet coins setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact quiet_pure _ _
      | ok answer =>
        rcases answer with ⟨events, status⟩
        cases status with
        | Accepted authenticated => exact after_quiet coins setup checks reserve representation created packet authenticated
        | _ => exact quiet_pure _ _

/-- Every actual source acceptance outcome retains the exact earlier ML signing prefix, including repeated pin hashing and external reservation failures. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat) × RegistrationServerFrontendCompiler.State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve
      route verify representation created packet).run before).run previous)) :
    result.1.2.world.world.2 = before.world.world.2 := by
  apply quiet_bind frontReceipts _ _ (pin_quiet coins) (afterPin_quiet coins setup codec checks reserve route verify representation created packet) before previous result supported


private theorem quiet_server (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (keeps : Quiet frontReceipts work) :
    Quiet (RegistrationNativeMldsaReceiptPreservation.receipts (source := source) (KemSK := KemSK)) (RegistrationNativePlatformExperiment.server work) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, state_map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact keeps before.server previous inner possible

private theorem quiet_parsed : Quiet (Platform := Platform)
    (RegistrationNativeMldsaReceiptPreservation.receipts (source := source) (n := n) (KemSK := KemSK))
    (modify fun before => { before with parsedAccepts := before.parsedAccepts + 1 }) := by
  intro before previous result supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

section Typed
variable [primitive : AdapterSealPrimitive.Operations]
variable {E : Type}
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The literal corrected typed incoming and ordinary callbacks retain their complete signing prefix under arbitrary shared ordinary coins and platform effects. -/
theorem source_handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    RegistrationNativeMldsaReceiptPreservation.receipts result.1.2 = RegistrationNativeMldsaReceiptPreservation.receipts before := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativePlatformExperiment.handler] at supported
    apply quiet_native RegistrationNativeMldsaReceiptPreservation.receipts coins _
      (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential _ allowed) before previous result supported
  | inr query => cases query with
    | create _ _ _ | bundle _ | build _ _ => exact False.elim allowed
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler] at supported
      apply quiet_bind RegistrationNativeMldsaReceiptPreservation.receipts _ _ quiet_parsed
        (fun _ => quiet_server _ (accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route source.verify representation created packet))
        before previous result supported
    | finish index packet =>
      simp only [RegistrationNativePlatformExperiment.handler] at supported
      apply quiet_native RegistrationNativeMldsaReceiptPreservation.receipts coins _
        (RegistrationNativeMldsaReceiptPreservation.beacon setup checks representation created _ (finish_holds setup wire index packet))
        before previous result supported
    | _ =>
      simp only [RegistrationNativePlatformExperiment.handler] at supported
      apply quiet_native RegistrationNativeMldsaReceiptPreservation.receipts coins _
        (RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential _ allowed) before previous result supported
end Typed

/-- A corrected callback outside generation and outgoing publication leaves the entire private ML pool and chronological native signing prefix unchanged. -/
theorem handler [primitive : AdapterSealPrimitive.Operations] {E : Type}
    (realSource : RegistrationNativeMldsa.Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential (RegistrationNativeMldsaOpaque.handleSource realSource))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) (previous : Platform)
    (pool : RegistrationNativeMldsaOpaque.Pool realSource)
    (result : ((RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (RegistrationNativeMldsaOpaque.handleSource realSource)) × Platform) × RegistrationNativeMldsaOpaque.Pool realSource)
    (supported : result ∈ support (RegistrationNativePlatformMldsaTableProgram.runState realSource
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) before previous pool)) :
    result.2 = pool ∧ RegistrationNativeMldsaReceiptPreservation.receipts result.1.1.2 = RegistrationNativeMldsaReceiptPreservation.receipts before := by
  have lifted : RegistrationNativePlatformMldsaProfile.handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query = RegistrationNativePlatformMldsaProgram.lift
      (RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created
        (RegistrationNativeMldsaOpaque.handleSource realSource) credential view failure allocation reserveRegistration reservePeer erased helper writer query) := by
    cases query with
    | inl coin => rfl
    | inr query => cases query with
      | create _ _ _ | bundle _ | build _ _ => exact False.elim allowed
      | _ => rfl
  rw [lifted, RegistrationNativePlatformMldsaTableProgram.run_lift, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact ⟨rfl, source_handler RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created credential
    view failure allocation reserveRegistration reservePeer erased helper writer query allowed before previous inner possible⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.finish_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.finish_holds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.source_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.source_handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformReceiptPreservation.handler
