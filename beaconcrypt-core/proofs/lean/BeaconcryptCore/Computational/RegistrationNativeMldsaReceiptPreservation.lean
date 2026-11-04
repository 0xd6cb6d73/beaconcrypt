-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign
import BeaconcryptCore.Computational.RegistrationNativeInitFinal
import BeaconcryptCore.Computational.RegistrationNativeMldsaCreation

/-! All original native callbacks outside outgoing ML publication retain the literal prior ML receipt list. Creation suffixes use only ordinary source operations after their named generation leaf; incoming finish and authentication cannot fabricate a signing receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaNoSign (Holds)
open RegistrationNativeBeaconFrontend (M)
variable {n : Nat} {ι KemSK Value Next Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerSdkSource.afterAuthentication
  RegistrationServerNativeSource.authenticate RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

def receipts (before : RegistrationNativeExperiment.State n KemSK source) := before.server.world.world.2

/-- A local controller with no ML receipt operation restores exactly its literal prior global prefix. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value) (law : Holds work)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    receipts result.2 = receipts before := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  apply law before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) inner.1
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

/-- Server lenses retain the enclosing raw native history whenever their actual frontend source body does. -/
theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (law : ∀ before result, result ∈ support (work.run before) → result.2.world.world.2 = before.world.world.2)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) :
    receipts result.2 = receipts before := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact law before.server inner possible

/-- Actual World operations never alter the separate ML attempt prefix. -/
theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) :
    receipts result.2 = receipts before := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

/-- Every original Server and Beacon ordinary record callback retains the exact earlier ML signing receipts. -/
theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) :
    receipts result.2 = receipts before := by
  cases query with
  | inl query => exact world _ before result supported
  | inr query =>
      rcases query with ⟨index, query⟩
      cases query <;> cases found : before.beacons[index]? with
      | none =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          rfl
      | some owner =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found] at supported
          exact world _ before result supported

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m]
    (value : A) (before : S) : (pure value : StateT S m A) before = pure (value, before) := rfl

/-- Actual incoming Init authentication, replay, reservation, agreement and token retention keep the literal earlier signing prefix on every outcome. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before : RegistrationServerFrontendCompiler.State n)
    (result : RustM (Option Nat) × RegistrationServerFrontendCompiler.State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route source.verify representation created packet).run before)) :
    result.2.world.world.2 = before.world.world.2 := by
  rw [RegistrationServerSdkSource.accept, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, first, continued⟩ := supported
  rw [RegistrationNativeInitAuthentication.authenticate setup codec route source.verify created packet before, support_map] at first
  obtain ⟨reached, _possible, same⟩ := first
  subst middle
  dsimp only [Prod.map, id] at continued
  rcases reached with ⟨reply, reached⟩
  cases reply with
  | fail error | div =>
      simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      rfl
  | ok checked =>
      rcases checked with ⟨events, authentication⟩
      cases authentication with
      | Accepted authenticated =>
          have sameSummary := RegistrationNativeInitFinal.afterAuthentication setup checks representation created packet authenticated
            (RegistrationNativeInitAuthentication.withWorld before reached) result continued
          exact congrArg (fun value : RegistrationSigningShared.State => value.1) sameSummary
      | _ =>
          simp only [StateT.run, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          rfl

def NonSigning : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.create _ _ _) | .inr (.bundle _) | .inr (.build _ _) => False
  | _ => True

/-- Every original typed non-signing callback preserves its complete global ML signing prefix. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : NonSigning query)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    receipts result.2 = receipts before := by
  cases query with
  | inl coin => exact world _ before result supported
  | inr query => cases query with
    | create _ _ _ | bundle _ | build _ _ => exact False.elim allowed
    | finish index packet =>
        change result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before) at supported
        exact beacon setup checks representation created _ (RegistrationNativeMldsaNoSign.finish setup wire index packet) before result supported
    | accept packet =>
        change result ∈ support ((RegistrationNativeExperiment.server
          (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
            representation created packet)).run { before with parsedAccepts := before.parsedAccepts + 1 }) at supported
        exact server _ (accept setup (RegistrationNativeWire.ledgerCodec wire) checks route representation created packet)
          { before with parsedAccepts := before.parsedAccepts + 1 } result supported
    | hash bytes => exact world _ before result supported
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        rfl
    | serverSend keyId plaintext => exact record setup wire route (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record setup wire route (.inl (.inr raw)) before result supported
    | beaconSend index plaintext => exact record setup wire route (.inr (index, .inl plaintext)) before result supported
    | beaconRaw index raw => exact record setup wire route (.inr (index, .inr raw)) before result supported

private theorem pure_holds (value : Value) : Holds (pure value : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem bind_holds (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → M n KemSK source RegistrationServerRoleBackend.State Next)
    (first : Holds work) (rest : ∀ value, Holds (next value)) : Holds (work >>= next) := by
  intro owners env result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first owners env middle queried)
private theorem trusted_holds (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    Holds (StateT.lift (StateT.lift work) : M n KemSK source RegistrationServerRoleBackend.State Value) := by
  intro owners env result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl
private theorem simulate_holds {Query : Type} {queries : OracleSpec Query}
    (implementation : QueryImpl queries (M n KemSK source RegistrationServerRoleBackend.State))
    (law : ∀ query, Holds (implementation query)) (work : OracleComp queries Value) : Holds (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_holds value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_holds _ _ (law query) ih
private theorem sample_holds (draw : ProbComp Value) : Holds
    (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source)
      (Auxiliary := RegistrationServerRoleBackend.State) draw) := by
  unfold RegistrationNativeBeaconFrontend.sample
  exact simulate_holds (fun (query : unifSpec.Domain) => RegistrationNativeBeaconFrontend.effect (.inl query))
    (fun _ => trusted_holds _) draw
private theorem get_holds : Holds
    (get : M n KemSK source RegistrationServerRoleBackend.State (RegistrationNativeBeaconFrontend.State source)) := by
  intro owners env result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl
private theorem set_holds (owners : RegistrationNativeBeaconFrontend.State source) :
    Holds (set owners : M n KemSK source RegistrationServerRoleBackend.State Unit) := by
  intro current env result supported
  simp only [StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

/-- The actual post-generation creation suffix has no signing callback; all original preflight, fingerprint, identity, KEM-birth and owner-allocation outcomes retain the earlier ML prefix. -/
theorem createSuffix (setup : Setup base KemSK) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential source)) :
    Holds (RegistrationNativeMldsaCreation.createSuffix (n := n) setup edPin mlPin keyId generated) := by
  have prepareLaw : Holds (RegistrationNativeMldsaCreation.afterGenerated (n := n) (KemSK := KemSK) edPin mlPin keyId generated) := by
    unfold RegistrationNativeMldsaCreation.afterGenerated
    cases generated with
    | none => exact pure_holds _
    | some credential =>
        dsimp only
        cases registration.begin_server_pin ⟨edPin, keyId⟩ mlPin with
        | fail error | div => exact pure_holds _
        | ok pending =>
            dsimp only
            cases pending.request with
            | fail error | div => exact pure_holds _
            | ok request =>
                apply bind_holds _ _ (trusted_holds _)
                intro digest
                cases pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)) with
                | fail error | div => exact pure_holds _
                | ok option => cases option with
                  | none => exact pure_holds _
                  | some pin => exact bind_holds _ _ (sample_holds _) (fun _ =>
                      bind_holds _ _ (sample_holds _) (fun _ => pure_holds _))
  unfold RegistrationNativeMldsaCreation.createSuffix
  apply bind_holds _ _ prepareLaw
  intro prepared
  cases prepared with
  | fail error | div => exact pure_holds _
  | ok option => cases option with
    | none => exact pure_holds _
    | some prepared =>
        unfold RegistrationNativeBeaconFrontend.appendBorn
        apply bind_holds _ _ (trusted_holds _)
        intro born
        apply bind_holds _ _ (trusted_holds _)
        intro worldOwner
        apply bind_holds _ _ get_holds
        intro owners
        apply bind_holds _ _ (set_holds _)
        intro ignored
        exact pure_holds _

/-- Closing that same actual suffix preserves its literal complete native global signing prefix. -/
theorem source_createSuffix (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64)
    (generated : Option (RegistrationNativeMldsa.Credential source))
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeMldsaCreation.createSuffix setup edPin mlPin keyId generated)).run before)) :
    receipts result.2 = receipts before :=
  beacon setup checks representation created _ (createSuffix setup edPin mlPin keyId generated) before result supported

end BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.beacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.world
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.createSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.createSuffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.source_createSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation.source_createSuffix
