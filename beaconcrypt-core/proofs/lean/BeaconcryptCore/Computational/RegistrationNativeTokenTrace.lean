-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTokenSource
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat
import BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-! Actual native token-table provenance through all complete callbacks and same-execution journals. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenTrace
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {n : Nat} {ι KemSK Value Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def sessions (before : RegistrationNativeExperiment.State n KemSK source) := before.server.sessions

/-- Actual environment and private indexed KEM calls retain the token table. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)) :
    sessions result.2 = sessions before := by
  cases query with
  | inl query =>
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl
  | inr query =>
      simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _possible, same⟩ := supported
      cases same
      rfl

/-- Complete actual trusted programs retain the exact token table. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before)) :
    sessions result.2 = sessions before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, first, continued⟩ := supported
      exact (ih middle.1 middle.2 result continued).trans
        (trusted setup checks representation created query before middle first)

/-- Native owner/environment closure cannot drop a hash receipt reached inside the actual callback. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    sessions result.2 = sessions before := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program setup checks representation created
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before inner possible


private theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) : sessions result.2 = sessions before := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

private theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) : sessions result.2 = sessions before := by
  cases query with
  | inl query => exact world _ before result supported
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query <;> cases found : before.beacons[owner]? with
      | none =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found, mem_support_pure_iff] at supported
          cases supported
          rfl
      | some selected =>
          simp only [RegistrationNativeExperiment.record, StateT.run, found] at supported
          exact world _ before result supported

open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "implementation" => RegistrationNativeExperiment.handler setup checks wire route representation created source credential
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerSdkSource.accept RegistrationServerSdkSource.build
  RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin

def SourceAt (call : Call RegistrationNativeRawAdapter.TypedSpec Native) (token : peer.ConsumedRegistration) : Prop :=
  ∃ packet events authenticated afterAuthentication,
    call.query = .inr (.accept packet) ∧
    (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
      ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet).run call.before.server) ∧
    Born setup checks representation created packet authenticated afterAuthentication token

set_option maxRecDepth 16384 in
private theorem accept_origin (packet : registration.InitPacket) (before after : Native)
    (reply : RustM (Option Nat))
    (called : (reply, after) ∈ support ((implementation (.inr (.accept packet))).run before))
    (token : peer.ConsumedRegistration) (present : Present token after.server) :
    Present token before.server ∨ SourceAt setup checks wire route representation created
      (⟨.inr (.accept packet), before, reply, after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) token := by
  simp only [RegistrationNativeExperiment.handler] at called
  change (reply, after) ∈ support ((RegistrationNativeExperiment.server
    (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify representation created packet)).run
    { before with parsedAccepts := before.parsedAccepts + 1 }) at called
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at called
  obtain ⟨inner, supported, same⟩ := called
  cases same
  rcases RegistrationNativeTokenSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
    representation created packet before.server inner supported token present with old | ⟨events, authenticated, middle, checked, born⟩
  · exact Or.inl old
  · exact Or.inr (show SourceAt setup checks wire route representation created
      (⟨.inr (.accept packet), before, inner.1, {before with parsedAccepts := before.parsedAccepts + 1, server := inner.2}⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) token from
      ⟨packet, events, authenticated, middle, rfl, checked, born⟩)

/-- Every live token survives from the callback input or comes from this actual accept's authentication and agreement chain. -/
theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Native)
    (called : Executed implementation call) (token : peer.ConsumedRegistration) (present : Present token call.after.server) :
    Present token call.before.server ∨ SourceAt setup checks wire route representation created call token := by
  rcases call with ⟨query, before, reply, after⟩
  change (reply, after) ∈ support ((implementation query).run before) at called
  cases query with
  | inl coin =>
      simp only [RegistrationNativeExperiment.handler] at called
      have same : after.server.sessions = before.server.sessions := world _ before (reply, after) called
      exact Or.inl (by simpa only [Present, same] using present)
  | inr query => cases query with
    | create edPin mlPin keyId | bundle owner | finish owner packet =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := beacon setup checks representation created _ before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)
    | build index application =>
        simp only [RegistrationNativeExperiment.handler, RegistrationNativeExperiment.server, StateT.run, support_map] at called
        obtain ⟨inner, supported, same⟩ := called
        cases same
        exact Or.inl (RegistrationNativeTokenSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks
          (RegistrationNativeMldsa.owned source credential) wire.encodeResponse index application before.server inner supported token present)
    | accept packet => exact accept_origin setup checks wire route representation created credential packet before after reply called token present
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, mem_support_pure_iff] at called
        cases called
        exact Or.inl present
    | hash bytes =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := world _ before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)
    | serverSend keyId plaintext =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := record setup wire route (.inl (.inl (plaintext, keyId))) before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)
    | serverRaw raw =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := record setup wire route (.inl (.inr raw)) before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)
    | beaconSend owner plaintext =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := record setup wire route (.inr (owner, .inl plaintext)) before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)
    | beaconRaw owner raw =>
        simp only [RegistrationNativeExperiment.handler] at called
        have same : after.server.sessions = before.server.sessions := record setup wire route (.inr (owner, .inr raw)) before (reply, after) called
        exact Or.inl (by simpa only [Present, same] using present)

/-- A source path derives the earlier accept provenance of every live final token. -/
theorem path_origin {first last : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls last) (token : peer.ConsumedRegistration) (present : Present token last.server) :
    Present token first.server ∨ ∃ call ∈ calls, SourceAt setup checks wire route representation created call token := by
  induction actual with
  | nil => exact Or.inl present
  | cons call called rest last following ih =>
      rcases ih present with old | ⟨earlier, member, origin⟩
      · rcases call_origin setup checks wire route representation created credential call called token old with initial | born
        · exact Or.inl initial
        · exact Or.inr ⟨call, List.mem_cons_self, born⟩
      · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

private theorem world_start_empty (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (publicKey : Std.Array U8 1952#usize) (before after : PqxdhRecordLiftWorld.State n)
    (native : RegistrationWorldServerFrontend.State n RegistrationServerRoleBackend.State)
    (supported : (.ok (.Some native), after) ∈ support
      ((RegistrationWorldServerFrontend.start created publicKey RegistrationServerRoleBackend.empty).run before)) :
    native.sessions = [] := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨installed, _first, pinned, _second, returned⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at returned
  rcases pinned with ⟨reply, current⟩
  cases reply with
  | fail error | div => cases returned
  | ok option => cases option with
    | none => cases returned
    | some pin => cases returned; rfl

/-- Effectful actual startup creates an empty registration-token table. -/
theorem start_empty (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid)) :
    initial.state.server.sessions = [] := by
  delta RegistrationNativeExperiment.start at startup
  simp only [mem_support_bind_iff] at startup
  obtain ⟨constructed, _constructor, continued⟩ := startup
  cases born : constructed.1.1 with
  | none =>
      simp only [born, support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | some created =>
      simp only [born, mem_support_bind_iff] at continued
      obtain ⟨generated, _generation, continued⟩ := continued
      cases keyed : generated.1 with
      | none =>
          simp only [keyed, support_pure, Set.mem_singleton_iff] at continued
          cases continued
      | some credential =>
          simp only [keyed, mem_support_bind_iff] at continued
          obtain ⟨initialized, possible, returned⟩ := continued
          rcases initialized with ⟨reply, after⟩
          cases reply with
          | fail error | div =>
              simp only [support_pure, Set.mem_singleton_iff] at returned
              cases returned
          | ok option => cases option with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
            | some native =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
                exact world_start_empty created credential.publicKey generated.2 after native possible

/-- A token consumed by a same-run build has a genuine earlier accept stage in its actual leading. -/
theorem taken_origin {first beforeBuild : Native} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)}
    (actual : Path implementation first calls beforeBuild) (empty : first.server.sessions = [])
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take index beforeBuild.server = (some token, current)) :
    ∃ call leading trailing,
      calls = leading ++ call :: trailing ∧ Path implementation first leading call.before ∧
      Executed implementation call ∧ Path implementation call.after trailing beforeBuild ∧
      SourceAt setup checks wire route representation created call token := by
  have found := (RegistrationNativeTokenSource.take_origin index beforeBuild.server current token taken).1
  have present : Present token beforeBuild.server := List.mem_of_getElem? found
  rcases path_origin setup checks wire route representation created credential actual token present with initial | ⟨call, member, origin⟩
  · simp only [Present, empty, List.not_mem_nil] at initial
  · obtain ⟨leading, trailing, split, earlier, called, later⟩ := actual.member call member
    exact ⟨call, leading, trailing, split, earlier, called, later, origin⟩

end BeaconcryptCore.Computational.RegistrationNativeTokenTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.call_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.call_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.start_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenTrace.taken_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenTrace.taken_origin
