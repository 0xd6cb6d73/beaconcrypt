-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerTrace
import BeaconcryptCore.Computational.RegistrationNativeKemServerRecipientMarker

/-! Successful actual corrected acceptance retains a token only after its actual same-log Server Root and encapsulation block. All authentication, repeated pin, reservation and retention prefixes remain in their original order and state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedServerTrace (Log)
open RegistrationNativePlatformKemCountedAccept
variable {n : Nat} {ι KemSK Platform Value Next Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK
local notation "Client" => State n source
local notation "M" => RegistrationNativePlatformKemCountedProgram.M KemSK Platform

private def run (work : StateT Client M Value) (before : Client) (previous : Platform) :
    OracleComp CP ((Value × Client) × Platform) := (work.run before).run previous

private theorem bind_cut (work : StateT Client M Value) (next : Value → StateT Client M Next)
    (before : Client) (previous : Platform) (result : (Next × Client) × Platform) (log : Log KemSK)
    (supported : (result, log) ∈ support (run (work >>= next) before previous).withQueryLog) :
    ∃ (first : (Value × Client) × Platform) (prefixLog suffixLog : Log KemSK),
      (first, prefixLog) ∈ support (run work before previous).withQueryLog ∧
      (result, suffixLog) ∈ support (run (next first.1.1) first.1.2 first.2).withQueryLog ∧
      log = prefixLog ++ suffixLog := by
  simp only [run, StateT.run_bind, withQueryLog_bind, mem_support_bind_iff, support_map] at supported
  obtain ⟨⟨first, prefixLog⟩, head, ⟨last, suffixLog⟩, tail, returned⟩ := supported
  simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
  rcases returned with ⟨rfl, rfl⟩
  exact ⟨first, prefixLog, suffixLog, head, tail, rfl⟩

private theorem pure_cut (value : Value) (before : Client) (previous : Platform)
    (result : (Value × Client) × Platform) (log : Log KemSK)
    (supported : (result, log) ∈ support (run (pure value) before previous).withQueryLog) :
    result = ((value, before), previous) ∧ log = [] := by
  simpa only [run, StateT.run_pure, withQueryLog_pure, support_pure, Set.mem_singleton_iff,
    Prod.mk.injEq] using supported

/-- The completed Server's exact private Root preimage and its same lower-log actual encapsulation receipt. -/
structure RootWitness (setup : Setup base KemSK) (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (accepted : agreement.ServerAgreement) (log : Log KemSK) where
  input : RegistrationServerEncapsulationTrace.Input
  next : pqxdh.ServerState
  original : pqxdh.PendingServerRegistration
  reply : PqxdhBeaconPhase2Preparation.Word32
  cost : Nat
  derived : reply = RegistrationAgreementShared.rootResponse setup.source.crypto ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩
  verified : input.verified = RegistrationRootInput.verified packet authenticated
  admitted : PqxdhServerRelatedRootInput.accept control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original))
  completed : accepted = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ }, authenticated.binding, ⟨reply⟩⟩
  bytes : absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
    (absBytes input.first) (absBytes input.second) (absBytes input.third) (absBytes input.fourth) (absBytes input.kem)
  encapsulated : (⟨.inr (.inr input.verified.keys.pqKey),
    ((PqxdhPhase2InputBytes.ciphertext input.ciphertext, PqxdhPhase2InputBytes.word input.kem), cost)⟩) ∈ log

private theorem RootWitness.append (setup : Setup base KemSK) (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (accepted : agreement.ServerAgreement)
    (prefixLog log suffixLog : Log KemSK) (witness : RootWitness setup control packet authenticated accepted log) :
    Nonempty (RootWitness setup control packet authenticated accepted (prefixLog ++ log ++ suffixLog)) := by
  exact ⟨{ witness with encapsulated := List.mem_append_left _ (List.mem_append_right _ witness.encapsulated) }⟩

private def RootCorrect (setup : Setup base KemSK) (entry : RegistrationAgreementQueryTrace.Entry) : Prop :=
  match entry with
  | ⟨.root request, reply⟩ => reply = .Some (RegistrationAgreementShared.rootResponse setup.source.crypto request)
  | _ => True

private theorem root_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (query : RegistrationAgreementExecutor.Request)
    (before : Client) (reply : RegistrationAgreementExecutor.Spec.Range query) (after : Client) (log : Log KemSK)
    (supported : ((reply, after), log) ∈ support
      ((RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created query).run before).withQueryLog) :
    RootCorrect setup ⟨query, reply⟩ := by
  cases query <;> try trivial
  rename_i request
  simp only [RegistrationNativeKemCountedServerPrimitive.agreement, StateT.run_bind, StateT.run_modify,
    pure_bind, RegistrationNativeKemCountedServerPrimitive.core, StateT.run_pure, withQueryLog_pure,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  rw [supported.1.1]
  trivial

private theorem agree_cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (accepted : agreement.ServerAgreement)
    (before after : Client) (log : Log KemSK)
    (supported : ((.ok (.ServerComplete accepted), after), log) ∈ support
      ((RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated).run before).withQueryLog) :
    Nonempty (RootWitness setup before.server.control packet authenticated accepted log) := by
  simp only [RegistrationNativeKemCountedServerPrimitive.agree, StateT.run_bind,
    StateT.run_get, pure_bind, RegistrationReplaySchedule.begin_eq] at supported
  cases consumed : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) with
  | false =>
    simp only [consumed, Bool.false_eq_true, ite_false] at supported
    obtain ⟨journal, traced⟩ := RegistrationAgreementMacroTrace.lift_support
      (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
      (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) before after
      (.ok (.ServerComplete accepted)) log supported
    obtain ⟨input, next, original, reply, cost, verified, admitted, complete, _journal, bytes, actual⟩ :=
      RegistrationNativeKemCountedServerTrace.server setup checks representation created before.server.control packet authenticated
        accepted journal before after log traced
    have laws := RegistrationAgreementMacroTrace.program
      (RegistrationNativeKemCountedServerPrimitive.agreement setup checks representation created)
      (fun entry _ => RootCorrect setup entry) (fun _ _ _ fact => fact) (fun _ _ _ fact => fact)
      (root_query setup checks representation created)
      (RegistrationAgreementExecutor.server before.server.control .Fresh authenticated) [] journal before after
      (.ok (.ServerComplete accepted)) log traced
    have rootMember : (⟨.root ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩, .Some reply⟩ : RegistrationAgreementQueryTrace.Entry) ∈ journal := by
      rw [_journal]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have rootLaw := (laws _ rootMember).resolve_left (List.not_mem_nil)
    change core.option.Option.Some reply = .Some (RegistrationAgreementShared.rootResponse setup.source.crypto
      ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩) at rootLaw
    exact ⟨⟨input, next, original, reply, cost, Option.some.inj rootLaw, verified, admitted, complete, bytes, actual⟩⟩
  | true =>
    simp only [consumed, ite_true, simulateQ_pure, StateT.run_pure, withQueryLog_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    cases supported.1.1

private theorem pure_success (value : RustM (Option Nat)) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK)
    (supported : (((.ok (some handle), after), finalPlatform), log) ∈ support
      (run (pure value) before previous).withQueryLog) : value = .ok (some handle) := by
  have same := (pure_cut value before previous _ log supported).1
  exact (congrArg (fun result => result.1.1) same).symm

private theorem inject_run (work : StateT Client (OracleComp CP) Value) (before : Client) (previous : Platform) :
    run (RegistrationNativePlatformKemCountedProgram.inject work) before previous =
      (fun result => (result, previous)) <$> work.run before := by
  change (work.run before >>= fun result => pure (result, previous)) = _
  exact bind_pure_comp _ _

/-- An actual retained one-use token is connected to its actual completed Server agreement and same-log private Root input. -/
structure Cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat)
    (after : Client) (finalPlatform : Platform) (log : Log KemSK) where
  beforeAgreement : Client
  afterAgreement : Client
  atPlatform : Platform
  accepted : agreement.ServerAgreement
  agreementLog : Log KemSK
  retainLog : Log KemSK
  agreed : ((.ok (.ServerComplete accepted), afterAgreement), agreementLog) ∈ support
    ((RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated).run beforeAgreement).withQueryLog
  retained : (((.ok (some handle), after), finalPlatform), retainLog) ∈ support
    (run (ordinaryServer (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins
      (RegistrationServerNativeSource.retain created accepted))) afterAgreement atPlatform).withQueryLog
  root : RootWitness setup beforeAgreement.server.control packet authenticated accepted log

/-- Actual successful replay/reservation/agreement/retention supplies its private Root/encapsulation receipt in the same complete lower log. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : Client) (previous finalPlatform : Platform)
    (handle : Nat) (log : Log KemSK)
    (supported : (((.ok (some handle), after), finalPlatform), log) ∈ support
      (run (RegistrationNativePlatformKemCountedAccept.afterAuthentication setup checks reserve representation created packet authenticated)
        before previous).withQueryLog) :
    Nonempty (Cut setup checks representation created packet authenticated handle after finalPlatform log) := by
  change (((.ok (some handle), after), finalPlatform), log) ∈ support
    (run (if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
      else do
        let admitted ← ordinaryServer reserve
        if admitted then do
          let completed ← RegistrationNativePlatformKemCountedProgram.inject
            (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)
          match completed with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok (.ServerComplete accepted) => ordinaryServer (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins (RegistrationServerNativeSource.retain created accepted))
          | .ok _ => pure (.ok none)
        else pure (.ok none)) before previous).withQueryLog at supported
  split at supported
  · cases pure_success (.ok none) before previous handle after finalPlatform log supported
  · obtain ⟨⟨⟨allowed, reserved⟩, reservedPlatform⟩, prefixLog, laterLog, _reserved, later, full⟩ :=
      bind_cut (ordinaryServer reserve) _ before previous _ log supported
    cases allowed with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at later
      cases pure_success (.ok none) reserved reservedPlatform handle after finalPlatform laterLog later
    | true =>
      simp only [ite_true] at later
      obtain ⟨⟨⟨effect, agreed⟩, agreedPlatform⟩, agreementLog, retainLog, actualAgree, retained, splitLog⟩ :=
        bind_cut (RegistrationNativePlatformKemCountedProgram.inject
          (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated))
          _ reserved reservedPlatform _ laterLog later
      rw [inject_run, RegistrationAgreementMacroTrace.logging_map, support_map] at actualAgree
      obtain ⟨⟨⟨actualEffect, actualAgreed⟩, actualLog⟩, ran, same⟩ := actualAgree
      simp only [Prod.map, id_eq, Prod.mk.injEq] at same
      rcases same with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      cases actualEffect with
      | fail error => cases pure_success (.fail error) actualAgreed reservedPlatform handle after finalPlatform retainLog retained
      | div => cases pure_success .div actualAgreed reservedPlatform handle after finalPlatform retainLog retained
      | ok answer =>
        cases answer <;> try {
          cases pure_success (.ok none) actualAgreed reservedPlatform handle after finalPlatform retainLog retained }
        case ServerComplete accepted =>
          obtain ⟨root⟩ := agree_cut setup checks representation created packet authenticated accepted reserved actualAgreed actualLog ran
          obtain ⟨extended⟩ := RootWitness.append setup _ packet authenticated accepted prefixLog actualLog retainLog root
          have sameLog : log = prefixLog ++ actualLog ++ retainLog := by
            rw [full, splitLog, List.append_assoc]
          rw [sameLog]
          exact ⟨⟨reserved, actualAgreed, reservedPlatform, accepted, actualLog, retainLog, ran, retained, extended⟩⟩

private theorem Cut.extend (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat) (after : Client) (finalPlatform : Platform)
    (prefixLog log suffixLog : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log) :
    Nonempty (Cut setup checks representation created packet authenticated handle after finalPlatform (prefixLog ++ log ++ suffixLog)) := by
  obtain ⟨root⟩ := RootWitness.append setup _ packet authenticated receipt.accepted prefixLog log suffixLog receipt.root
  exact ⟨{ receipt with root := root }⟩

attribute [local irreducible] RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformServerSdk.liftNative

/-- The actual mandatory authentication prefix and the retained token's actual Root cut share this same callback log. -/
structure CheckedCut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (pin : session.ServerAuthenticationPin) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK) where
  authenticated : registration.AuthenticatedInit
  events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event
  afterCheck : Client
  checkPlatform : Platform
  checkLog : Log KemSK
  checked : (((.ok (events, .Accepted authenticated), afterCheck), checkPlatform), checkLog) ∈ support
    (run (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route source.verify pin packet))
      before previous).withQueryLog
  root : Cut setup checks representation created packet authenticated handle after finalPlatform log

private theorem CheckedCut.extend (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (pin : session.ServerAuthenticationPin) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (prefixLog log suffixLog : Log KemSK)
    (receipt : CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform log) :
    Nonempty (CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform (prefixLog ++ log ++ suffixLog)) := by
  obtain ⟨root⟩ := Cut.extend setup checks representation created packet receipt.authenticated handle after finalPlatform prefixLog log suffixLog receipt.root
  exact ⟨{ receipt with root := root }⟩

/-- A successful actual post-pin accept derives its mandatory authentication and completed same-log Root cut; all failed authentication branches are excluded by their literal returned values. -/
theorem afterPin (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin))
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (supported : (((.ok (some handle), after), finalPlatform), log) ∈ support
      (run (RegistrationNativePlatformKemCountedAccept.afterPin setup codec checks reserve route representation created packet pinResult)
        before previous).withQueryLog) :
    ∃ pin, pinResult = .ok (.Some pin) ∧
      Nonempty (CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform log) := by
  unfold RegistrationNativePlatformKemCountedAccept.afterPin at supported
  cases pinResult with
  | fail error => cases pure_success (.fail error) before previous handle after finalPlatform log supported
  | div => cases pure_success .div before previous handle after finalPlatform log supported
  | ok option =>
    cases option with
    | none => cases pure_success (.ok none) before previous handle after finalPlatform log supported
    | some pin =>
      obtain ⟨⟨⟨checked, current⟩, currentPlatform⟩, checkLog, laterLog, verified, later, full⟩ :=
        bind_cut (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins
          setup codec route source.verify pin packet)) _ before previous _ log supported
      cases checked with
      | fail error => cases pure_success (.fail error) current currentPlatform handle after finalPlatform laterLog later
      | div => cases pure_success .div current currentPlatform handle after finalPlatform laterLog later
      | ok checked =>
        rcases checked with ⟨events, answer⟩
        cases answer <;> try {
          cases pure_success (.ok none) current currentPlatform handle after finalPlatform laterLog later }
        case Accepted authenticated =>
          obtain ⟨root⟩ := afterAuthentication setup checks reserve representation created packet authenticated
            current after currentPlatform finalPlatform handle laterLog later
          obtain ⟨extended⟩ := Cut.extend setup checks representation created packet authenticated handle after finalPlatform checkLog laterLog [] root
          simp only [List.append_nil] at extended
          rw [full]
          exact ⟨pin, rfl, ⟨⟨authenticated, events, current, currentPlatform, checkLog, verified, extended⟩⟩⟩

/-- Complete actual corrected acceptance retains its original repeated pin, mandatory authentication, reservation, Root and token-retention blocks in one lower capability log. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (supported : (((.ok (some handle), after), finalPlatform), log) ∈ support
      (run (RegistrationNativePlatformKemCountedAccept.accept setup codec checks reserve route representation created packet)
        before previous).withQueryLog) :
    ∃ pin current currentPlatform pinLog laterLog,
      ((((.ok (.Some pin), current), currentPlatform), pinLog) ∈ support
        (run (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins)) before previous).withQueryLog) ∧
      log = pinLog ++ laterLog ∧
      Nonempty (CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log) := by
  unfold RegistrationNativePlatformKemCountedAccept.accept at supported
  obtain ⟨⟨⟨pinResult, current⟩, currentPlatform⟩, pinLog, laterLog, pinned, later, full⟩ :=
    bind_cut (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins))
      _ before previous _ log supported
  obtain ⟨pin, pinEq, ⟨checked⟩⟩ := afterPin setup codec checks reserve route representation created packet pinResult
    current after currentPlatform finalPlatform handle laterLog later
  obtain ⟨extended⟩ := CheckedCut.extend setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform pinLog laterLog [] checked
  simp only [List.append_nil] at extended
  rw [← full] at extended
  exact ⟨pin, current, currentPlatform, pinLog, laterLog, by simpa only [pinEq] using pinned, full, ⟨extended⟩⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut.accept
