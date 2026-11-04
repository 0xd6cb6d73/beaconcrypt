-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptRecipientCut
import BeaconcryptCore.Computational.RegistrationNativeKemTracedServerSource

/-! Evaluated actual accept controllers carry native collector receipts through their actual private-pool, authentication, reservation and retention cuts. Each Root operand is tied to the same lower encapsulation reply rather than a separately chosen support sample. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeKemServerState (State)
open RegistrationNativeKemCountedServerTrace (Log)
open RegistrationNativePlatformKemCountedAccept
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Platform Value Next Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
local notation "CP" => RegistrationNativeKemCountedProgram.Spec KemSK
local notation "Client" => State n source
local notation "M" => RegistrationNativePlatformKemCountedProgram.M KemSK Platform

private def flat (work : StateT Client M Value) (before : Client) (previous : Platform) := (work.run before).run previous
private noncomputable def eval (setup : Setup base KemSK) (work : StateT Client M Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :=
  RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (flat work before previous).withQueryLog pool

private theorem evaluate_bind {A B : Type} (setup : Setup base KemSK)
    (work : OracleComp CP A) (next : A → OracleComp CP B) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (work >>= next) pool = (do
      let result ← RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool
      RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (next result.1) result.2) := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_bind, StateT.run_bind]

private theorem evaluate_map {A B : Type} (setup : Setup base KemSK) (function : A → B) (work : OracleComp CP A) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem (function <$> work) pool =
      Prod.map function id <$> RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem work pool := by
  simp only [RegistrationNativeKemCountedProgram.evaluate, simulateQ_map, StateT.run_map]
  rfl

private theorem bind_cut (setup : Setup base KemSK) (work : StateT Client M Value) (next : Value → StateT Client M Next)
    (before : Client) (previous : Platform) (result : (Next × Client) × Platform) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((result, log), afterPool) ∈ support (eval setup (work >>= next) before previous beforePool)) :
    ∃ (first : (Value × Client) × Platform) (prefixLog suffixLog : Log KemSK) (middlePool : Pool KemSK),
      ((first, prefixLog), middlePool) ∈ support (eval setup work before previous beforePool) ∧
      ((result, suffixLog), afterPool) ∈ support (eval setup (next first.1.1) first.1.2 first.2 middlePool) ∧
      log = prefixLog ++ suffixLog := by
  simp only [eval, flat, StateT.run_bind, withQueryLog_bind, evaluate_bind, evaluate_map,
    mem_support_bind_iff, support_map] at supported
  obtain ⟨⟨⟨first, prefixLog⟩, middlePool⟩, head, ⟨⟨last, suffixLog⟩, finalPool⟩, tail, returned⟩ := supported
  simp only [Prod.map, id_eq, Prod.mk.injEq] at returned
  rcases returned with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨first, prefixLog, suffixLog, middlePool, head, tail, rfl⟩

private theorem pure_success (setup : Setup base KemSK) (value : RustM (Option Nat)) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (pure value) before previous beforePool)) : value = .ok (some handle) := by
  simp only [eval, flat, StateT.run_pure, withQueryLog_pure, RegistrationNativeKemCountedProgram.evaluate,
    simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact supported.1.1.1.1.symm

private theorem inject_run (work : StateT Client (OracleComp CP) Value) (before : Client) (previous : Platform) :
    flat (RegistrationNativePlatformKemCountedProgram.inject work) before previous =
      (fun result => (result, previous)) <$> work.run before := by
  change (work.run before >>= fun result => pure (result, previous)) = _
  exact bind_pure_comp _ _

/-- The actual one-use retention and the genuine native Root collector from the same evaluated accept block. -/
structure Cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat)
    (after : Client) (finalPlatform : Platform) (log : Log KemSK) where
  beforeAgreement : Client
  afterAgreement : Client
  atPlatform : Platform
  accepted : agreement.ServerAgreement
  agreementLog : Log KemSK
  retainLog : Log KemSK
  beforePool : Pool KemSK
  afterAgreementPool : Pool KemSK
  afterPool : Pool KemSK
  agreed : (((.ok (.ServerComplete accepted), afterAgreement), agreementLog), afterAgreementPool) ∈ support
    (RegistrationNativeKemCountedProgram.evaluate setup.baseImpl setup.kem
      ((RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated).run beforeAgreement).withQueryLog beforePool)
  retained : ((((.ok (some handle), after), finalPlatform), retainLog), afterPool) ∈ support
    (eval setup (ordinaryServer (RegistrationNativePlatformServerSdk.liftNative RegistrationNativePlatformMldsaProgram.coins
      (RegistrationServerNativeSource.retain created accepted))) afterAgreement atPlatform afterAgreementPool)
  root : RegistrationNativeKemTracedServerSource.Receipt setup checks representation created packet authenticated beforeAgreement afterAgreement accepted log

/-- Actual successful replay/reservation/agreement/retention supplies a genuine native collector receipt and its actual same-log encapsulation reply. -/
theorem afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before after : Client) (previous finalPlatform : Platform)
    (handle : Nat) (log : Log KemSK) (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.afterAuthentication setup checks reserve representation created packet authenticated)
        before previous beforePool)) :
    Nonempty (Cut setup checks representation created packet authenticated handle after finalPlatform log) := by
  change ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
    (eval setup (if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
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
        else pure (.ok none)) before previous beforePool) at supported
  split at supported
  · cases pure_success setup (.ok none) before previous handle after finalPlatform log beforePool afterPool supported
  · obtain ⟨⟨⟨allowed, reserved⟩, reservedPlatform⟩, prefixLog, laterLog, reservedPool, _reserved, later, full⟩ :=
      bind_cut setup (ordinaryServer reserve) _ before previous _ log beforePool afterPool supported
    cases allowed with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at later
      cases pure_success setup (.ok none) reserved reservedPlatform handle after finalPlatform laterLog reservedPool afterPool later
    | true =>
      simp only [ite_true] at later
      obtain ⟨⟨⟨effect, agreed⟩, agreedPlatform⟩, agreementLog, retainLog, agreementPool, actualAgree, retained, splitLog⟩ :=
        bind_cut setup (RegistrationNativePlatformKemCountedProgram.inject
          (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated))
          _ reserved reservedPlatform _ laterLog reservedPool afterPool later
      simp only [eval] at actualAgree
      rw [inject_run, RegistrationAgreementMacroTrace.logging_map, evaluate_map, support_map] at actualAgree
      obtain ⟨⟨⟨⟨actualEffect, actualAgreed⟩, actualLog⟩, actualPool⟩, ran, same⟩ := actualAgree
      simp only [Prod.map, id_eq, Prod.mk.injEq] at same
      rcases same with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      cases actualEffect with
      | fail error => cases pure_success setup (.fail error) actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained
      | div => cases pure_success setup .div actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained
      | ok answer =>
        cases answer <;> try {
          cases pure_success setup (.ok none) actualAgreed reservedPlatform handle after finalPlatform retainLog actualPool afterPool retained }
        case ServerComplete accepted =>
          obtain ⟨root⟩ := RegistrationNativeKemTracedServerSource.agree setup checks representation created packet authenticated accepted
            reserved actualAgreed reservedPool actualPool actualLog ran
          have sameLog : log = prefixLog ++ actualLog ++ retainLog := by rw [full, splitLog, List.append_assoc]
          rw [sameLog]
          exact ⟨⟨reserved, actualAgreed, reservedPlatform, accepted, actualLog, retainLog, reservedPool, actualPool, afterPool,
            ran, retained, { root with encapsulated := List.mem_append_left _ (List.mem_append_right _ root.encapsulated) }⟩⟩

private theorem Cut.extend (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (handle : Nat) (after : Client) (finalPlatform : Platform)
    (prefixLog log suffixLog : Log KemSK)
    (receipt : Cut setup checks representation created packet authenticated handle after finalPlatform log) :
    Nonempty (Cut setup checks representation created packet authenticated handle after finalPlatform (prefixLog ++ log ++ suffixLog)) := by
  exact ⟨{ receipt with root := { receipt.root with encapsulated := (List.mem_append_left _ (List.mem_append_right _ receipt.root.encapsulated)) } }⟩

attribute [local irreducible] RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformServerSdk.liftNative

/-- The actual mandatory authentication prefix and the retained token's actual Root cut share this same callback log. -/
structure CheckedCut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (pin : session.ServerAuthenticationPin) (before : Client) (previous : Platform)
    (handle : Nat) (after : Client) (finalPlatform : Platform) (log : Log KemSK) where
  authenticated : registration.AuthenticatedInit
  events : List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event
  afterCheck : Client
  checkPlatform : Platform
  checkLog : Log KemSK
  beforePool : Pool KemSK
  checkPool : Pool KemSK
  checked : ((((.ok (events, .Accepted authenticated), afterCheck), checkPlatform), checkLog), checkPool) ∈ support
    (eval setup (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route source.verify pin packet))
      before previous beforePool)
  root : Cut setup checks representation created packet authenticated handle after finalPlatform log

private theorem CheckedCut.extend (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
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
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (pinResult : RustM (core.option.Option session.ServerAuthenticationPin))
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.afterPin setup codec checks reserve route representation created packet pinResult)
        before previous beforePool)) :
    ∃ pin, pinResult = .ok (.Some pin) ∧
      Nonempty (CheckedCut setup codec checks route representation created packet pin before previous handle after finalPlatform log) := by
  unfold RegistrationNativePlatformKemCountedAccept.afterPin at supported
  cases pinResult with
  | fail error => cases pure_success setup (.fail error) before previous handle after finalPlatform log beforePool afterPool supported
  | div => cases pure_success setup .div before previous handle after finalPlatform log beforePool afterPool supported
  | ok option =>
    cases option with
    | none => cases pure_success setup (.ok none) before previous handle after finalPlatform log beforePool afterPool supported
    | some pin =>
      obtain ⟨⟨⟨checked, current⟩, currentPlatform⟩, checkLog, laterLog, currentPool, verified, later, full⟩ :=
        bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins
          setup codec route source.verify pin packet)) _ before previous _ log beforePool afterPool supported
      cases checked with
      | fail error => cases pure_success setup (.fail error) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | div => cases pure_success setup .div current currentPlatform handle after finalPlatform laterLog currentPool afterPool later
      | ok checked =>
        rcases checked with ⟨events, answer⟩
        cases answer <;> try {
          cases pure_success setup (.ok none) current currentPlatform handle after finalPlatform laterLog currentPool afterPool later }
        case Accepted authenticated =>
          obtain ⟨root⟩ := afterAuthentication setup checks reserve representation created packet authenticated
            current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
          obtain ⟨extended⟩ := Cut.extend setup checks representation created packet authenticated handle after finalPlatform checkLog laterLog [] root
          simp only [List.append_nil] at extended
          rw [full]
          exact ⟨pin, rfl, ⟨⟨authenticated, events, current, currentPlatform, checkLog, beforePool, currentPool, verified, extended⟩⟩⟩

/-- Complete actual corrected acceptance retains its original repeated pin, mandatory authentication, reservation, Root and token-retention blocks in one lower capability log. -/
theorem accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before after : Client) (previous finalPlatform : Platform) (handle : Nat) (log : Log KemSK)
    (beforePool afterPool : Pool KemSK)
    (supported : ((((.ok (some handle), after), finalPlatform), log), afterPool) ∈ support
      (eval setup (RegistrationNativePlatformKemCountedAccept.accept setup codec checks reserve route representation created packet)
        before previous beforePool)) :
    ∃ pin current currentPlatform pinLog laterLog currentPool,
      (((((.ok (.Some pin), current), currentPlatform), pinLog), currentPool) ∈ support
        (eval setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins)) before previous beforePool)) ∧
      log = pinLog ++ laterLog ∧
      Nonempty (CheckedCut setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform log) := by
  unfold RegistrationNativePlatformKemCountedAccept.accept at supported
  obtain ⟨⟨⟨pinResult, current⟩, currentPlatform⟩, pinLog, laterLog, currentPool, pinned, later, full⟩ :=
    bind_cut setup (ordinaryServer (RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformMldsaProgram.coins))
      _ before previous _ log beforePool afterPool supported
  obtain ⟨pin, pinEq, ⟨checked⟩⟩ := afterPin setup codec checks reserve route representation created packet pinResult
    current after currentPlatform finalPlatform handle laterLog currentPool afterPool later
  obtain ⟨extended⟩ := CheckedCut.extend setup codec checks route representation created packet pin current currentPlatform handle after finalPlatform pinLog laterLog [] checked
  simp only [List.append_nil] at extended
  rw [← full] at extended
  exact ⟨pin, current, currentPlatform, pinLog, laterLog, currentPool, by simpa only [pinEq] using pinned, full, ⟨extended⟩⟩


end BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.afterAuthentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.afterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.afterPin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.afterPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualRoot.accept
