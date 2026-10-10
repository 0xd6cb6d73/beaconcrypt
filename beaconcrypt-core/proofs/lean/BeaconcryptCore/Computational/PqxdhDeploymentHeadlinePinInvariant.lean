-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinEnv
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinControl

/-!
# The two env_g ideal-world invariants of the pin lift (CE-12 P4 step 2, AG lift R1)

The two facts of the ideal environment that the P2b remainder names for the b2s Server-pin row of design-v2 section 7.6 (R1), on every outcome of every CTX world (in particular `idealAuth`) with the ideal environment of a target (`PqxdhDeploymentIdealEnv.envGD`), as `PinFacts`:

- (a) every established owner's installed shell has associated data `RawCtxServerRouting.associatedArray pin beacon`, where `pin` is the pin with which the public transcript summary (`PqxdhDeploymentTranscript.summarize`) created that owner and `beacon` is some Beacon identity;
- (b) when the record control holds a Server, every successful build entry of the final transcript is the Phase 2 writer output of fields carrying that Server's identity (`PqxdhDeploymentEligibility.BuildShaped`); with `Phase2ReadBack`, the Server identity field read from a build response is then the record control's Server identity.

Proof: the joint invariant `Inv` of the flattened world (ledger, environment state, record control): the environment's Server identity, the environment's pins equal to the summary's created pins, `ControlOk` with `PinOk` (the associated data the transcript admits), and every build entry shaped. It holds after the startup, whose effects are coins, and the Server installation (`startup_facts`, `install_facts`, `PqxdhDeploymentHeadlinePinEnv.envGD_start`), and every adversary query keeps it (`full_inv`): quiet native commands (`forward_quiet`), environment commands (`forward_env`, from `PqxdhDeploymentHeadlinePinEnv.envGD_move`, `PqxdhDeploymentHeadlinePinEnv.envGD_ok` and `PqxdhDeploymentHeadlinePinControl.nativeImpl_env`, with `fits_of_ok`) and secrecy commands, whose native commands are coins and sends (`secrecy_quiet`, `secrecy_inv`). `ctxRun_pinFacts` (every key modes and plaintext replacement), `idealAuth_pinFacts`.

No assumption or codec law; support facts only. No `PqxdhBoundary*` module is imported.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry Spec FullSpec Command FreshBounds Mode ModeSpec)
open PqxdhDeploymentTranscript (summarize)
open PqxdhRecordLiftInterface (Environment EnvEffects IsEnvironment)
open PqxdhRecordLiftIdeal (ctxRun idealAuth)
open PqxdhRecordLiftFlat (NativeState nativeImpl fullImpl)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentHeadlinePinEnv (pins serverId InstallOk badInstall PinMove)
open PqxdhDeploymentHeadlinePinControl (ServerIs ShellsOk ControlOk InstallFits Quiet)

variable {KemSK : Type}

/-! ### The public pins of a transcript -/

/-- The associated data of an owner index admitted by a transcript: the extracted builder's output on the pin the transcript's summary records for that owner and some Beacon identity. -/
def PinOk (transcript : List Entry) (owner : ℕ) (associatedData : Std.Array Std.U8 153#usize) : Prop :=
  ∃ pin keyId beacon, (summarize transcript).owners[owner]? = some (pin, keyId) ∧
    associatedData = RawCtxServerRouting.associatedArray pin beacon

/-- A transcript entry only extends the summary's owners. -/
theorem summarize_owners_extend (transcript : List Entry) (entry : Entry) :
    ∃ extra, (summarize (transcript ++ [entry])).owners = (summarize transcript).owners ++ extra := by
  rw [PqxdhDeploymentTranscript.summarize_append]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · exact ⟨[], by simp [PqxdhDeploymentTranscript.step]⟩
  · cases command with
    | create pin keyId =>
        cases reply with
        | none => exact ⟨[], by simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand]⟩
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin pin with
            | none => exact ⟨[], by simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, parsed]⟩
            | some word =>
                exact ⟨[(word, keyId)], by
                  simp [PqxdhDeploymentTranscript.step, PqxdhDeploymentTranscript.stepCommand, parsed]⟩
    | _ =>
        exact ⟨[], by
          simp only [PqxdhDeploymentTranscript.step, List.append_nil]
          exact PqxdhDeploymentHeadlinePinEnv.stepCommand_owners _ _ _ (fun _ _ wrong => by cases wrong)⟩
  · exact ⟨[], by simp [PqxdhDeploymentTranscript.step]⟩

/-- A later transcript admits every associated data an earlier one admits. -/
theorem pinOk_extend (transcript : List Entry) (entry : Entry) (owner : ℕ)
    (associatedData : Std.Array Std.U8 153#usize) (ok : PinOk transcript owner associatedData) :
    PinOk (transcript ++ [entry]) owner associatedData := by
  obtain ⟨pin, keyId, beacon, found, built⟩ := ok
  obtain ⟨extra, extended⟩ := summarize_owners_extend transcript entry
  refine ⟨pin, keyId, beacon, ?_, built⟩
  rw [extended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- The established shells admitted by a transcript are admitted by every later transcript. -/
theorem shellsOk_extend {n : ℕ} (transcript : List Entry) (entry : Entry) (control : PqxdhRecordLiftProtocol.Control n)
    (holds : ShellsOk (PinOk transcript) control) : ShellsOk (PinOk (transcript ++ [entry])) control :=
  fun owner shell kernel found => pinOk_extend transcript entry owner _ (holds owner shell kernel found)

/-- An admissible request of an environment state whose pins agree with the transcript fits the transcript's admitted associated data. -/
theorem fits_of_ok {Bk : Type} {n : ℕ} (transcript : List Entry) (e : EnvState KemSK Bk)
    (agree : (summarize transcript).owners.map Prod.fst = pins e) (query : (EnvEffects n).Domain)
    (good : badInstall e query = false) : InstallFits (PinOk transcript) query := by
  rcases query with coin | capability
  · trivial
  · cases capability with
    | installBeacon owner shell ref =>
        have ok : InstallOk e (n := n) (.inr (.installBeacon owner shell ref)) := by
          by_contra bad
          have flagged := (PqxdhDeploymentHeadlinePinEnv.badInstall_iff e _).2 bad
          rw [good] at flagged
          cases flagged
        obtain ⟨before, found, beacon, built⟩ := ok
        have mapped : ((summarize transcript).owners.map Prod.fst)[owner]? = some before.beacon.serverIdentity := by
          rw [agree]
          unfold pins
          rw [List.getElem?_map, found]
          rfl
        rw [List.getElem?_map] at mapped
        obtain ⟨⟨pin, keyId⟩, entryFound, pinEq⟩ := Option.map_eq_some_iff.mp mapped
        exact ⟨pin, keyId, beacon, entryFound, by rw [built]; simp only at pinEq; rw [pinEq]⟩
    | _ => trivial


/-! ### The secrecy commands issue only coins and sends -/

/-- A native command that is an environment command. -/
def envQuery : Spec.Domain → Bool
  | .inr (.create _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) | .inr (.finish _ _)
  | .inr (.hmac _ _) => true
  | _ => false

/-- A native command that is not an environment command is quiet. -/
theorem quiet_of_envQuery (query : Spec.Domain) (notEnv : envQuery query = false) : Quiet query := by
  rcases query with coin | command
  · trivial
  · cases command <;> simp_all [envQuery, Quiet, IsEnvironment]

/-- A uniform message is drawn with coins only. -/
theorem uniformBytes_quiet (length : ℕ) :
    (PqxdhDeploymentSecrecy.uniformBytes length).IsQueryBoundP (fun query => envQuery query = true) 0 := by
  induction length with
  | zero => trivial
  | succ length ih =>
      unfold PqxdhDeploymentSecrecy.uniformBytes PqxdhDeploymentSecrecy.coin
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [envQuery]), fun _ => ?_⟩
      simp only [envQuery, Bool.false_eq_true, ↓reduceIte]
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind ih fun _ _ => trivial

/-- A send is one record command. -/
theorem send_quiet (handle : PqxdhDeploymentInterface.Handle) (message : Pqxdh.Bytes) :
    (PqxdhDeploymentSecrecy.send handle message).IsQueryBoundP (fun query => envQuery query = true) 0 := by
  cases handle <;>
    exact (isQueryBoundP_query_iff _ _ _).2 (by simp [envQuery])

/-- The test bit is one coin. -/
theorem drawBit_quiet : PqxdhDeploymentSecrecy.drawBit.IsQueryBoundP (fun query => envQuery query = true) 0 := by
  unfold PqxdhDeploymentSecrecy.drawBit PqxdhDeploymentSecrecy.coin
  rw [isQueryBoundP_map_iff]
  exact (isQueryBoundP_query_iff _ _ _).2 (by simp [envQuery])

/-- A secrecy command of the ledger issues only coins and sends. -/
theorem secrecy_quiet (crypto : Pqxdh.Crypto) {Reader Response : Type} (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (ledger : PqxdhDeploymentSecrecy.Ledger) :
    ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run ledger).IsQueryBoundP
      (fun query => envQuery query = true) 0 := by
  rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
    split
    · split
      · rw [show (0 : ℕ) = 0 + 0 from rfl]
        refine isQueryBoundP_bind drawBit_quiet fun _ _ => ?_
        rw [show (0 : ℕ) = 0 + 0 from rfl]
        exact isQueryBoundP_bind (send_quiet _ _) fun _ _ => trivial
      · split
        · rw [show (0 : ℕ) = 0 + 0 from rfl]
          exact isQueryBoundP_bind (send_quiet _ _) fun _ _ => trivial
        · trivial
    · trivial
  · simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
    split
    · rw [show (0 : ℕ) = 0 + 0 from rfl]
      refine isQueryBoundP_bind (uniformBytes_quiet length) fun _ _ => ?_
      rw [show (0 : ℕ) = 0 + 0 from rfl]
      exact isQueryBoundP_bind (send_quiet _ _) fun _ _ => trivial
    · trivial


/-! ### The joint invariant -/

section Invariant
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhRecordLiftWorldCompiler (Label)

/-- The environment state type of the ideal environment of a target. -/
abbrev GD (KemSK : Type) (count : ℕ) :=
  EnvState KemSK (PqxdhDeploymentIdealParams.Params KemSK count × SplitBk)

/-- The joint invariant of the flattened CTX world with the ideal environment of a target, for a Server identity: the environment's Server has that identity; the environment's pins are the transcript summary's created pins; the record control holds a Server with that identity and every established owner's shell has associated data admitted by the transcript; and every successful build entry of the transcript is the Phase 2 writer output of fields with that identity. -/
def Inv (identity : RawCtxServerRouting.Identity)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState 2 (GD KemSK count)) : Prop :=
  serverId state.2.1.1 = identity ∧ (summarize state.1.transcript).owners.map Prod.fst = pins state.2.1.1 ∧
    ControlOk identity (PinOk state.1.transcript) state.2.1.2 ∧
    ∀ entry ∈ state.1.transcript, PqxdhDeploymentEligibility.BuildShaped codec identity entry

/-- An entry that is not a command keeps the summary. -/
theorem summarize_quiet (transcript : List Entry) (entry : Entry)
    (notCommand : ∀ command reply, entry ≠ ⟨.inl (.inr command), reply⟩) :
    summarize (transcript ++ [entry]) = summarize transcript := by
  rw [PqxdhDeploymentTranscript.summarize_append]
  rcases entry with ⟨(coin | command) | secrecy, reply⟩
  · rfl
  · exact absurd rfl (notCommand command reply)
  · rfl

/-- Appending an entry that keeps the summary's owners and is shaped keeps the invariant at an unchanged environment state with a control that keeps both facts. -/
theorem inv_append (identity : RawCtxServerRouting.Identity) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (native native' : NativeState 2 (GD KemSK count)) (entry : Entry)
    (holds : Inv codec identity (ledger, native))
    (identityEq : serverId native'.1.1 = identity)
    (agree : (summarize (ledger.transcript ++ [entry])).owners.map Prod.fst = pins native'.1.1)
    (control : ControlOk identity (PinOk ledger.transcript) native'.1.2)
    (shaped : PqxdhDeploymentEligibility.BuildShaped codec identity entry) (ledger' : PqxdhDeploymentSecrecy.Ledger)
    (transcript : ledger'.transcript = ledger.transcript ++ [entry]) : Inv codec identity (ledger', native') := by
  refine ⟨identityEq, by rw [transcript]; exact agree, ⟨control.1, ?_⟩, fun other member => ?_⟩
  · rw [transcript]
    exact shellsOk_extend ledger.transcript entry native'.1.2 control.2
  · rw [transcript, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact holds.2.2.2 other old
    · exact shaped

/-- A quiet native command keeps the invariant with its entry recorded. -/
theorem forward_quiet (modes : Label 2 → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment 2 (GD KemSK count))
    (identity : RawCtxServerRouting.Identity) (query : Spec.Domain) (quiet : envQuery query = false)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (native : NativeState 2 (GD KemSK count))
    (holds : Inv codec identity (ledger, native)) :
    ∀ inner ∈ support ((nativeImpl modes replace setup codec route env query).run native),
      Inv codec identity (ledger.record (.inl query) inner.1, inner.2) := by
  intro inner member
  obtain ⟨same, control⟩ := PqxdhDeploymentHeadlinePinControl.nativeImpl_quiet identity (PinOk ledger.transcript)
    modes replace setup codec route env query (quiet_of_envQuery query quiet) native holds.2.2.1 inner member
  have summary : summarize (ledger.transcript ++ [⟨.inl query, inner.1⟩]) = summarize ledger.transcript := by
    rcases query with coin | command
    · exact summarize_quiet _ _ (fun _ _ wrong => by cases wrong)
    · rw [PqxdhDeploymentTranscript.summarize_append]
      exact PqxdhDeploymentTranscript.step_other _ _ (fun _ _ _ wrong => by cases wrong; simp [envQuery] at quiet)
        (fun _ _ wrong => by cases wrong; simp [envQuery] at quiet)
        (fun _ _ _ wrong => by cases wrong; simp [envQuery] at quiet)
  refine inv_append codec identity ledger native inner.2 _ holds (by rw [same]; exact holds.1)
    (by rw [summary, same]; exact holds.2.1) control ?_ _ rfl
  rcases query with coin | command
  · trivial
  · cases command <;> trivial

/-- An environment command of the ideal environment of a target keeps the invariant with its entry recorded. -/
theorem forward_env {A : Type} (modes : Label 2 → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (t : PqxdhDeploymentIdealParams.Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (identity : RawCtxServerRouting.Identity)
    (command : Command) (allowed : IsEnvironment command) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (native : NativeState 2 (GD KemSK count)) (holds : Inv codec identity (ledger, native)) :
    ∀ inner ∈ support ((nativeImpl modes replace setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) (.inr command)).run native),
      Inv codec identity (ledger.record (.inl (.inr command)) inner.1, inner.2) := by
  intro inner member
  obtain ⟨stepped, control⟩ := PqxdhDeploymentHeadlinePinControl.nativeImpl_env identity (PinOk ledger.transcript)
    modes replace setup codec route _ command allowed native inner member
  have moved := PqxdhDeploymentHeadlinePinEnv.envGD_move setup codec checks t ensureInit identityIndex runtime
    ⟨command, allowed⟩ native.1.1 _ stepped
  have controlOk := control (badInstall native.1.1)
    (fun query good => fits_of_ok ledger.transcript native.1.1 holds.2.1 query good)
    (PqxdhDeploymentHeadlinePinEnv.envGD_ok setup codec checks t ensureInit identityIndex runtime ⟨command, allowed⟩
      native.1.1) holds.2.2.1
  refine inv_append codec identity ledger native inner.2 _ holds (moved.1.trans holds.1) ?_ controlOk ?_ _ rfl
  · rw [PqxdhDeploymentTranscript.summarize_append]
    exact moved.2.1 _ holds.2.1
  · have shaped := moved.2.2
    rw [holds.1] at shaped
    exact shaped

/-- A secrecy command keeps the invariant: its native commands are coins and sends, and its entry neither changes the summary nor is a build. -/
theorem secrecy_inv (modes : Label 2 → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment 2 (GD KemSK count)) (serverKid : Std.U64)
    (bounds : FreshBounds) (identity : RawCtxServerRouting.Identity) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (native : NativeState 2 (GD KemSK count))
    (holds : Inv codec identity (ledger, native)) :
    ∀ result ∈ support ((fullImpl modes replace setup codec route env serverKid bounds (.inr secrecy)).run
      (ledger, native)), Inv codec identity result.2 := by
  intro result member
  rw [PqxdhRecordLiftFlat.fullImpl_run, support_map] at member
  obtain ⟨z, zMember, rfl⟩ := member
  obtain ⟨reply, transcript⟩ := PqxdhRecordLiftFlat.ledger_append setup.source.crypto codec serverKid bounds
    (.inr secrecy) ledger z.1 (PqxdhDeploymentHeadlinePinControl.run_value _ _ _ z zMember)
  have kept := PqxdhDeploymentHeadlinePinControl.keep_bounded (nativeImpl modes replace setup codec route env) envQuery
    (fun state => state.1.1 = native.1.1 ∧ ControlOk identity (PinOk ledger.transcript) state.1.2)
    (fun query state good held next nextMember => by
      obtain ⟨same, control⟩ := PqxdhDeploymentHeadlinePinControl.nativeImpl_quiet identity (PinOk ledger.transcript)
        modes replace setup codec route env query (quiet_of_envQuery query good) state held.2 next nextMember
      exact ⟨same.trans held.1, control⟩) _ (secrecy_quiet setup.source.crypto codec serverKid bounds secrecy ledger)
    native ⟨rfl, holds.2.2.1⟩ z zMember
  refine inv_append codec identity ledger native z.2 _ holds (by rw [kept.1]; exact holds.1)
    (by rw [summarize_quiet _ _ (fun _ _ wrong => by cases wrong), kept.1]; exact holds.2.1) kept.2
    (show PqxdhDeploymentEligibility.BuildShaped codec identity ⟨.inr secrecy, reply⟩ from trivial) _ transcript

/-- Every adversary query of the CTX world with the ideal environment of a target keeps the invariant. -/
theorem full_inv {A : Type} (modes : Label 2 → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (t : PqxdhDeploymentIdealParams.Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : FreshBounds) (identity : RawCtxServerRouting.Identity) (query : FullSpec.Domain)
    (state : PqxdhDeploymentSecrecy.Ledger × NativeState 2 (GD KemSK count)) (holds : Inv codec identity state) :
    ∀ result ∈ support ((fullImpl modes replace setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds query).run
        state), Inv codec identity result.2 := by
  obtain ⟨ledger, native⟩ := state
  rcases query with forwarded | secrecy
  · intro result member
    rw [PqxdhRecordLiftFlat.fullImpl_run, PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map, support_map] at member
    obtain ⟨_, ⟨inner, reached, rfl⟩, rfl⟩ := member
    rcases forwarded with coin | command
    · exact forward_quiet setup codec modes replace route _ identity (.inl coin) rfl ledger native holds inner reached
    · cases command with
      | create pin keyId =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.create pin keyId) trivial
            ledger native holds inner reached
      | bundle owner =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.bundle owner) trivial
            ledger native holds inner reached
      | accept raw =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.accept raw) trivial
            ledger native holds inner reached
      | build session payload =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.build session payload) trivial
            ledger native holds inner reached
      | finish owner raw =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.finish owner raw) trivial
            ledger native holds inner reached
      | hmac key message =>
          exact forward_env setup codec checks modes replace route t ensureInit identityIndex runtime identity (.hmac key message) trivial
            ledger native holds inner reached
      | hash bytes =>
          exact forward_quiet setup codec modes replace route _ identity (.inr (.hash bytes)) rfl ledger native holds inner reached
      | serverSend keyId plaintext =>
          exact forward_quiet setup codec modes replace route _ identity (.inr (.serverSend keyId plaintext)) rfl ledger native holds inner reached
      | serverRaw raw =>
          exact forward_quiet setup codec modes replace route _ identity (.inr (.serverRaw raw)) rfl ledger native holds inner reached
      | beaconSend owner plaintext =>
          exact forward_quiet setup codec modes replace route _ identity (.inr (.beaconSend owner plaintext)) rfl ledger native holds inner reached
      | beaconRaw owner raw =>
          exact forward_quiet setup codec modes replace route _ identity (.inr (.beaconRaw owner raw)) rfl ledger native holds inner reached
  · exact secrecy_inv setup codec modes replace route _ serverKid bounds identity secrecy ledger native holds

end Invariant


/-! ### The ideal-world facts -/

section Facts
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}
open PqxdhRecordLiftWorldCompiler (Label Phase)

/-- The two ideal-world facts of the pin lift on a CTX-world outcome: (b) when the record control holds a Server, every successful build entry of the final transcript is the Phase 2 writer output of fields carrying that Server's identity; (a) every established owner's installed shell has the extracted associated data of the pin with which the transcript created that owner and some Beacon identity. -/
def PinFacts {n : ℕ} {E X : Type} (result : PqxdhRecordLiftIdeal.Client n E X × PqxdhRecordLiftIdeal.CtxPrivate n) :
    Prop :=
  ∀ value ∈ result.1.1,
    (∀ server, result.1.2.server = some server → ∀ entry ∈ value.2.1.2.transcript,
      PqxdhDeploymentEligibility.BuildShaped codec server.identity entry) ∧
    (∀ (owner : ℕ) shell kernel, result.1.2.owners[owner]? = some (Phase.established shell kernel) →
      ∃ pin keyId beacon, (summarize value.2.1.2.transcript).owners[owner]? = some (pin, keyId) ∧
        shell.associatedData = RawCtxServerRouting.associatedArray pin beacon)

/-- An environment coin of the compiled client keeps the record control. -/
theorem effects_coin_control {n : ℕ} (coin : unifSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    ∀ result ∈ support ((PqxdhRecordLiftProtocol.effects (n := n) (.inl coin)).run control), result.2 = control := by
  intro result supported
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨charged, member, continued⟩ := supported
  have same := PqxdhRecordLiftProtocolHistory.lift_control (.charge (PqxdhRecordLiftInterface.effectKind
    (n := n) (.inl coin))) control charged member
  rw [same] at continued
  exact PqxdhRecordLiftProtocolHistory.lift_control (.coin coin) control result continued

/-- The startup of a CTX world (the environment's start, whose effects are coins) keeps the initial record control, and its environment outcome is a startup outcome of the environment. -/
theorem startup_facts {n : ℕ} {E : Type} (modes : Label n → PqxdhRecordLiftIdeal.KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) :
    ∀ born ∈ support (PqxdhRecordLiftFlat.startup modes replace setup codec route env),
      born.1.1 ∈ support env.start ∧ born.1.2 = PqxdhRecordLiftProtocol.initialControl := by
  intro born member
  have client := PqxdhDeploymentHeadlinePinControl.run_value _ _ _ born member
  rw [← QueryImpl.simulateQ_compose] at client
  refine ⟨PqxdhDeploymentHeadlinePinControl.run_value _ _ _ _ client, ?_⟩
  exact PqxdhRecordLiftFlat.support_keep_oracle _ (fun control => control = PqxdhRecordLiftProtocol.initialControl)
    (fun coin control held next nextMember => by
      rw [← held]
      exact effects_coin_control coin control next nextMember) _ _ rfl born.1 client

/-- The installation of the constructed Server from the initial record control holds that Server's identity and no owner. -/
theorem install_facts {n : ℕ} (modes : Label n → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (created : PqxdhLiveServerConstruction.Created Unit)
    (secret : PqxdhRecordLiftIdeal.CtxPrivate n) :
    ∀ installed ∈ support (PqxdhRecordLiftFlat.install modes replace setup codec route created
      PqxdhRecordLiftProtocol.initialControl secret),
      ServerIs created.server.server.identity installed.1.2 ∧ installed.1.2.owners = [] := by
  intro installed member
  have client := PqxdhDeploymentHeadlinePinControl.run_value _ _ _ installed member
  change installed.1 ∈ support (PqxdhRecordLiftProtocol.initializeServer created
    PqxdhRecordLiftProtocol.initialControl) at client
  simp only [PqxdhRecordLiftProtocol.initializeServer, PqxdhRecordLiftProtocol.initialControl,
    PqxdhRecordLiftProtocol.control, PqxdhRecordLiftWorldCompiler.initial, support_pure,
    Set.mem_singleton_iff] at client
  rw [client]
  exact ⟨⟨_, rfl, rfl⟩, rfl⟩

/-- **The two env_g ideal-world invariants.** On every outcome of every CTX world (in particular `idealAuth`) with the ideal environment of a target, the record control and the final transcript satisfy `PinFacts`. -/
theorem ctxRun_pinFacts {A X : Type} (modes : Label 2 → PqxdhRecordLiftIdeal.KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (route : RawCtxServerRouting.SenderDecoder) (t : PqxdhDeploymentIdealParams.Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (ctxRun modes replace setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) serverKid bounds mode
        adversary), PinFacts codec result := by
  intro result member
  rw [PqxdhRecordLiftFlat.ctxRun_flat, mem_support_bind_iff] at member
  obtain ⟨born, bornMember, member⟩ := member
  obtain ⟨started, bornControl⟩ := startup_facts setup codec modes replace route _ born bornMember
  rcases bornEq : born.1.1 with _ | ⟨created, initial⟩
  · rw [bornEq] at member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    intro value valueMember
    cases valueMember
  · rw [bornEq] at member started
    rw [mem_support_bind_iff] at member
    obtain ⟨installed, installedMember, member⟩ := member
    rw [support_map] at member
    obtain ⟨final, finalMember, rfl⟩ := member
    rw [bornControl] at installedMember
    obtain ⟨serverIs, ownersEmpty⟩ := install_facts setup codec modes replace route created born.2 installed installedMember
    obtain ⟨identityEq, pinsEmpty⟩ := PqxdhDeploymentHeadlinePinEnv.envGD_start setup codec checks t ensureInit
      identityIndex runtime created initial started
    have initialInv : Inv codec created.server.server.identity
        (PqxdhDeploymentSecrecy.Ledger.empty, ((initial, installed.1.2), installed.2)) := by
      refine ⟨identityEq, ?_, ⟨serverIs, fun owner shell kernel found => ?_⟩, fun entry member => by cases member⟩
      · rw [pinsEmpty]
        rfl
      · rw [ownersEmpty] at found
        cases found
    have finalInv := PqxdhRecordLiftFlat.support_keep_oracle _ (Inv codec created.server.server.identity)
      (fun query state held next nextMember => full_inv setup codec checks modes replace route t ensureInit identityIndex
        runtime serverKid bounds _ query state held next nextMember) _ _ initialInv final finalMember
    intro value valueMember
    simp only [Option.mem_def, Option.some.injEq] at valueMember
    subst valueMember
    refine ⟨fun server found entry entryMember => ?_, fun owner shell kernel found => finalInv.2.2.1.2 owner shell kernel found⟩
    obtain ⟨current, currentFound, currentIdentity⟩ := finalInv.2.2.1.1
    rw [found, Option.some.injEq] at currentFound
    subst currentFound
    rw [currentIdentity]
    exact finalInv.2.2.2 entry entryMember

/-- **The two env_g ideal-world invariants in `idealAuth`.** On every outcome of the integrity-ideal world with the ideal environment of a target, `PinFacts` holds. -/
theorem idealAuth_pinFacts {A X : Type} (route : RawCtxServerRouting.SenderDecoder)
    (t : PqxdhDeploymentIdealParams.Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (idealAuth setup codec route
      (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode
        adversary), PinFacts codec result :=
  ctxRun_pinFacts setup codec checks (fun _ => .replay) id route t ensureInit identityIndex runtime setup.serverKeyId bounds
    mode adversary

end Facts

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.summarize_owners_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.summarize_owners_extend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.pinOk_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.pinOk_extend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.shellsOk_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.shellsOk_extend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.fits_of_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.fits_of_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.quiet_of_envQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.quiet_of_envQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.uniformBytes_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.uniformBytes_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.send_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.send_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.drawBit_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.drawBit_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.secrecy_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.secrecy_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.summarize_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.summarize_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.inv_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.inv_append

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.forward_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.forward_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.forward_env' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.forward_env

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.secrecy_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.secrecy_inv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.full_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.full_inv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.effects_coin_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.effects_coin_control

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.startup_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.startup_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.install_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.install_facts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.ctxRun_pinFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.ctxRun_pinFacts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlinePinInvariant.idealAuth_pinFacts
