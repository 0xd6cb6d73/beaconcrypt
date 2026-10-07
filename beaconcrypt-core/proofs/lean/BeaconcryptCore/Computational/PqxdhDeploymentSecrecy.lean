-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentNative
import BeaconcryptCore.Computational.PqxdhDeploymentTranscript

/-! The complete common deployment experiment (CE-2): the secrecy commands, the transcript and both observation modes on top of the native handler of `PqxdhDeploymentNative`. The secrecy layer `ledgerImpl` forwards every coin and command unchanged and records it with its mode O reply in the transcript. `test handle left right` requires `|left| = |right| > 0`; the first admitted test draws the hidden bit with one experiment coin and fixes its handle as the test session; a later test is admitted only on the same handle or on a handle with the same public designation as the first, computed on the transcript so far; an admitted test is exactly one send of `left` or `right` by the bit, with the send's allocation, failure and rollback behaviour. `fresh handle length` requires `min ≤ length ≤ max`, draws a uniform message of `length` bytes with one experiment coin per byte when the command is issued, keeps it private and sends it on the handle. A rejected secrecy command changes nothing but the transcript. The experiment's draws are never recorded in the transcript. The CE handler is this layer composed with the native handler on the product state `Ledger × State`; running an adversary under it is running the wrapped adversary `wrap` against the native handler (`run_wrap`). Mode P is the mode O experiment behind `observeFull`, whose replies are the mode P projections of the mode O replies (`observeFull_project`). No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentSecrecy
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentInterface (Spec Command Handle Secrecy FullSpec FullSuccessSpec ModeSpec Mode Entry Logs
  FreshBounds observeFull asModeO project)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The test session: the hidden bit, the handle of the first admitted test and the number of admitted tests. -/
structure TestState where
  bit : Bool
  first : Handle
  count : Nat

/-- One admitted fresh message: its handle, the private message and the send's reply. -/
structure FreshEntry where
  handle : Handle
  message : Pqxdh.Bytes
  reply : Option RawCtxSourceSend.Encrypted

/-- The secrecy layer's state: the transcript, the test session and the fresh messages in order. -/
structure Ledger where
  transcript : List Entry
  test : Option TestState
  fresh : List FreshEntry

/-- The initial ledger. -/
def Ledger.empty : Ledger := ⟨[], none, []⟩

/-- Record one adversary query with its mode O reply. -/
def Ledger.record (ledger : Ledger) (query : PqxdhDeploymentInterface.Query) (reply : FullSpec.Range query) : Ledger :=
  { ledger with transcript := ledger.transcript ++ [⟨query, reply⟩] }

/-- One experiment coin of the native interface. -/
def coin (bound : Nat) : OracleComp Spec (Fin (bound + 1)) :=
  (Spec.query (.inl bound) : OracleComp Spec _)

/-- The hidden bit: one coin in `Fin 2`. -/
def drawBit : OracleComp Spec Bool := (fun value : Fin 2 => decide (value = 1)) <$> coin 1

/-- A uniform message of `length` bytes, one coin in `Fin 256` per byte. -/
def uniformBytes : Nat → OracleComp Spec Pqxdh.Bytes
  | 0 => pure []
  | length + 1 => do
      let byte ← coin 255
      let rest ← uniformBytes length
      pure (UInt8.ofNat byte.val :: rest)

/-- The native send on a handle: a Server send to a peer key ID or a Beacon send on an owner handle. -/
def send : Handle → Pqxdh.Bytes → OracleComp Spec (Option RawCtxSourceSend.Encrypted)
  | .peer keyId, plaintext => (Spec.query (.inr (.serverSend keyId plaintext)) : OracleComp Spec _)
  | .owner index, plaintext => (Spec.query (.inr (.beaconSend index plaintext)) : OracleComp Spec _)

/-- A later test handle belongs to the test session: it is the first handle, or it has the first handle's public designation. -/
def SameSession (codec : Codec Reader Response) (serverKid : Std.U64) (transcript : List Entry) (first handle : Handle) :
    Prop :=
  handle = first ∨ ∃ target, PqxdhDeploymentTranscript.designate codec serverKid transcript first = some target ∧
    PqxdhDeploymentTranscript.designate codec serverKid transcript handle = some target

/-- The two test messages have equal nonzero length. -/
def Admissible (left right : Pqxdh.Bytes) : Prop := left.length = right.length ∧ 0 < left.length

open Classical in
/-- The secrecy layer. Coins and commands are forwarded unchanged and recorded; `test` and `fresh` are sends of experiment-chosen messages, recorded with their reply. -/
noncomputable def ledgerImpl (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT Ledger (OracleComp Spec))
  | .inl query => fun ledger =>
      (fun reply => (reply, ledger.record (.inl query) reply)) <$> (Spec.query query : OracleComp Spec _)
  | .inr (.test handle left right) => fun ledger =>
      if Admissible left right then
        match ledger.test with
        | none => do
            let bit ← drawBit
            let reply ← send handle (if bit then right else left)
            pure (reply, { ledger.record (.inr (.test handle left right)) reply with test := some ⟨bit, handle, 1⟩ })
        | some session =>
            if SameSession codec serverKid ledger.transcript session.first handle then do
              let reply ← send handle (if session.bit then right else left)
              pure (reply, { ledger.record (.inr (.test handle left right)) reply with
                test := some { session with count := session.count + 1 } })
            else pure (none, ledger.record (.inr (.test handle left right)) none)
      else pure (none, ledger.record (.inr (.test handle left right)) none)
  | .inr (.fresh handle length) => fun ledger =>
      if bounds.min ≤ length ∧ length ≤ bounds.max then do
        let message ← uniformBytes length
        let reply ← send handle message
        pure (reply, { ledger.record (.inr (.fresh handle length)) reply with
          fresh := ledger.fresh ++ [⟨handle, message, reply⟩] })
      else pure (none, ledger.record (.inr (.fresh handle length)) none)

/-- The experiment state: the secrecy layer's ledger and the native deployment state. -/
abbrev State (KemSK : Type) := Ledger × PqxdhDeploymentNative.State KemSK

/-- The record logs of an experiment state: its transcript and its produced frames. -/
def logs (state : State KemSK) : Logs := ⟨state.1.transcript, state.2.produced⟩

/-- The CE handler: the secrecy layer composed with the native handler, on the product state. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (State KemSK) ProbComp) :=
  ((PqxdhDeploymentNative.handler setup codec checks route serverSeed).mapStateTBase
    (ledgerImpl codec setup.serverKeyId bounds)).flattenStateT

/-- A complete-interface adversary as a native-interface program that runs the secrecy layer itself and returns its final ledger. -/
noncomputable def wrap (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp FullSpec X) : OracleComp Spec (X × Ledger) :=
  (simulateQ (ledgerImpl codec serverKid bounds) adversary).run Ledger.empty

/-- The common deployment experiment in observation mode `mode`: the actual Server constructor with a generated seed (never a supplied one), then the adversary against the CE handler from the empty ledger and the initial native state. A constructor failure ends the run with no outcome. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × State KemSK)) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (handler setup codec checks route created.seed bounds) (asModeO mode adversary)).run
        (Ledger.empty, PqxdhDeploymentNative.initial created)

/-- Running an adversary under the CE handler is running the wrapped adversary under the native handler, with the ledger moved into the state. -/
theorem run_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (bounds : FreshBounds)
    (adversary : OracleComp FullSpec X) (state : PqxdhDeploymentNative.State KemSK) :
    (simulateQ (handler setup codec checks route serverSeed bounds) adversary).run (Ledger.empty, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
          (wrap codec setup.serverKeyId bounds adversary)).run state := by
  rw [wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  simp only [handler]
  exact (id_map _).symm

/-- The common deployment experiment is the native deployment game of the wrapped adversary, with the ledger moved into the final state. -/
theorem game_wrap (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      (fun outcome => (outcome.1.map fun result => (result.1, result.2.1.1, (result.2.1.2, result.2.2)), outcome.2)) <$>
        (PqxdhDeploymentNative.game setup codec checks route ensureInit identityIndex
          (wrap codec setup.serverKeyId bounds (asModeO mode adversary))).run runtime := by
  simp only [game, PqxdhDeploymentNative.game, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨_ | created, after⟩
  · simp only [map_pure, Option.map_none]
  · have wrapped := run_wrap setup codec checks route created.seed bounds (asModeO mode adversary)
      (PqxdhDeploymentNative.initial created)
    simp only [StateT.run] at wrapped
    simp only [wrapped, Functor.map_map, Option.map_some]

/-- Mode P answers every query with the mode P projection of the mode O reply. -/
theorem observeFull_project (query : PqxdhDeploymentInterface.Query) :
    observeFull query = project .P query <$> (FullSpec.query query : OracleComp FullSpec _) := by
  rcases query with (coin | command) | secrecy
  · exact (id_map _).symm
  · cases command <;> rfl
  · exact (id_map _).symm

/-- Coins and sends, the only native queries the secrecy commands may issue. -/
def coinOrSend : Spec.Domain → Bool
  | .inl _ => true
  | .inr (.serverSend _ _) => true
  | .inr (.beaconSend _ _) => true
  | .inr _ => false

/-- The secrecy commands issue nothing but experiment coins and sends: no registration command, no HMAC or BLAKE2b query and no raw receive. In particular they never touch the Extract family, the pending tokens, the consumed registration IDs or an owner's phase. -/
theorem secrecy_frame (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (secrecy : Secrecy) (ledger : Ledger) :
    ((ledgerImpl codec serverKid bounds (.inr secrecy)).run ledger).IsQueryBoundP
      (fun query => coinOrSend query = false) 0 := by
  have pureFrame : ∀ {Value : Type} (value : Value),
      (pure value : OracleComp Spec Value).IsQueryBoundP (fun query => coinOrSend query = false) 0 :=
    fun _ => trivial
  have sendFrame : ∀ handle plaintext, (send handle plaintext).IsQueryBoundP
      (fun query => coinOrSend query = false) 0 := by
    intro handle plaintext
    cases handle with
    | peer keyId =>
        unfold send
        rw [isQueryBoundP_query_iff]
        intro hit
        simp [coinOrSend] at hit
    | owner index =>
        unfold send
        rw [isQueryBoundP_query_iff]
        intro hit
        simp [coinOrSend] at hit
  have coinFrame : ∀ bound, (coin bound).IsQueryBoundP
      (fun query => coinOrSend query = false) 0 := by
    intro bound
    unfold coin
    rw [isQueryBoundP_query_iff]
    intro hit
    simp [coinOrSend] at hit
  have bytesFrame : ∀ length, (uniformBytes length).IsQueryBoundP
      (fun query => coinOrSend query = false) 0 := by
    intro length
    induction length with
    | zero => trivial
    | succ length ih =>
        unfold uniformBytes
        exact isQueryBoundP_bind (coinFrame 255) fun _ _ =>
          isQueryBoundP_bind ih fun _ _ => pureFrame _
  rcases secrecy with ⟨handle, left, right⟩ | ⟨handle, length⟩
  · simp only [ledgerImpl, StateT.run]
    split
    · split
      · exact isQueryBoundP_bind (by unfold drawBit; rw [isQueryBoundP_map_iff]; exact coinFrame 1) fun _ _ =>
          isQueryBoundP_bind (sendFrame _ _) fun _ _ => pureFrame _
      · split
        · exact isQueryBoundP_bind (sendFrame _ _) fun _ _ => pureFrame _
        · trivial
    · trivial
  · simp only [ledgerImpl, StateT.run]
    split
    · exact isQueryBoundP_bind (bytesFrame length) fun _ _ => isQueryBoundP_bind (sendFrame _ _) fun _ _ => pureFrame _
    · trivial

/-- A forwarded coin or command is answered by exactly that query and recorded with its reply. -/
theorem ledgerImpl_forward (codec : Codec Reader Response) (serverKid : Std.U64) (bounds : FreshBounds)
    (query : Spec.Domain) (ledger : Ledger) :
    (ledgerImpl codec serverKid bounds (.inl query)).run ledger =
      (fun reply => (reply, ledger.record (.inl query) reply)) <$> (Spec.query query : OracleComp Spec _) := rfl

end BeaconcryptCore.Computational.PqxdhDeploymentSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.run_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.run_wrap

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.game_wrap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.game_wrap

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.observeFull_project' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.observeFull_project

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.secrecy_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.secrecy_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.ledgerImpl_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSecrecy.ledgerImpl_forward
