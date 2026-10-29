-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordHiding
import BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-! The actual cursor-filtered World is flattened below the secrecy ledger. Its native state retains the environment, public cursor shell, compiled record control and complete CTX private state. Uniform bytes and test bits remain actual ledger draws; a cursor refusal stutters before an oversized established send reaches the record interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.CborRawRecordFlat
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Spec FullSpec Handle asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (KnownAt coinStep support_keep_oracle support_run_fst)
variable {n : Nat} {ι : Type} {base : OracleSpec ι} {KemSK Reader Response E X : Type}

abbrev NativeState (n : Nat) (E : Type) := PqxdhRecordLiftFlat.NativeState n (E × CborRecordWorldClient.Shell)

def project (state : NativeState n E) : PqxdhRecordLiftFlat.NativeState n E :=
  ((state.1.1.1, state.1.2), state.2)

noncomputable def clientImpl (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT ((E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n)
      (OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n))) := fun query state =>
  (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler ((native env query).run state.1.1)).run state.1.2)).run state.2

theorem clientImpl_run (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (state : (E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) :
    (clientImpl env codec route query).run state =
      (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
        (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
          ((simulateQ CborRecordWorldClient.handler ((native env query).run state.1.1)).run state.1.2)).run state.2 := rfl

noncomputable def nativeImpl (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) : QueryImpl Spec (StateT (NativeState n E) ProbComp) :=
  ((ctxInterpreter modes replace setup codec).mapStateTBase (clientImpl env codec route)).flattenStateT

noncomputable def fullImpl (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × NativeState n E) ProbComp) :=
  ((nativeImpl modes replace setup codec route env).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds)).flattenStateT

theorem fullImpl_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (query : FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : NativeState n E) :
    (fullImpl modes replace setup codec route env serverKid bounds query).run (ledger, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (nativeImpl modes replace setup codec route env)
          ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds query).run ledger)).run state := rfl

theorem nativeImpl_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (state : NativeState n E) :
    (nativeImpl modes replace setup codec route env query).run state =
      (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
        (simulateQ (ctxInterpreter modes replace setup codec)
          ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
            ((simulateQ CborRecordWorldClient.handler ((native env query).run state.1.1.1)).run state.1.1.2)).run
              state.1.2)).run state.2 := by
  simp only [nativeImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run_mk, clientImpl_run, simulateQ_map, StateT.run_map, Functor.map_map]

/-- Refusing a send leaves its caller-known handle intact; every forwarded compiled request preserves the same source invariant. -/
theorem nativeImpl_known (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (handle : Handle) (query : Spec.Domain) (state : NativeState n E)
    (known : KnownAt state.1.2 handle) :
    ∀ result ∈ support ((nativeImpl modes replace setup codec route env query).run state), KnownAt result.2.1.2 handle := by
  intro result reached
  rw [nativeImpl_run, support_map] at reached
  obtain ⟨inner, member, rfl⟩ := reached
  exact support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route) (fun control => KnownAt control handle)
    (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle) _ state.1.2 known inner.1
      (support_run_fst _ _ _ inner member)


def sendQuery (handle : Handle) (plaintext : Pqxdh.Bytes) : (WorldSpec n).Domain :=
  match handle with
  | .peer keyId => .inr (.inr (.inl (.inl (plaintext, keyId))))
  | .owner owner => .inr (.inr (.inr (owner, .inl plaintext)))

def sendRefusal (handle : Handle) (plaintext : Pqxdh.Bytes) (shell : CborRecordWorldClient.Shell) :
    Option (Option RawCtxSourceSend.Encrypted) :=
  match handle with
  | .peer keyId => CborRecordWorldClient.refusal (sendQuery (n := n) (.peer keyId) plaintext) shell
  | .owner owner => CborRecordWorldClient.refusal (sendQuery (n := n) (.owner owner) plaintext) shell

/-- Native CBOR refusal reads a send's length and public cursor, so byte shifts and equal-length test alternatives take the same branch. -/
theorem refusal_length (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (shell : CborRecordWorldClient.Shell) :
    sendRefusal (n := n) handle first shell = sendRefusal (n := n) handle second shell := by
  cases handle <;> simp only [sendRefusal, sendQuery, CborRecordWorldClient.refusal, length] <;> rfl

private theorem advance_length (first second : Pqxdh.Bytes) (length : first.length = second.length) :
    CborRecordWorldClient.advance first = CborRecordWorldClient.advance second := by
  have empty : first.isEmpty = second.isEmpty := by
    cases first <;> cases second <;> simp_all
  funext sequence
  simp only [CborRecordWorldClient.advance, empty]

/-- Equal-length sends advance the same public cursor even when their optional ciphertext replies differ. -/
theorem next_length (handle : Handle) (first second : Pqxdh.Bytes) (length : first.length = second.length)
    (reply₁ : (WorldSpec n).Range (sendQuery handle first)) (reply₂ : (WorldSpec n).Range (sendQuery handle second))
    (shell : CborRecordWorldClient.Shell) :
    CborRecordWorldClient.next (sendQuery handle first) reply₁ shell =
      CborRecordWorldClient.next (sendQuery handle second) reply₂ shell := by
  cases handle <;> simp only [sendQuery, CborRecordWorldClient.next,
    CborRecordWorldClient.advanceServer, CborRecordWorldClient.advanceOwner, advance_length first second length]


private theorem refusal_nonsend (query : (WorldSpec n).Domain)
    (free : ¬ PqxdhRecordLiftBudget.WorldRecord .send query) (shell : CborRecordWorldClient.Shell) :
    CborRecordWorldClient.refusal query shell = none := by
  rcases query with created | effect | (send | raw) | ⟨owner, send | raw⟩
  all_goals first | rfl | exact False.elim (free rfl)

/-- An actual World program issuing no established send keeps its exact original execution after forgetting only the cursor shell. -/
theorem client_no_send {Result : Type} (work : OracleComp (WorldSpec n) Result)
    (bounded : work.IsQueryBoundP (PqxdhRecordLiftBudget.WorldRecord .send) 0)
    (shell : CborRecordWorldClient.Shell) : CborRecordWorldClient.client work shell = work := by
  unfold CborRecordWorldClient.client
  induction work using OracleComp.inductionOn generalizing shell with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    have free : ¬PqxdhRecordLiftBudget.WorldRecord .send query := by
      intro selected
      exact bounded.1.elim (fun notSelected => notSelected selected) (Nat.not_lt_zero _)
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
    change (Prod.fst <$> ((CborRecordWorldClient.handler query).run shell >>= fun result =>
      (simulateQ CborRecordWorldClient.handler (next result.1)).run result.2)) = _
    rw [show (CborRecordWorldClient.handler query).run shell = CborRecordWorldClient.forward query shell by
      simp only [CborRecordWorldClient.handler, StateT.run, refusal_nonsend query free shell]]
    simp only [CborRecordWorldClient.forward, map_bind, bind_map_left]
    apply bind_congr
    intro reply
    exact ih reply (by simpa only [Nat.zero_sub, ite_self] using bounded.2 reply) (CborRecordWorldClient.next query reply shell)


/-- Raw receives, registration effects and coins have the exact original native execution after forgetting only public cursor metadata. -/
theorem nativeImpl_project_nonrecord (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (state : NativeState n E)
    (free : ¬PqxdhRecordLiftBudget.NativeRecord .send query) :
    Prod.map id project <$> (nativeImpl modes replace setup codec route env query).run state =
      (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env query).run (project state) := by
  have bounded := PqxdhRecordLiftBudget.native_record_step env .send query state.1.1.1
  rw [ite_eq_right free] at bounded
  have same := client_no_send ((native env query).run state.1.1.1) bounded state.1.1.2
  have observed := congrArg (fun work => (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ (ctxInterpreter modes replace setup codec)
      ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) work).run state.1.2)).run state.2) same
  rw [nativeImpl_run, PqxdhRecordLiftFlat.nativeImpl_run]
  simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run_map, Functor.map_map,
    project, Prod.map, id_eq] using observed


def clientProject (state : (E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) :
    E × PqxdhRecordLiftProtocol.Control n := (state.1.1, state.2)

def clientWithShell (shell : CborRecordWorldClient.Shell) (state : E × PqxdhRecordLiftProtocol.Control n) :
    (E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n := ((state.1, shell), state.2)

theorem old_clientImpl_run (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) (state : E × PqxdhRecordLiftProtocol.Control n) :
    (PqxdhRecordLiftFlat.clientImpl env codec route query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) ((native env query).run state.1)).run state.2 := rfl

/-- Before any service interpretation, every non-send native command projects to the exact original compiled client. -/
theorem clientImpl_project_nonrecord (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (state : (E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n)
    (free : ¬PqxdhRecordLiftBudget.NativeRecord .send query) :
    Prod.map id clientProject <$> (clientImpl env codec route query).run state =
      (PqxdhRecordLiftFlat.clientImpl env codec route query).run (clientProject state) := by
  have bounded := PqxdhRecordLiftBudget.native_record_step env .send query state.1.1
  rw [ite_eq_right free] at bounded
  have same := client_no_send ((native env query).run state.1.1) bounded state.1.2
  have observed := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) work).run state.2) same
  rw [clientImpl_run, old_clientImpl_run]
  simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run_map, Functor.map_map,
    clientProject, Prod.map, id_eq] using observed

noncomputable def nextSend (handle : Handle) (plaintext : Pqxdh.Bytes) (reply : Option RawCtxSourceSend.Encrypted)
    (shell : CborRecordWorldClient.Shell) : CborRecordWorldClient.Shell :=
  match handle with
  | .peer keyId => CborRecordWorldClient.next (sendQuery (n := n) (.peer keyId) plaintext) reply shell
  | .owner owner => CborRecordWorldClient.next (sendQuery (n := n) (.owner owner) plaintext) reply shell

private theorem cursor_run (query : (WorldSpec n).Domain) (shell : CborRecordWorldClient.Shell) :
    (CborRecordWorldClient.handler query).run shell =
      match CborRecordWorldClient.refusal query shell with
      | some reply => pure (reply, shell)
      | none => CborRecordWorldClient.forward query shell := rfl

private theorem lift_run {Result : Type} (work : OracleComp (WorldSpec n) Result) (state : E) :
    (StateT.lift work).run state = (fun result => (result, state)) <$> work := by
  simp only [StateT.lift, StateT.run, map_eq_bind_pure_comp]
  rfl

/-- The exact pre-service send either fully stutters on native CBOR refusal or forwards the original compiled send, retaining its actual reply and updated public cursor. -/
theorem clientImpl_send (env : Environment n E) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (handle : Handle) (plaintext : Pqxdh.Bytes)
    (state : (E × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) :
    (simulateQ (clientImpl env codec route) (PqxdhDeploymentSecrecy.send handle plaintext)).run state =
      match sendRefusal (n := n) handle plaintext state.1.2 with
      | some reply => pure (reply, state)
      | none => (fun result => (result.1,
          clientWithShell (nextSend (n := n) handle plaintext result.1 state.1.2) result.2)) <$>
        (simulateQ (PqxdhRecordLiftFlat.clientImpl env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run (clientProject state) := by
  cases handle
  all_goals
    simp only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query, sendRefusal, nextSend, sendQuery]
    rw [clientImpl_run, old_clientImpl_run]
    simp only [native]
    erw [lift_run]
    simp only [simulateQ_map, StateT.run_map, simulateQ_spec_query]
    rw [cursor_run]
    split
    all_goals simp_all only [CborRecordWorldClient.forward, simulateQ_pure, StateT.run_pure,
      simulateQ_map, StateT.run_map, Functor.map_map, simulateQ_spec_query, clientProject, clientWithShell]
    all_goals rfl

end BeaconcryptCore.Computational.CborRawRecordFlat

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.fullImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.fullImpl_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_known

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.refusal_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.refusal_length

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.next_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.next_length

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.client_no_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.client_no_send

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_project_nonrecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.nativeImpl_project_nonrecord

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.old_clientImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.old_clientImpl_run

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_project_nonrecord' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_project_nonrecord

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFlat.clientImpl_send
