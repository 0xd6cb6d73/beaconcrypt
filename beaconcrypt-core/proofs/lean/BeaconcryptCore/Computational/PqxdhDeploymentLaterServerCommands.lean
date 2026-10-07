-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix

/-! LQ-F spike: the logged source compiled to the open private-service interface with the Server encapsulation exposed (the level of `KemEncapsulation.commands`, on which the KEM cut, the KEM games, T4 and T6 are stated). The exposed logged accept (`accept`) is the exposed accept of `KemEncapsulation` with the logged collector; forgetting the logged scalar gives it back (`ordered_fst`, `prepare_fst`, `accept_fst`). The logged command handler `impl` keeps the owner registry and the ephemeral log beside the native state: a raw accept runs the exposed logged accept and appends its entry, every other source14 request runs the unchanged exposed backend on the unchanged level-2 client, and the terminal read issues the ordinary identity-pool reveal of the Server's slot and returns it with the log. `commands` runs a program from an owner list, a log and a native state and returns the source outcome type `KemCommands.Outcome` of the existing chain, so every generic consumer of that type applies. For every source14 program, `commands` from any log is `KemEncapsulation.commands` (`commands_embed`), and the hidden logged program is the actual source command program (`actual_embed`). The module also states the raw-accept scan, finish and recording tag for programs of the logged source (`scan`, `finish`, `scan_finish`, `tag`, `tag_erase`), which count raw accepts exactly as `AcceptCut.scan` does and treat the terminal read as an ordinary request. No security statement and no assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhDeploymentLaterServerSource (Log Reveal Spec embed collectLogged collectLogged_fst)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result Next X : Type}

/-- A raw-accept cut of a logged-source program, as `AcceptCut.Cut`. -/
inductive Cut (KemSK Result : Type) where
  | complete (result : Result)
  | pending (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp (Spec KemSK) Result)

/-- Count every raw accept request of a logged-source program and stop before the one at the given ordinal. The terminal read and every other request are forwarded unchanged. -/
noncomputable def scan (work : OracleComp (Spec KemSK) Result) : Nat → OracleComp (Spec KemSK) (Cut KemSK Result) :=
  OracleComp.recOn work
    (fun result _ => pure (.complete result))
    (fun query next recurse index => match query with
      | .inl (.inl (.inr (.accept raw))) => match index with
        | 0 => pure (.pending raw next)
        | index + 1 => do
          let answer ← (Spec KemSK).query (.inl (.inl (.inr (.accept raw))))
          recurse answer index
      | query => do
        let answer ← (Spec KemSK).query query
        recurse answer index)

/-- Resume a cut with the literal suspended raw accept. -/
noncomputable def finish : Cut KemSK Result → OracleComp (Spec KemSK) Result
  | .complete result => pure result
  | .pending raw next => (Spec KemSK).query (.inl (.inl (.inr (.accept raw)))) >>= next

/-- Scanning and resuming give back the logged-source program. -/
theorem scan_finish (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    (scan work index >>= finish) = work := by
  induction work using OracleComp.inductionOn generalizing index with
  | pure result => rfl
  | query_bind query next ih =>
    rcases query with ((coin | request) | read) | later
    · change ((((Spec KemSK).query (.inl (.inl (.inl coin))) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (next answer) index) >>= finish) = _
      simp only [bind_assoc, ih]
    · cases request
      all_goals first
        | change ((((Spec KemSK).query _ : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>=
            finish) = _
          simp only [bind_assoc, ih]
        | skip
      cases index with
      | zero => rfl
      | succ index =>
        change ((((Spec KemSK).query _ : OracleComp (Spec KemSK) _) >>= fun answer => scan (next answer) index) >>=
          finish) = _
        simp only [bind_assoc, ih]
    · change ((((Spec KemSK).query (.inl (.inr read)) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (next answer) index) >>= finish) = _
      simp only [bind_assoc, ih]
    · change ((((Spec KemSK).query (.inr later) : OracleComp (Spec KemSK) _) >>= fun answer =>
        scan (next answer) index) >>= finish) = _
      simp only [bind_assoc, ih]

/-- Resume a cut and also return the suspended raw bytes and the public reply of the resumed accept, as `AcceptCutTag.tagFinish`. -/
noncomputable def tagFinish : Cut KemSK Result → OracleComp (Spec KemSK) (Result × Tag)
  | .complete result => pure (result, none)
  | .pending raw next => do
    let answer ← (Spec KemSK).query (.inl (.inl (.inr (.accept raw))))
    (fun result => (result, some (raw, answer))) <$> next answer

/-- The logged-source program suspended before its raw accept at the given ordinal and resumed with the recording finish. -/
noncomputable def tag (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    OracleComp (Spec KemSK) (Result × Tag) :=
  scan work index >>= tagFinish

/-- Forgetting the record gives back the logged-source program. -/
theorem tag_erase (work : OracleComp (Spec KemSK) Result) (index : Nat) :
    Prod.fst <$> tag work index = work := by
  have finish_erase : ∀ cut : Cut KemSK Result, Prod.fst <$> tagFinish cut = finish cut := by
    intro cut
    cases cut with
    | complete result => rfl
    | pending raw next => simp only [tagFinish, finish, map_bind, Functor.map_map, id_map']
  rw [tag, map_bind]
  simp only [finish_erase]
  exact scan_finish work index

/-- The exposed logged collector: the exposed collector of `KemSourceSuffix.ordered` run on the logged collector. -/
noncomputable def ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))
      (Option (Inputs Reader ScalarBytes Word32) × Option ScalarBytes) :=
  simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) (collectLogged raw)

/-- Forgetting the logged scalar gives the exposed collector of the existing chain. -/
theorem ordered_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    (fun result => (result.1.1, result.2)) <$> (ordered setup codec checks identityIndex raw).run consumed =
      (PqxdhRegistrationJointKemSourceSuffix.ordered setup codec checks identityIndex raw).run consumed := by
  rw [← PqxdhRegistrationJointKemSourceSuffix.ordered_source, ← collectLogged_fst, simulateQ_map, StateT.run_map,
    ordered]

/-- The exposed logged collector, unfolded at its encapsulation: verification, the steps before encapsulation, the exposed encapsulation and the literal suffix, with the generated ephemeral logged after the suffix. -/
theorem ordered_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    ordered setup codec checks identityIndex raw = (do
      let verified ← simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
        (PqxdhServerRootPreparation.verifyInput raw)
      match verified with
      | none => pure (none, none)
      | some verified => do
          let ephemeral ← simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
            (PqxdhRegistrationJointKemCollected.beforeEncapsulation verified)
          match ephemeral with
          | none => pure (none, none)
          | some ephemeral => do
              let reply ← (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
                (.encapsulate verified.keys.pqKey)
              let input ← PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw verified
                ephemeral reply
              pure (input, some ephemeral.secret)) := by
  simp only [ordered, collectLogged, simulateQ_bind]
  apply bind_congr
  intro verified
  cases verified with
  | none => rfl
  | some verified =>
    simp only [simulateQ_bind]
    apply bind_congr
    intro ephemeral
    cases ephemeral <;> simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query,
      PqxdhRegistrationJointKemSourceSuffix.suffix]

/-- The exposed logged preparation: the logged collector from the current consumed set, with the full native state kept. -/
noncomputable def prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) : PqxdhRegistrationJointKemEncapsulation.Client KemSK
      ((Option (Inputs Reader ScalarBytes Word32) × List Pqxdh.Bytes) × Option ScalarBytes) := fun state =>
  (fun result => (((result.1.1, result.2), result.1.2), state)) <$>
    (ordered setup codec checks identityIndex raw).run state.2.server.consumed

/-- Forgetting the logged scalar gives the exposed preparation of the existing chain. -/
theorem prepare_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (fun result => (result.1.1, result.2)) <$> (prepare setup codec checks identityIndex raw).run state =
      (PqxdhRegistrationJointKemEncapsulation.prepare setup codec checks identityIndex raw).run state := by
  rw [PqxdhRegistrationJointKemSourceSuffix.preparation, ← ordered_fst, Functor.map_map]
  simp only [prepare, StateT.run, Functor.map_map]

/-- The exposed logged raw accept: the exposed accept of `KemEncapsulation` with the logged collector, returning the reply and the logged scalar. -/
noncomputable def accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    PqxdhRegistrationJointKemEncapsulation.Client KemSK (Option Nat × Option ScalarBytes) := do
  let before ← PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native nativeGet)
  let collected ← prepare setup codec checks identityIndex raw
  let reply ← PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected.1))
  pure (reply, collected.2)

/-- Forgetting the logged scalar gives the exposed accept of the existing chain. -/
theorem accept_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (fun result => (result.1.1, result.2)) <$> (accept setup codec checks identityIndex publicIdentity raw).run state =
      (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run state := by
  simp only [accept, PqxdhRegistrationJointKemEncapsulation.accept, StateT.run_bind, map_bind]
  apply bind_congr
  intro before
  rw [← prepare_fst, bind_map_left]
  apply bind_congr
  intro collected
  simp only [StateT.run_pure, map_pure, Prod.mk.eta, bind_pure]

/-- The exposed logged raw accept at its encapsulation: the logged collector from the current consumed set, then the accept tail on its collected input, with the logged scalar returned beside the reply. -/
theorem accept_ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    (accept setup codec checks identityIndex publicIdentity raw).run state = (do
      let collected ← (ordered setup codec checks identityIndex raw).run state.2.server.consumed
      let answer ← (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 (collected.1.1, collected.2)))).run state
      pure ((answer.1, collected.1.2), answer.2)) := by
  simp only [accept, StateT.run_bind]
  simp only [PqxdhRegistrationJointKemEncapsulation.lift, PqxdhRegistrationJointOpenBackend.native,
    nativeGet, localState, StateT.run, PqxdhLiveKemBirth.coins, simulateQ_pure, pure_bind]
  simp only [prepare, bind_map_left]
  rfl

/-- The local state of the logged command compiler: the owner registry and the ephemeral log. -/
abbrev Local := List EncodedEntry × Log

/-- The logged command handler over the exposed interface. A raw accept runs the exposed logged accept and appends its entry to the log; every other source14 request runs the unchanged exposed backend on the unchanged level-2 client; the terminal read reveals the Server's identity-pool slot and returns it with the log. -/
noncomputable def impl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (Spec KemSK) (StateT Local (PqxdhRegistrationJointKemEncapsulation.Client KemSK))
  | .inl (.inl (.inr (.accept raw))) => fun held => (fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
      accept setup codec checks identityIndex publicIdentity raw
  | .inl query => fun held => (fun result => (result.1, (result.2, held.2))) <$>
      simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity)
        ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run held.1)
  | .inr _ => fun held state => (fun seed => (((seed, held.2), held), state)) <$>
      ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inl (.inl (.inr (.reveal identityIndex)))) :
        OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Option IdentitySeed))

/-- The complete logged command run: final result, owner registry, log and native state. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) ((Result × Local) × NativeState KemSK) :=
  ((simulateQ (impl setup codec checks identityIndex publicIdentity) work).run (owners, log)).run state

/-- The logged command program with the outcome type of the existing chain: the final log is dropped. -/
noncomputable def commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK Result) :=
  (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
    run setup codec checks identityIndex publicIdentity work owners log state

/-- A logged run of a sequential program is the run of its first part followed by the run of the rest from the reached owners, log and native state. -/
theorem run_bind (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (next : Result → OracleComp (Spec KemSK) Next) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    run setup codec checks identityIndex publicIdentity (work >>= next) owners log state =
      (run setup codec checks identityIndex publicIdentity work owners log state >>= fun result =>
        run setup codec checks identityIndex publicIdentity (next result.1.1) result.1.2.1 result.1.2.2 result.2) := by
  simp only [run, simulateQ_bind, StateT.run_bind]

/-- Keeping a fixed log beside a level-2 client step and dropping it again changes nothing. -/
theorem map_held {α : Type} (work : PqxdhRegistrationJointKemEncapsulation.Client KemSK (α × List EncodedEntry))
    (log : Log) (state : NativeState KemSK) :
    (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
      ((fun result => (result.1, (result.2, log))) <$> work).run state = work.run state := by
  rw [StateT.run_map, Functor.map_map]
  exact id_map _

/-- Every source14 request of the logged command handler projects to the exposed backend of the existing chain, whatever the log. -/
theorem query_embed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
      ((impl setup codec checks identityIndex publicIdentity (.inl query)).run (owners, log)).run state =
      (simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity)
        ((PqxdhRegistrationJointRevealSchedule.client setup codec query).run owners)).run state := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request
    case accept raw =>
      have logged := accept_fst setup codec checks identityIndex publicIdentity raw state
      change (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
        ((fun answer => (answer.1, (owners, log ++ [answer.2]))) <$>
          accept setup codec checks identityIndex publicIdentity raw).run state = _
      simp only [PqxdhRegistrationJointRevealSchedule.client, PqxdhRegistrationJointServiceSchedule.handler,
        StateT.run_lift, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, PqxdhRegistrationJointKemEncapsulation.impl,
        StateT.run_bind, StateT.run_pure, StateT.run_map, Functor.map_map]
      rw [← logged, bind_map_left]
      simp only [map_eq_bind_pure_comp, Function.comp_def]
    all_goals exact map_held _ log state
  all_goals exact map_held _ log state

/-- For every source14 program, the logged command program from any log is the exposed command program of the existing chain. -/
theorem commands_embed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity (simulateQ embed work) owners log state =
      PqxdhRegistrationJointKemEncapsulation.commands setup codec checks identityIndex publicIdentity work owners
        state := by
  induction work using OracleComp.inductionOn generalizing owners log state with
  | pure value => simp [commands, run, PqxdhRegistrationJointKemEncapsulation.commands]
  | query_bind query next ih =>
    have step := query_embed setup codec checks identityIndex publicIdentity query owners log state
    simp only [commands, run, PqxdhRegistrationJointKemEncapsulation.commands] at ih ⊢
    simp only [simulateQ_bind, simulateQ_spec_query, embed, StateT.run_bind, map_bind]
    rw [← step, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2.1 result.1.2.2 result.2

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.scan_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.scan_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.tag_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.tag_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.ordered_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.ordered_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.ordered_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.ordered_split

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.prepare_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.prepare_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.accept_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.accept_fst

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.accept_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.accept_ordered

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.run_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.map_held' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.map_held

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.query_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.query_embed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.commands_embed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands.commands_embed
