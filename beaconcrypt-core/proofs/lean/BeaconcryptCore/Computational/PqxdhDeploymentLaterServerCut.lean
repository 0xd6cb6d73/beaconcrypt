-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCommands
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerKemHop
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque

/-! LQ-F: the KEM cut of the logged source at the encapsulation of the selected raw accept. `exposeAt` is `AcceptKemCut.exposeAt` for programs of the logged source: the logged command compiler runs the program up to the raw accept at the designated raw-accept ordinal with every encapsulation interpreted in place, then runs the exposed logged accept, appends its entry to the log and runs the rest of the tagged program. `rawResume` is the saved continuation of an active cut: the literal suffix after the encapsulation reply, the unchanged accept tail and the rest of the tagged program, from the log at the cut extended by the selected accept's ephemeral scalar, which is an explicit value fixed before the encapsulation (`ordered_cut`, `accept_scan`, `exposeAt_scan`, `rawCut_shape`). A completed cut has a non-accepted tag (`accepted_reached`). Interpreting the one exposed encapsulation gives the logged command program of the tagged program (`exposeAt_actual`). Fed the ordinary challenge reply, the saved continuation is the candidate-free opaque resumption followed by the logged rest (`rawResume_opaque`), by the existing `KemOpaqueResume.resume_reply`, which takes the rest as an argument: this is the core of T6 for the logged source, and it holds because the logged entry is the explicit ephemeral and depends on neither the ciphertext nor the candidate. The KEM hop for the logged exposure is the generic hop of `PqxdhDeploymentLaterServerKemHop` at `scanned` (`kem_hop`), with one ordinary one-key ML-KEM IND-CCA advantage and one ordinary correctness error. The selected-first reservation and the selected-disclosure monitor are the generic `PqxdhDynamicKemJointSource.selected_source` and `PqxdhDynamicKemJointStopping.history_event` at the hidden logged program (`selected_first`, `monitor`); the creation cap they need is a premise here. No assumption, contract or premise beyond those of the instantiated theorems is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut
open PqxdhKemIndCca PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerRootPreparation (Inputs Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointAcceptCutTag (Tag accepted decideTag)
open PqxdhRegistrationJointKemEncapsulation (actual forward)
open PqxdhRegistrationJointAcceptKemCut (hide free_hide scan_free_bind scan_bind_zero support_simulate scan_hide
  before_free actual_hide tail_none)
open PqxdhRegistrationJointServerBirth (ClientCreated)
open PqxdhDeploymentLaterServerSource (Log Spec)
open PqxdhDeploymentLaterServerCommands (Cut scan tag ordered accept run commands)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R Result Next : Type}

/-- The logged-source continuation after the selected accept, recording the selected raw bytes and that accept's public reply. -/
noncomputable def tagged (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (Spec KemSK) X) (answer : Option Nat) : OracleComp (Spec KemSK) R :=
  (fun result => observe (result, some (raw, answer))) <$> next answer

/-- The logged command compiler on the tagged logged program with only the encapsulation of the raw accept at ordinal `index` exposed. The log at the cut is extended by the selected accept's entry before the rest runs. -/
noncomputable def exposeAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let reached ← hide setup (run setup codec checks identityIndex publicIdentity (scan work index) owners log state)
  match reached.1.1 with
  | .complete result => pure ((observe (result, none), reached.1.2.1), reached.2)
  | .pending raw next => do
    let answer ← (accept setup codec checks identityIndex publicIdentity raw).run reached.2
    hide setup (commands setup codec checks identityIndex publicIdentity
      (tagged observe raw next answer.1.1) reached.1.2.1 (reached.1.2.2 ++ [answer.1.2]) answer.2)

/-- The saved continuation of an active cut: the literal suffix after the encapsulation reply, the unchanged accept tail, and the rest of the tagged logged program from the log at the cut extended by the explicit ephemeral of the selected accept. -/
noncomputable def rawResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : Verified Reader) (ephemeral : Ephemeral ScalarBytes) (consumed : List Pqxdh.Bytes)
    (state : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (Spec KemSK) X) (reply : PqxdhRegistrationJointKemCut.Reply) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let input ← (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw value
    ephemeral reply).run consumed
  let answer ← (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 input))).run state
  hide setup (commands setup codec checks identityIndex publicIdentity
    (tagged observe raw next answer.1) owners (log ++ [some ephemeral.secret]) answer.2)

/-- A doubly stateful interpretation only removes results of an oracle program. -/
theorem support_nested {κ κ' : Type} {spec : OracleSpec κ} {target : OracleSpec κ'} {σ τ : Type}
    (handler : QueryImpl spec (StateT σ (StateT τ (OracleComp target)))) (work : OracleComp spec Result)
    (held : σ) (state : τ) (outcome : (Result × σ) × τ)
    (reached : outcome ∈ support (((simulateQ handler work).run held).run state)) : outcome.1.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing held state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst reached
    simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, _, reached⟩ := reached
    exact (mem_support_bind_iff _ _ _).mpr
      ⟨middle.1.1, mem_support_query query _, ih middle.1.1 middle.1.2 middle.2 reached⟩

/-- Every outcome of a logged run carries a result of the logged-source program. -/
theorem run_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK)
    (outcome : (Result × PqxdhDeploymentLaterServerCommands.Local) × NativeState KemSK)
    (reached : outcome ∈ support (run setup codec checks identityIndex publicIdentity work owners log state)) :
    outcome.1.1 ∈ support work :=
  support_nested _ work (owners, log) state outcome reached

/-- Every outcome of the logged command program carries a result of the logged-source program. -/
theorem commands_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) (outcome : Outcome KemSK Result)
    (reached : outcome ∈ support (commands setup codec checks identityIndex publicIdentity work owners log state)) :
    outcome.1.1 ∈ support work := by
  rw [commands, support_map] at reached
  obtain ⟨full, fullReached, rfl⟩ := reached
  exact run_support setup codec checks identityIndex publicIdentity work owners log state full fullReached

/-- The interpreted logged steps before encapsulation issue no exposed encapsulation request, for every consumed set and every reply. -/
theorem beforeLogged_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (value : Verified Reader) (consumed : List Pqxdh.Bytes) :
    ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
      (PqxdhDeploymentLaterServerSource.beforeLogged value)).run consumed).IsQueryBoundP
      (PqxdhRegistrationJointKemExposedCounts.IsEncapsulation (KemSK := KemSK)) 0 := by
  have free := before_free setup codec checks identityIndex raw value consumed
  rw [← PqxdhDeploymentLaterServerSource.beforeLogged_fst, simulateQ_map, StateT.run_map, isQueryBoundP_map_iff]
    at free
  exact free

/-- The KEM cut of the exposed logged collector of one raw accept. The attached verification is pure; a rejected verification completes with no logged scalar and a rejection before encapsulation completes with the entry of the logged steps before encapsulation; otherwise the cut is the encapsulation of the verified PQ key, and the saved continuation is the literal suffix followed by logging the ephemeral generated before the cut, an explicit value. -/
theorem ordered_cut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    PqxdhRegistrationJointKemCut.scan setup ((ordered setup codec checks identityIndex raw).run consumed) 0 =
      match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
      | none => pure (.complete ((none, none), consumed))
      | some value => simulateQ (actual setup)
          ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
            (PqxdhDeploymentLaterServerSource.beforeLogged value)).run consumed) >>= fun prepared =>
          match prepared.1.1 with
          | none => pure (.complete ((none, prepared.1.2), prepared.2))
          | some ephemeral => pure (.pending (raw, value.keys.pqKey) fun reply =>
              (fun input => ((input.1, some ephemeral.secret), input.2)) <$>
                (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw value
                  ephemeral reply).run prepared.2) := by
  rw [PqxdhDeploymentLaterServerCommands.ordered_split]
  simp only [StateT.run_bind]
  rw [← PqxdhRegistrationJointAcceptKemCut.handler_eq, PqxdhRegistrationJointCutVerification.verified_pure, pure_bind,
    PqxdhRegistrationJointAcceptKemCut.handler_eq]
  generalize PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = verified
  cases verified with
  | none => rfl
  | some value =>
    dsimp only
    conv_lhs => rw [StateT.run_bind, ← free_hide setup _ (beforeLogged_free setup codec checks identityIndex raw value
      consumed), hide, scan_free_bind]
    apply bind_congr
    intro prepared
    rcases prepared with ⟨⟨_ | ephemeral, entry⟩, after⟩
    · rfl
    · have cut := PqxdhRegistrationJointKemSourceSuffix.suffix_cut setup codec checks identityIndex raw value
        ephemeral after (fun input => pure ((input.1, some ephemeral.secret), input.2))
      simpa only [StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, Function.comp_def] using cut

/-- A completed KEM cut of the exposed logged collector is a rejection: its collected input is `none`. -/
theorem ordered_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (collected : (Option (Inputs Reader ScalarBytes Word32) × Option ScalarBytes) × List Pqxdh.Bytes)
    (reached : .complete collected ∈ support (PqxdhRegistrationJointKemCut.scan setup
      ((ordered setup codec checks identityIndex raw).run consumed) 0)) :
    collected.1.1 = none := by
  rw [ordered_cut] at reached
  generalize PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = verified at reached
  cases verified with
  | none =>
    obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj (OracleComp.eq_of_mem_support_pure _ reached)
    rfl
  | some value =>
    rw [mem_support_bind_iff] at reached
    obtain ⟨⟨⟨_ | ephemeral, entry⟩, after⟩, _, reached⟩ := reached
    · obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj (OracleComp.eq_of_mem_support_pure _ reached)
      rfl
    · simp at reached

/-- The KEM scan of the exposed logged accept followed by a continuation: the logged collector is scanned first; a completed collector runs the accept tail and continues into the scan of the continuation, and an active collector saves the tail and the continuation behind its suffix. -/
theorem accept_scan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK)
    (next : (Option Nat × Option ScalarBytes) × NativeState KemSK →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Next) :
    PqxdhRegistrationJointKemCut.scan setup
      ((accept setup codec checks identityIndex publicIdentity raw).run state >>= next) 0 =
      PqxdhRegistrationJointKemCut.scan setup
        ((ordered setup codec checks identityIndex raw).run state.2.server.consumed) 0 >>= fun cut => match cut with
        | .complete collected => (PqxdhRegistrationJointOpenBackend.native
            (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 (collected.1.1, collected.2))).run
              state >>= fun answer => PqxdhRegistrationJointKemCut.scan setup (next ((answer.1, collected.1.2), answer.2)) 0
        | .pending request resume => pure (.pending request fun reply => resume reply >>= fun collected =>
            (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
              (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 (collected.1.1, collected.2)))).run
                state >>= fun answer => next ((answer.1, collected.1.2), answer.2)) := by
  rw [PqxdhDeploymentLaterServerCommands.accept_ordered]
  simp only [bind_assoc, pure_bind]
  rw [scan_bind_zero]
  apply bind_congr
  intro cut
  cases cut with
  | complete collected =>
    exact scan_free_bind setup _ (fun answer : Option Nat × NativeState KemSK => next ((answer.1, collected.1.2), answer.2)) 0
  | pending request resume => rfl

/-- The KEM scan of `exposeAt` runs the hidden logged prefix up to the selected raw accept and then scans that accept with its hidden continuation. -/
theorem exposeAt_scan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state) 0 =
      simulateQ (actual setup) (run setup codec checks identityIndex publicIdentity (scan work index) owners log state) >>=
        fun reached => match reached.1.1 with
        | .complete result => pure (.complete ((observe (result, none), reached.1.2.1), reached.2))
        | .pending raw next => PqxdhRegistrationJointKemCut.scan setup
            ((accept setup codec checks identityIndex publicIdentity raw).run reached.2 >>= fun answer =>
              hide setup (commands setup codec checks identityIndex publicIdentity
                (tagged observe raw next answer.1.1) reached.1.2.1 (reached.1.2.2 ++ [answer.1.2]) answer.2)) 0 := by
  rw [exposeAt, hide, scan_free_bind]
  apply bind_congr
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut <;> rfl

/-- An active KEM cut of the logged `exposeAt` is the encapsulation of the selected raw accept: the raw bytes are those of a reached pending raw-accept cut of the logged program, their attached verification succeeds with `value`, the request is the raw bytes with the verified PQ key, and the saved continuation is `rawResume`, which carries the selected accept's ephemeral and the log at the cut as explicit values. -/
theorem rawCut_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) (request : PqxdhRegistrationJointKemCut.Request)
    (resume : PqxdhRegistrationJointKemCut.Reply →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R))
    (reached : .pending request resume ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state) 0)) :
    ∃ raw next value ephemeral consumed native after logAt,
      Cut.pending raw next ∈ support (scan work index) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      request = (raw, value.keys.pqKey) ∧
      resume = rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
        after logAt next := by
  rw [exposeAt_scan, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨cut, after, logAt⟩, native⟩, prefixReached, reached⟩ := reached
  cases cut with
  | complete result => simp at reached
  | pending raw next =>
    have source := run_support setup codec checks identityIndex publicIdentity _ owners log state _
      (support_simulate _ _ _ prefixReached)
    dsimp only at reached
    rw [accept_scan, mem_support_bind_iff] at reached
    obtain ⟨cut, collectorReached, reached⟩ := reached
    cases cut with
    | complete collected =>
      rw [mem_support_bind_iff] at reached
      obtain ⟨answer, _, reached⟩ := reached
      rw [scan_hide] at reached
      simp at reached
    | pending request' resume' =>
      simp only [support_pure, Set.mem_singleton_iff, PqxdhRegistrationJointKemCut.Cut.pending.injEq] at reached
      obtain ⟨rfl, rfl⟩ := reached
      rw [ordered_cut] at collectorReached
      cases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
      | none =>
        rw [verified] at collectorReached
        simp at collectorReached
      | some value =>
        rw [verified, mem_support_bind_iff] at collectorReached
        obtain ⟨⟨_ | ephemeral, consumed⟩, _, collectorReached⟩ := collectorReached
        · simp at collectorReached
        · simp only [support_pure, Set.mem_singleton_iff, PqxdhRegistrationJointKemCut.Cut.pending.injEq] at collectorReached
          obtain ⟨rfl, rfl⟩ := collectorReached
          refine ⟨raw, next, value, ephemeral, consumed, native, after, logAt, source, verified, rfl, ?_⟩
          funext reply
          simp only [rawResume, bind_map_left]

/-- Every completed KEM cut of the logged `exposeAt` has an outcome whose tag is not accepted: completion before the selected accept gives the tag `none`, and a rejection before encapsulation gives an accept reply `none`. -/
theorem accepted_reached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) (outcome : Outcome KemSK R)
    (reached : .complete outcome ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state) 0)) :
    ∃ result tag, outcome.1.1 = observe (result, tag) ∧ accepted tag = false := by
  rw [exposeAt_scan, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨cut, after, logAt⟩, native⟩, _, reached⟩ := reached
  cases cut with
  | complete result =>
    obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj (OracleComp.eq_of_mem_support_pure _ reached)
    exact ⟨result, none, rfl, rfl⟩
  | pending raw next =>
    dsimp only at reached
    rw [accept_scan, mem_support_bind_iff] at reached
    obtain ⟨cut, collectorReached, reached⟩ := reached
    cases cut with
    | complete collected =>
      rw [mem_support_bind_iff] at reached
      obtain ⟨answer, tailReached, reached⟩ := reached
      rw [scan_hide, support_map] at reached
      obtain ⟨final, finalReached, same⟩ := reached
      obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj same
      have rejected := ordered_complete setup codec checks identityIndex raw _ collected collectorReached
      obtain ⟨⟨none', logged⟩, consumed⟩ := collected
      dsimp only at rejected
      subst rejected
      have noSession := tail_none setup publicIdentity native.2 consumed native answer tailReached
      have client := commands_support setup codec checks identityIndex publicIdentity _ _ _ _ _
        (support_simulate _ _ _ finalReached)
      rw [tagged, noSession, support_map] at client
      obtain ⟨result, _, same⟩ := client
      exact ⟨result, some (raw, none), same.symm, rfl⟩
    | pending request resume => simp at reached

/-- One logged raw accept of the command handler: the exposed logged accept, with its entry appended to the log and the owners kept. -/
theorem impl_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (owners : List EncodedEntry)
    (log : Log) (state : NativeState KemSK) :
    ((PqxdhDeploymentLaterServerCommands.impl setup codec checks identityIndex publicIdentity
      (.inl (.inl (.inr (.accept raw))))).run (owners, log)).run state =
      (fun answer => ((answer.1.1, (owners, log ++ [answer.1.2])), answer.2)) <$>
        (accept setup codec checks identityIndex publicIdentity raw).run state := by
  change (((fun answer : Option Nat × Option ScalarBytes => (answer.1, (owners, log ++ [answer.2]))) <$>
    accept setup codec checks identityIndex publicIdentity raw).run state) = _
  rw [StateT.run_map]

/-- At a pending raw cut, the logged command program of the recording finish runs the exposed logged accept, appends its entry to the log and continues with the tagged continuation. -/
theorem pending_commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (Spec KemSK) X) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity
      (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (.pending raw next)) owners log state =
      ((accept setup codec checks identityIndex publicIdentity raw).run state >>= fun answer =>
        commands setup codec checks identityIndex publicIdentity (tagged observe raw next answer.1.1) owners
          (log ++ [answer.1.2]) answer.2) := by
  simp only [PqxdhDeploymentLaterServerCommands.tagFinish, map_bind, Functor.map_map, commands,
    PqxdhDeploymentLaterServerCommands.run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [impl_accept, bind_map_left]
  rfl

/-- Interpreting the logged `exposeAt` by the actual encapsulator is interpreting the logged command program of the tagged logged program. -/
theorem exposeAt_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    simulateQ (actual setup) (exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state) =
      simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity
        (observe <$> tag work index) owners log state) := by
  rw [tag, map_bind, commands, PqxdhDeploymentLaterServerCommands.run_bind, map_bind]
  simp only [exposeAt, simulateQ_bind, actual_hide]
  apply bind_congr
  rintro ⟨⟨cut, after, logAt⟩, native⟩
  cases cut with
  | complete result =>
    simp [PqxdhDeploymentLaterServerCommands.tagFinish, PqxdhDeploymentLaterServerCommands.run]
  | pending raw next =>
    dsimp only
    rw [show ((fun result => ((result.1.1, result.1.2.1), result.2)) <$>
        PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
          (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (Cut.pending raw next)) after logAt native) =
        commands setup codec checks identityIndex publicIdentity
          (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (Cut.pending raw next)) after logAt native from rfl,
      pending_commands]
    simp only [simulateQ_bind, actual_hide]

/-- The candidate-free opaque resumption of an active logged cut after a challenge ciphertext: `KemOpaqueResume.resume` with the challenge marker under the private client interpreter, followed by the rest of the tagged logged program from the log extended by the explicit ephemeral. -/
noncomputable def opaqueResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : Verified Reader) (ephemeral : Ephemeral ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (Spec KemSK) X) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let answer ← (simulateQ (PqxdhRegistrationJointKemOpaqueResume.liftImpl PqxdhRegistrationJointKemOpaqueResume.clientNative
      setup native.2.sessions candidate PqxdhRegistrationJointKemOpaqueResume.forwardClient)
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run native
  hide setup (commands setup codec checks identityIndex publicIdentity (tagged observe raw next answer.1) owners
    (log ++ [some ephemeral.secret]) answer.2)

/-- The core of T6 for the logged source: fed the ordinary challenge reply, the saved continuation of an active logged cut is the opaque resumption, in which the candidate is only an argument of the private client interpreter. The logged entry is the explicit ephemeral, so the existing `KemOpaqueResume.resume_reply` applies with the logged rest. -/
theorem rawResume_opaque (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : Verified Reader) (ephemeral : Ephemeral ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (Spec KemSK) X) (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners log next
      (PqxdhRegistrationJointKemResume.reply ciphertext candidate) =
      opaqueResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners log
        next ciphertext candidate :=
  PqxdhRegistrationJointKemOpaqueResume.resume_reply setup codec checks identityIndex publicIdentity raw value
    ephemeral ciphertext candidate native.2 consumed native
    (fun answer => hide setup (commands setup codec checks identityIndex publicIdentity
      (tagged observe raw next answer.1) owners (log ++ [some ephemeral.secret]) answer.2))

/-- The scanned program of the logged source for the KEM games: the KEM scan at occurrence zero of the logged `exposeAt` on the decision-tagged program, over the actual initialized Server, from no owner and the empty log. -/
noncomputable def scanned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index : Nat) :
    PqxdhDeploymentLaterServerKemHop.Scanned KemSK := fun created =>
  PqxdhRegistrationJointKemCut.scan setup
    (exposeAt setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
      (decideTag decision) work index [] [] (PqxdhRegistrationJointInitializedAccept.initial created)) 0

/-- The KEM hop for the logged source, by instantiation of the generic hop: the real game of the logged exposure wins with at most the probability of its KEM-ideal branch plus one ordinary one-key ML-KEM IND-CCA advantage of the proof-carrying adversary and one ordinary ML-KEM correctness error. -/
theorem kem_hop (setup : Setup baseSpec KemSK)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (codec : Codec Reader Response) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
        (scanned setup codec checks decision work index) runtime count selected] {true} ≤
      𝒟[PqxdhDeploymentLaterServerKemHop.branch setup ensureInit supplied
        (scanned setup codec checks decision work index) runtime count selected false] {true} +
        ENNReal.ofReal (setup.kem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl))
          (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit supplied
            (scanned setup codec checks decision work index) runtime count selected).toINDCCA +
          PqxdhRegistrationJointKemRawGame.correctnessError setup) :=
  PqxdhDeploymentLaterServerKemHop.real_le_ideal setup functional ensureInit supplied
    (scanned setup codec checks decision work index) runtime count selected

set_option linter.deprecated false in
/-- The selected-first reservation for the hidden logged command program, by instantiation of the generic `PqxdhDynamicKemJointSource.selected_source`; the creation cap is the premise `room`. -/
theorem selected_first (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK)
    (joint : PqxdhDynamicIdentityPool.SourceState) (count : Nat) (selected : Fin (count + 1))
    (room : (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
      state)).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) (count + 1)) :
    𝒮[(fun result => (some result.1, result.2)) <$>
      (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log state))).run
          (joint, PqxdhLiveKemBirth.empty)] =
      𝒮[do
        let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
        let others ← PqxdhLiveKemSelection.sampleFamily
          (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
        let pairs := List.ofFn (selected.insertNth chosen others)
        Prod.map id (PqxdhDynamicKemJointSource.project pairs) <$>
          (((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected.val pairs)
            (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
              state))).run).run (joint, PqxdhDynamicKemRouter.empty))] :=
  PqxdhDynamicKemJointSource.selected_source setup.baseImpl setup.joint setup.kem _ count selected room joint

set_option linter.deprecated false in
/-- The selected-disclosure monitor for the hidden logged command program, by instantiation of the generic `PqxdhDynamicKemJointStopping.history_event`. -/
theorem monitor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (owners : List EncodedEntry) (log : Log) (native : NativeState KemSK) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (state : PqxdhDynamicKemJointSource.State KemSK)
    (tracked : PqxdhDynamicKemJointStopping.Tracked selected state)
    (event : Option (Outcome KemSK Result) × PqxdhDynamicKemJointSource.State KemSK → Prop) :
    probEvent ((simulateQ (PqxdhDynamicKemJointSource.normal setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
          native))).run.run state)
        (fun result => event result ∧ result.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false) =
      probEvent ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity work owners log
          native))).run.run state)
        (fun result => event result ∧ PqxdhDynamicKemJointStopping.Good result.2) :=
  PqxdhDynamicKemJointStopping.history_event setup.baseImpl setup.joint setup.kem selected pairs _ state tracked event

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.support_nested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.support_nested

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.run_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.run_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.commands_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.commands_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.beforeLogged_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.beforeLogged_free

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.ordered_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.ordered_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.ordered_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.ordered_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.accept_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.accept_scan

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.exposeAt_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.exposeAt_scan

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.rawCut_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.rawCut_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.accepted_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.accepted_reached

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.impl_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.impl_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.pending_commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.pending_commands

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.exposeAt_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.exposeAt_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.rawResume_opaque' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.rawResume_opaque

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.kem_hop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.kem_hop

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.selected_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.selected_first

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerCut.monitor
