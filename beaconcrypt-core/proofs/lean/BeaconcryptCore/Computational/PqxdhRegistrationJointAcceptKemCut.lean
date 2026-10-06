-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutTag
import BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptCutSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointCutVerification
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemSourceSuffix

/-! Expose only the encapsulation of the selected raw accept. Every other encapsulation of the actual source command compiler is interpreted in place by the actual source encapsulator, so the KEM cut at occurrence zero of this program is the encapsulation of the raw accept at the designated raw-accept ordinal, when that accept reaches encapsulation. The raw-accept ordinal counts every raw accept, including rejected ones, and differs from the encapsulation ordinal of `PqxdhRegistrationJointKemCut`. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (forward actual commands)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemExposedCounts (IsEncapsulation)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X R Result Next : Type}

/-- Interpret every exposed encapsulation of a program by the actual source encapsulator, leaving the program over the exposed interface with no exposed request. -/
noncomputable def hide (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result :=
  simulateQ forward (simulateQ (actual setup) work)

/-- The source continuation after the selected accept, whose result records the selected raw bytes and the public reply of that accept. -/
noncomputable def tagged (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (answer : Option Nat) :
    OracleComp (SourceSpec KemSK) R :=
  (fun result => observe (result, some (raw, answer))) <$> next answer

/-- The actual source command compiler on the tagged client `observe <$> AcceptCutTag.tag work index`, with only the encapsulation of the raw accept at ordinal `index` exposed. Earlier and later encapsulations, all private services, owners and native state are those of the actual source. A client that completes before that accept returns the fallback tag `none`. -/
noncomputable def exposeAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let reached ← hide setup (commands setup codec checks identityIndex publicIdentity
    (PqxdhRegistrationJointAcceptCut.scan work index) owners state)
  match reached.1.1 with
  | .complete result => pure ((observe (result, none), reached.1.2), reached.2)
  | .pending raw next => do
    let answer ← (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex
      publicIdentity raw).run reached.2
    hide setup (commands setup codec checks identityIndex publicIdentity
      (tagged observe raw next answer.1) reached.1.2 answer.2)

/-- The saved continuation of an active KEM cut of `exposeAt`: the literal interpreted source suffix after the encapsulation reply, the unchanged allocation/root/consumption/publication tail of the accept, and the rest of the tagged client with every later encapsulation interpreted in place. -/
noncomputable def rawResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (state : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (reply : PqxdhRegistrationJointKemCut.Reply) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let input ← (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw value
    ephemeral reply).run consumed
  let answer ← (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
    (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 input))).run state
  hide setup (commands setup codec checks identityIndex publicIdentity
    (tagged observe raw next answer.1) owners answer.2)

/-- The verification step of the exposed collector and of the ported source suffix is the same handler. -/
theorem handler_eq (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) :
    PqxdhRegistrationJointCutVerification.handler setup codec checks identityIndex raw =
      PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw := rfl

/-- Interpreting a hidden program by the actual encapsulator is interpreting the original program. -/
theorem actual_hide (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    simulateQ (actual setup) (hide setup work) = simulateQ (actual setup) work :=
  PqxdhRegistrationJointKemEncapsulation.forward_actual setup _

/-- A program with no exposed encapsulation request is unchanged by hiding. -/
theorem free_hide (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
    (free : work.IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) 0) : hide setup work = work := by
  induction work using OracleComp.inductionOn with
  | pure result => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at free
    cases query with
    | inl query =>
      simp only [hide, simulateQ_bind, simulateQ_spec_query, actual] at ih ⊢
      exact bind_congr fun answer => ih answer (by simpa [IsEncapsulation] using free.2 answer)
    | inr request => simp [IsEncapsulation] at free

/-- A prefix without exposed requests steps through the KEM scan unchanged, at every occurrence. -/
theorem scan_free_bind (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result)
    (next : Result → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Next) (index : Nat) :
    PqxdhRegistrationJointKemCut.scan setup (simulateQ forward work >>= next) index =
      work >>= fun result => PqxdhRegistrationJointKemCut.scan setup (next result) index := by
  induction work using OracleComp.inductionOn with
  | pure result => simp
  | query_bind query cont ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, bind_assoc]
    exact (PqxdhRegistrationJointKemCut.scan_other setup query _ index).trans (bind_congr ih)

/-- The KEM scan at occurrence zero of a sequential program scans the first part, and either continues into the second part or saves the second part behind the first part's saved continuation. -/
theorem scan_bind_zero (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result)
    (next : Result → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Next) :
    PqxdhRegistrationJointKemCut.scan setup (work >>= next) 0 =
      PqxdhRegistrationJointKemCut.scan setup work 0 >>= fun cut => match cut with
        | .complete result => PqxdhRegistrationJointKemCut.scan setup (next result) 0
        | .pending request resume => pure (.pending request fun reply => resume reply >>= next) := by
  induction work using OracleComp.inductionOn with
  | pure result => simp; rfl
  | query_bind query cont ih =>
    cases query with
    | inl query =>
      rw [bind_assoc, PqxdhRegistrationJointKemCut.scan_other, PqxdhRegistrationJointKemCut.scan_other, bind_assoc]
      exact bind_congr ih
    | inr request =>
      rw [bind_assoc, PqxdhRegistrationJointKemCut.scan_target, PqxdhRegistrationJointKemCut.scan_target, pure_bind]
      rfl


/-- Any oracle interpretation only removes results of an oracle program. -/
theorem support_simulate {κ κ' : Type} {spec : OracleSpec κ} {target : OracleSpec κ'}
    (impl : QueryImpl spec (OracleComp target)) (work : OracleComp spec Result) (result : Result)
    (reached : result ∈ support (simulateQ impl work)) : result ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa using reached
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
    obtain ⟨answer, _, reached⟩ := reached
    exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query query answer, ih answer reached⟩

/-- Every outcome of the exposed command compiler carries a result of the original client program. -/
theorem commands_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (SourceSpec KemSK) Result)
    (owners : List EncodedEntry) (state : NativeState KemSK) (outcome : Outcome KemSK Result)
    (reached : outcome ∈ support (commands setup codec checks identityIndex publicIdentity work owners state)) :
    outcome.1.1 ∈ support work := by
  have client : outcome.1 ∈ support
      ((simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) work).run owners) := by
    apply support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity) _ state
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ reached
  apply support_simulateQ_run'_subset (PqxdhRegistrationJointRevealSchedule.client setup codec) work owners
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ client

/-- A hidden program issues no exposed encapsulation request. -/
theorem hide_free (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) :
    (hide setup work).IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) 0 :=
  PqxdhRegistrationJointKemExposedCounts.forward_bound _ _ 0 (isQueryBoundP_false _ 0)

/-- Scanning a hidden program completes with the actual interpretation of the program. -/
theorem scan_hide (setup : Setup baseSpec KemSK)
    (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Result) (index : Nat) :
    PqxdhRegistrationJointKemCut.scan setup (hide setup work) index =
      (fun result => .complete result) <$> simulateQ (actual setup) work := by
  rw [← bind_pure (hide setup work), hide, scan_free_bind, map_eq_bind_pure_comp]
  rfl

/-- The source steps before encapsulation (freshness, reservation, both point parsers, ephemeral generation and KEM parsing) contain no encapsulation callback. -/
theorem before_callbacks {E Shared : Type} (verified : PqxdhServerRootPreparation.Verified Reader) :
    (PqxdhRegistrationJointKemCollected.beforeEncapsulation (E := E) (Shared := Shared) verified).IsQueryBoundP
      (fun query => PqxdhServerAuthSourceCosts.serverClass query = .encapsulate) 0 := by
  unfold PqxdhRegistrationJointKemCollected.beforeEncapsulation
  simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [PqxdhServerAuthSourceCosts.serverClass], ?_⟩)
    | (fail_if_no_progress simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left,
        Option.elim_some, OptionT.run_mk, PqxdhServerAuthSourceCosts.serverClass,
        Bool.not_true, Bool.false_eq_true, ite_false, reduceCtorEq])
    | intro answer; cases answer

set_option backward.isDefEq.respectTransparency false in
/-- The interpreted steps before encapsulation issue no exposed encapsulation request, for every consumed set and every reply. -/
theorem before_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (consumed : List Pqxdh.Bytes) :
    ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
      (PqxdhRegistrationJointKemCollected.beforeEncapsulation value)).run consumed).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) 0 := by
  rw [PqxdhRegistrationJointKemSourceSuffix.handler]
  exact (before_callbacks (E := PqxdhJointGapDh.ScalarBytes) (Shared := PqxdhBeaconPhase2Preparation.Word32) value).simulateQ_run_of_step
    (fun query counted state => by
      simpa only [QueryImpl.apply_compose, ite_eq_left counted] using
        PqxdhRegistrationJointKemExposedCounts.prefix_step setup codec checks identityIndex raw query state)
    (fun query excluded state => by
      simpa only [QueryImpl.apply_compose, ite_eq_right excluded] using
        PqxdhRegistrationJointKemExposedCounts.prefix_step setup codec checks identityIndex raw query state)
    consumed

/-- The KEM cut of the literal ordered collector of one raw accept. The attached verification is pure; a rejected verification or a rejection before encapsulation completes without an exposed request; otherwise the cut is the encapsulation of the verified PQ key with the literal interpreted source suffix saved. -/
theorem ordered_cut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    PqxdhRegistrationJointKemCut.scan setup
      ((PqxdhRegistrationJointKemSourceSuffix.ordered setup codec checks identityIndex raw).run consumed) 0 =
      match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
      | none => pure (.complete (none, consumed))
      | some value => simulateQ (actual setup)
          ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
            (PqxdhRegistrationJointKemCollected.beforeEncapsulation value)).run consumed) >>= fun prepared =>
          match prepared.1 with
          | none => pure (.complete (none, prepared.2))
          | some ephemeral => pure (.pending (raw, value.keys.pqKey) fun reply =>
              (PqxdhRegistrationJointKemSourceSuffix.suffix setup codec checks identityIndex raw value
                ephemeral reply).run prepared.2) := by
  simp only [PqxdhRegistrationJointKemSourceSuffix.ordered, StateT.run_bind]
  rw [← handler_eq, PqxdhRegistrationJointCutVerification.verified_pure, pure_bind, handler_eq]
  generalize PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = verified
  cases verified with
  | none => rfl
  | some value =>
    dsimp only
    conv_lhs => rw [StateT.run_bind, ← free_hide setup _ (before_free setup codec checks identityIndex raw value consumed),
      hide, scan_free_bind]
    apply bind_congr
    intro prepared
    rcases prepared with ⟨_ | ephemeral, after⟩
    · rfl
    · have cut := PqxdhRegistrationJointKemSourceSuffix.suffix_cut setup codec checks identityIndex raw value
        ephemeral after pure
      simp only [bind_pure] at cut
      simpa only [StateT.run_bind] using cut


/-- A completed KEM cut of the ordered collector is a rejection: its collected input is `none`. -/
theorem ordered_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes)
    (reached : .complete collected ∈ support (PqxdhRegistrationJointKemCut.scan setup
      ((PqxdhRegistrationJointKemSourceSuffix.ordered setup codec checks identityIndex raw).run consumed) 0)) :
    collected.1 = none := by
  rw [ordered_cut] at reached
  generalize PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = verified at reached
  cases verified with
  | none =>
    obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj (OracleComp.eq_of_mem_support_pure _ reached)
    rfl
  | some value =>
    rw [mem_support_bind_iff] at reached
    obtain ⟨⟨_ | ephemeral, after⟩, _, reached⟩ := reached
    · obtain rfl := PqxdhRegistrationJointKemCut.Cut.complete.inj (OracleComp.eq_of_mem_support_pure _ reached)
      rfl
    · simp at reached

/-- The accept tail on a rejected collection returns no session. -/
theorem tail_none (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (game : GameState KemSK) (consumed : List Pqxdh.Bytes) (state : NativeState KemSK)
    (answer : Option Nat × NativeState KemSK)
    (reached : answer ∈ support ((PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK)
      (PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup publicIdentity game (none, consumed))).run state)) :
    answer.1 = none := by
  simp only [PqxdhRegistrationJointOpenBackend.native, PqxdhRegistrationJointServerAccept.tail,
    PqxdhServerAuthNative.nativeSet, StateT.run, PqxdhLiveKemBirth.coins] at reached
  simp at reached
  rw [reached]

/-- The KEM scan of `exposeAt` runs the hidden source prefix up to the selected raw accept and then scans that accept with its hidden continuation. -/
theorem exposeAt_scan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0 =
      simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity
        (PqxdhRegistrationJointAcceptCut.scan work index) owners state) >>= fun reached =>
        match reached.1.1 with
        | .complete result => pure (.complete ((observe (result, none), reached.1.2), reached.2))
        | .pending raw next => PqxdhRegistrationJointKemCut.scan setup
            ((PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
              reached.2 >>= fun answer => hide setup (commands setup codec checks identityIndex publicIdentity
                (tagged observe raw next answer.1) reached.1.2 answer.2)) 0 := by
  rw [exposeAt, hide, scan_free_bind]
  apply bind_congr
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut <;> rfl

/-- The KEM scan of one exposed raw accept followed by a continuation: the ordered collector is scanned first; a completed collector runs the accept tail and continues into the scan of the continuation, and an active collector saves the tail and the continuation behind its suffix. -/
theorem accept_scan (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK)
    (next : Option Nat × NativeState KemSK → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) Next) :
    PqxdhRegistrationJointKemCut.scan setup
      ((PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
        state >>= next) 0 =
      PqxdhRegistrationJointKemCut.scan setup
        ((PqxdhRegistrationJointKemSourceSuffix.ordered setup codec checks identityIndex raw).run
          state.2.server.consumed) 0 >>= fun cut => match cut with
        | .complete collected => (PqxdhRegistrationJointOpenBackend.native
            (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 collected)).run state >>= fun answer =>
            PqxdhRegistrationJointKemCut.scan setup (next answer) 0
        | .pending request resume => pure (.pending request fun reply => resume reply >>= fun collected =>
            (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
              (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state.2 collected))).run state >>= next) := by
  rw [PqxdhRegistrationJointKemSourceSuffix.accept_ordered, bind_assoc, scan_bind_zero]
  apply bind_congr
  intro cut
  cases cut with
  | complete collected => exact scan_free_bind setup _ next 0
  | pending request resume => rfl


/-- Interpreting `exposeAt` by the actual encapsulator is interpreting the fully exposed command compiler on the tagged client `observe <$> AcceptCutTag.tag work index`. -/
theorem exposeAt_commands (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    simulateQ (actual setup) (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) =
      simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhRegistrationJointAcceptCutTag.tag work index) owners state) := by
  rw [PqxdhRegistrationJointAcceptCutTag.tag, map_bind, PqxdhRegistrationJointAcceptCutSource.commands_bind]
  simp only [exposeAt, simulateQ_bind, actual_hide]
  apply bind_congr
  rintro ⟨⟨cut, after⟩, native⟩
  cases cut with
  | complete result =>
    simp [PqxdhRegistrationJointAcceptCutTag.tagFinish, commands]
  | pending raw next =>
    have finish : observe <$> PqxdhRegistrationJointAcceptCutTag.tagFinish (.pending raw next) =
        PqxdhRegistrationJointAcceptCut.finish (.pending raw (tagged observe raw next)) := by
      simp only [PqxdhRegistrationJointAcceptCutTag.tagFinish, PqxdhRegistrationJointAcceptCut.finish,
        map_bind, Functor.map_map]
      rfl
    dsimp only
    rw [finish, PqxdhRegistrationJointAcceptCutSource.pending_command]
    simp only [simulateQ_bind, actual_hide]

/-- `exposeAt` is the actual initialized source command program of the tagged client once its single exposed encapsulation is interpreted by the actual encapsulator. -/
theorem exposeAt_actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    simulateQ (actual setup) (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) =
      PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhRegistrationJointAcceptCutTag.tag work index) owners state :=
  (exposeAt_commands setup codec checks identityIndex publicIdentity observe work index owners state).trans
    (PqxdhRegistrationJointKemEncapsulation.commands_actual setup codec checks identityIndex publicIdentity _ owners state)

/-- Scanning `exposeAt` at occurrence zero and finishing with the actual encapsulator restores the actual source program of the tagged client. -/
theorem rawCut_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0 >>=
        PqxdhRegistrationJointKemCut.finish setup) =
      PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhRegistrationJointAcceptCutTag.tag work index) owners state := by
  rw [PqxdhRegistrationJointKemCut.scan_finish, exposeAt_actual]

/-- `exposeAt` issues at most one exposed encapsulation request on every path, for every reply. -/
theorem exposeAt_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) :
    (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state).IsQueryBoundP
      (IsEncapsulation (KemSK := KemSK)) 1 := by
  unfold exposeAt
  rw [← Nat.zero_add 1]
  apply isQueryBoundP_bind (hide_free setup _)
  rintro ⟨⟨cut, after⟩, native⟩ _
  cases cut with
  | complete result => trivial
  | pending raw next =>
    rw [← Nat.add_zero 1]
    exact isQueryBoundP_bind (PqxdhRegistrationJointKemExposedCounts.accept_bound setup codec checks identityIndex
      publicIdentity raw native) (fun answer _ => hide_free setup _)

/-- An active KEM cut of `exposeAt` is the encapsulation of the selected raw accept: the raw bytes are those of a reached pending raw-accept cut, the attached verification of those bytes succeeds with `value`, the request is the raw bytes with the verified PQ key, and the saved continuation is `rawResume`. -/
theorem rawCut_shape (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK)
    (request : PqxdhRegistrationJointKemCut.Request)
    (resume : PqxdhRegistrationJointKemCut.Reply →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R))
    (reached : .pending request resume ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0)) :
    ∃ raw next value ephemeral consumed native after,
      PqxdhRegistrationJointAcceptCut.Cut.pending raw next ∈ support (PqxdhRegistrationJointAcceptCut.scan work index) ∧
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
      request = (raw, value.keys.pqKey) ∧
      resume = rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
        after next := by
  rw [exposeAt_scan, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨cut, after⟩, native⟩, prefixReached, reached⟩ := reached
  cases cut with
  | complete result => simp at reached
  | pending raw next =>
    have source := commands_support setup codec checks identityIndex publicIdentity _ owners state _
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
          refine ⟨raw, next, value, ephemeral, consumed, native, after, source, verified, rfl, ?_⟩
          funext reply
          simp only [rawResume]

/-- A completed KEM cut of `exposeAt` has a rejected selected accept: its result is `observe (result, tag)` for a tag whose accept did not return a session. This covers completion before the selected accept, a rejected attached verification, and every rejection between verification and encapsulation. -/
theorem accepted_reached (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) (outcome : Outcome KemSK R)
    (reached : .complete outcome ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity observe work index owners state) 0)) :
    ∃ result tag, outcome.1.1 = observe (result, tag) ∧ PqxdhRegistrationJointAcceptCutTag.accepted tag = false := by
  rw [exposeAt_scan, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨cut, after⟩, native⟩, _, reached⟩ := reached
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
      obtain ⟨none', consumed⟩ := collected
      simp only at rejected
      subst rejected
      have noSession := tail_none setup publicIdentity native.2 consumed native answer tailReached
      have client := commands_support setup codec checks identityIndex publicIdentity _ _ _ _
        (support_simulate _ _ _ finalReached)
      rw [tagged, noSession, support_map] at client
      obtain ⟨result, _, same⟩ := client
      exact ⟨result, some (raw, none), same.symm, rfl⟩
    | pending request resume => simp at reached

end BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.handler_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.handler_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.actual_hide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.actual_hide

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.free_hide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.free_hide

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_free_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_free_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_bind_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_bind_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.support_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.support_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.commands_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.commands_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.hide_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.hide_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_hide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.scan_hide

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.before_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.before_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.before_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.before_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.ordered_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.ordered_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.ordered_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.ordered_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.tail_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.tail_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_scan

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.accept_scan' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.accept_scan

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_commands

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_actual

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.rawCut_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.rawCut_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.exposeAt_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.rawCut_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.rawCut_shape

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.accepted_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointAcceptKemCut.accepted_reached
