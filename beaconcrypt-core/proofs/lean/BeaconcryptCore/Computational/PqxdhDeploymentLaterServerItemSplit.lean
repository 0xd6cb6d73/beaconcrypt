-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared

/-! LQ-F upstream, unit A1: stage S1c of item 2 over the logged source (LQ-F upstream design-v2, section 4.3, module `…ItemSplit`). The main theorem `opaqueBranchL_split` instantiates G1 (`PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`) on the logged prefix and client of stage S1b at coefficient one:

```text
(opaqueBranch … false).boolDistAdvantage (splitGame (sharedStartL …) (sharedClientL …)) ≤ (qAccept + qFinish + qHmac) / 2^256
```

The premise is the logged source budget `certified`: caps per source14 kind through `PqxdhDeploymentLaterServerReserve.laterKind`; the Server read has kind `none`, reads no table and needs no cap. The compiled LQ-F program `PqxdhDeploymentLaterServerCompile.compileServer` meets this premise at the transported caps `PqxdhDeploymentLaterServerCompileBudget.laterTransported bounds budget post` (`PqxdhDeploymentLaterServerCompileBudget.compile_server_certified`), whose HMAC cap `qHmac + qHmac₂` adds the post phase's HMAC budget to the run's; at these caps the three caps of the bound add up to `qAccept + qFinish + (qHmac + qHmac₂)` (`PqxdhDeploymentLaterServerItemTargets.later_guess_term`), so post-run HMAC queries enter the guessing term with coefficient one.

The budget split is the classical one with one more request on each side. Before the cut, the logged accept adds at most one key to the table cache (`acceptL_grows`, from `impl_grows` along `accept_fst`), every logged-source request makes at most one native table request, and only if it is a table request of the logged source (`client_boundL`; the Server read makes none), and the potential moves with the remaining budget along the logged scan (`scanL_potential`, `commandsL_cut`); `opaqueScanL_fits`, `sourcePreOpaqueL_fits` and `sharedStartL_fits` follow. After the cut, the logged accept step of the skeleton makes at most one table read (`skelImplL_reads`) and every logged-source request at most one table request of the logged grouped interface (`groupedClientL_bound`), so the client makes at most `1 + (Q - c - 1)` direct reads (`skelResumeL_reads`, `postSkelL_direct`, `sharedClientL_direct`). For the post-run HMAC queries of the compiled LQ-F program, three cases arise. (a) The selected accept is active and its KEM key is the challenger's: the post phase runs after the cut, and each of its HMAC queries makes at most one direct read of G1's client, counted among these reads by `groupedClientL_bound` against the continuation's budget. (b) The selected accept is active with another KEM key: `postSkelL` returns `false` at once, so the branch runs no continuation, the post phase included, and its client makes no read. (c) The selected accept is never reached, or it rejects before encapsulation: the logged scan completes the whole program inside the prefix (its run, its terminal reads, the Server read and the post phase); the context is then inactive, its cache component is empty and its client makes no read (`sharedClientL_inactive`), so the charge for that prefix outcome (its cache keys plus its client's direct reads) is zero; the bound stays the uniform `Q / 2^256`.

R1 caveat (LQ-F upstream design-v2, section 5): the step is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1). In LQ-F the post-run adversary knows every revealed Beacon secret, the Server seed and every generated ephemeral, hence both hidden entries' 128-byte DH coordinates `m` exactly; each hidden entry is the R1 table at `padFF32 ‖ m ‖ u` with only the shared 32-byte ML-KEM output `u` unknown. G1's bound fixes only the 32-byte suffix and holds for every client, whatever the client knows about `m`, so the term is unchanged. But the unpredictability of the entries given `m` and their mutual independence rest on R1 alone: classically `m` also contains honest-honest DH values the adversary cannot compute (item 2 never uses them), and in LQ-F no such second line of defence exists. The premises (R1 and the logged `certified`) are those of the classical stage S1c; no assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRomSplit (TableKind NativeKind keyCount Grows impl_grows client_bound potential_run
  compose compose_run cacheKeys cacheKeys_empty initial_keys support_option simulate_free query_free query_one keys
  keys_cover keys_card tableBudget isQueryBoundP_or tableRead? directRead? direct_table fwd_reads fwdOption_reads
  ReadsC readsC_liftT readsN_acceptTail groupKind skelImpl_reads groupedClient_bound resume_root resumeImpl_reads
  tableKind_source)
open PqxdhRegistrationJointKemPostSkeleton (GSpec Services encLift compileHidden)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerCommands (Local)
open PqxdhDeploymentLaterServerItemTargets (GSpecL acceptStepL skelImplL groupedClientL skelResumeL postSkelL cacheOfL
  sharedStartL sharedClientL)
open PqxdhDeploymentLaterServerItemFree (SpecL clientL logClient implL run_clientL)
open PqxdhDeploymentLaterServerItemShared (groupedClientL_log)

/-! ### Table requests of the logged source -/

section Kinds

variable {KemSK Response : Type}

/-- The logged-source requests that read the shared table: raw accepts, Beacon finishes and public HMAC. The Server read reads no table. -/
def TableKindL : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop
  | .inl query => TableKind (KemSK := KemSK) query
  | .inr _ => False

instance : DecidablePred (TableKindL (KemSK := KemSK))
  | .inl query => inferInstanceAs (Decidable (TableKind (KemSK := KemSK) query))
  | .inr _ => inferInstanceAs (Decidable False)

/-- The native requests of the logged source client that read the shared table: those of the source client, and the logged accept. -/
def NativeKindL : (SpecL KemSK Response).Domain → Prop
  | .inl query => NativeKind (KemSK := KemSK) (Response := Response) query
  | .inr _ => True

instance : DecidablePred (NativeKindL (KemSK := KemSK) (Response := Response))
  | .inl query => inferInstanceAs (Decidable (NativeKind (KemSK := KemSK) (Response := Response) query))
  | .inr _ => inferInstanceAs (Decidable True)

/-- A table request of the logged source has the source kind of a raw accept, a Beacon finish or a public HMAC. -/
theorem tableKindL_later (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (table : TableKindL query) :
    (PqxdhDeploymentLaterServerReserve.laterKind query = some (.inl 3) ∨
      PqxdhDeploymentLaterServerReserve.laterKind query = some (.inl 5)) ∨
      PqxdhDeploymentLaterServerReserve.laterKind query = some (.inl 6) := by
  rcases query with query | later
  · simpa [PqxdhDeploymentLaterServerReserve.laterKind] using tableKind_source query table
  · exact table.elim

/-- The logged source budget bounds the table requests of the logged-source program. -/
theorem certified_tableL {X : Type} (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind)) :
    work.IsQueryBoundP (TableKindL (KemSK := KemSK)) (tableBudget budget) :=
  IsQueryBoundP.of_imp tableKindL_later
    (isQueryBoundP_or work (isQueryBoundP_or work (certified (.inl 3)) (certified (.inl 5))) (certified (.inl 6)))

end Kinds

/-! ### The cut-split along the logged scan -/

section Scan

open PqxdhDeploymentLaterServerSource (Spec)
open PqxdhDeploymentLaterServerCommands (Cut scan)

variable {KemSK Result σ ι' : Type} {spec' : OracleSpec ι'}

/-- One forwarded request of the logged scan: the potential and the remaining bound of the continuation move together. -/
theorem scanL_forward (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec'))) (potential : σ → ℕ∞)
    (step : ∀ query state, ∀ result ∈ support ((handler query).run state),
      potential result.2 ≤ potential state + ((if TableKindL query then 1 else 0 : ℕ) : ℕ∞))
    (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (n : ℕ)
    (bounded : (liftM ((Spec KemSK).query query) >>= next : OracleComp (Spec KemSK) Result).IsQueryBoundP
      (TableKindL (KemSK := KemSK)) n)
    (index : Nat) (state : σ)
    (ih : ∀ reply (n : ℕ), (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) n → ∀ state,
      ∀ result ∈ support ((simulateQ handler (scan (next reply) index)).run state), ∀ raw rest,
        result.1 = .pending raw rest → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
          ∀ reply, (rest reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) (n - c - 1)) :
    ∀ result ∈ support ((simulateQ handler (liftM ((Spec KemSK).query query) >>= fun reply =>
        scan (next reply) index)).run state), ∀ raw rest,
      result.1 = .pending raw rest → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (rest reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) (n - c - 1) := by
  intro result reached raw rest pending
  rw [isQueryBoundP_query_bind_iff] at bounded
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, first, later⟩ := reached
  obtain ⟨c, growth, room, remaining⟩ := ih middle.1 _ (bounded.2 middle.1) middle.2 result later raw rest pending
  have now := step query state middle first
  by_cases target : TableKindL query
  · have positive : 0 < n := bounded.1.resolve_left (not_not.mpr target)
    simp only [target, ite_true, Nat.cast_one] at room remaining now
    refine ⟨c + 1, ?_, by omega, fun reply => (remaining reply).mono (by omega)⟩
    calc potential result.2 ≤ potential middle.2 + c := growth
      _ ≤ potential state + 1 + c := add_le_add now le_rfl
      _ = potential state + ((c + 1 : ℕ) : ℕ∞) := by
        rw [add_assoc, Nat.cast_add, Nat.cast_one, add_comm (1 : ℕ∞)]
  · simp only [target, ite_false, Nat.cast_zero, add_zero] at room remaining now
    exact ⟨c, growth.trans (add_le_add now le_rfl), room, remaining⟩

/-- The cut-split along the logged scan to the selected raw accept (`PqxdhRegistrationJointKemRomSplit.scan_potential` for `PqxdhDeploymentLaterServerCommands.scan`, which forwards the Server read unchanged): the potential at the cut has grown by at most `c`, the cut's accept and the `c` table requests before it fit the budget, and the suspended continuation keeps the rest of it. -/
theorem scanL_potential (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec'))) (potential : σ → ℕ∞)
    (step : ∀ query state, ∀ result ∈ support ((handler query).run state),
      potential result.2 ≤ potential state + ((if TableKindL query then 1 else 0 : ℕ) : ℕ∞))
    (work : OracleComp (Spec KemSK) Result) (n : ℕ) (bounded : work.IsQueryBoundP (TableKindL (KemSK := KemSK)) n)
    (index : Nat) (state : σ) :
    ∀ result ∈ support ((simulateQ handler (scan work index)).run state), ∀ raw next,
      result.1 = .pending raw next → ∃ c : ℕ, potential result.2 ≤ potential state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) (n - c - 1) := by
  induction work using OracleComp.inductionOn generalizing index n state with
  | pure value =>
      intro result reached raw next pending
      change result ∈ support ((simulateQ handler (pure (Cut.complete value) : OracleComp (Spec KemSK) _)).run state)
        at reached
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      cases pending
  | query_bind query next ih =>
      rcases query with ((coin | request) | read) | later
      · exact scanL_forward handler potential step _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · cases request with
        | accept raw =>
            cases index with
            | zero =>
                intro result reached raw' rest pending
                change result ∈ support ((simulateQ handler (pure (Cut.pending raw next) :
                  OracleComp (Spec KemSK) _)).run state) at reached
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
                subst reached
                cases pending
                rw [isQueryBoundP_query_bind_iff] at bounded
                have positive : 0 < n := bounded.1.resolve_left (not_not.mpr trivial)
                refine ⟨0, by simp, by omega, fun reply => ?_⟩
                have later := bounded.2 reply
                rw [ite_eq_left (show TableKindL (KemSK := KemSK) (.inl (.inl (.inr (.accept raw)))) from trivial)]
                  at later
                simpa using later
            | succ index =>
                exact scanL_forward handler potential step _ next n bounded index state
                  (fun reply n bounded state => ih reply n bounded index state)
        | _ =>
            exact scanL_forward handler potential step _ next n bounded index state
              (fun reply n bounded state => ih reply n bounded index state)
      · exact scanL_forward handler potential step _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · exact scanL_forward handler potential step _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)

end Scan

/-! ### Keys of the table cache before the cut -/

section Prefix

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-- The exposed logged raw accept adds at most one key to the table cache: forgetting the logged scalar keeps the native state (`PqxdhDeploymentLaterServerCommands.accept_fst`), and the exposed accept adds at most one (`PqxdhRegistrationJointKemRomSplit.impl_grows`). -/
theorem acceptL_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    Grows (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw) 1 := by
  intro state result reached
  have forgotten : (result.1.1, result.2) ∈ support
      ((PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
        state) := by
    rw [← PqxdhDeploymentLaterServerCommands.accept_fst, support_map]
    exact ⟨result, reached, rfl⟩
  simpa [NativeKind] using impl_grows (Response := Response) setup codec checks identityIndex publicIdentity
    (.inr (.accept raw)) state _ forgotten

/-- Every native step of the logged source client's backend adds at most one key, and only on a native table request. -/
theorem implL_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (query : (SpecL KemSK Response).Domain) :
    Grows (implL setup codec checks identityIndex publicIdentity query) (if NativeKindL query then 1 else 0) := by
  rcases query with query | raw
  · exact impl_grows setup codec checks identityIndex publicIdentity query
  · have grows := acceptL_grows (Response := Response) setup codec checks identityIndex publicIdentity raw
    simp only [NativeKindL]
    exact grows

/-- Every logged-source request makes at most one native table request, and only if it is a table request of the logged source. -/
theorem client_boundL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    ((clientL (Response := Response) setup codec identityIndex query).run held).IsQueryBoundP
      (NativeKindL (KemSK := KemSK) (Response := Response)) (if TableKindL query then 1 else 0) := by
  have lifted : ∀ {β : Type} (work : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) β) (k : ℕ),
      work.IsQueryBoundP (NativeKind (KemSK := KemSK) (Response := Response)) k →
      IsQueryBoundP (simulateQ (fun q => ((SpecL KemSK Response).query (.inl q) : OracleComp (SpecL KemSK Response) _))
        work) (NativeKindL (KemSK := KemSK) (Response := Response)) k := by
    intro _ work k bounded
    refine IsQueryBoundP.simulateQ_of_step bounded (fun query native => query_one _ _)
      (fun query native => query_free _ _ ?_)
    simpa [NativeKindL] using native
  rcases query with ((coin | request) | read) | later
  · simp only [clientL, logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (client_bound setup codec _ held.1)
  · cases request
    case accept raw =>
      simp only [clientL, logClient, StateT.run, isQueryBoundP_map_iff]
      exact query_one _ _
    all_goals
      simp only [clientL, logClient, StateT.run, isQueryBoundP_map_iff]
      exact lifted _ _ (client_bound setup codec _ held.1)
  · simp only [clientL, logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (client_bound setup codec _ held.1)
  · simp only [clientL, logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (query_free _ _ (by simp [NativeKind]))

/-- The cut-split for the logged-source program interpreted by the logged command handler: at a reached cut, the keys of the table cache have grown by at most `c`, the selected accept and the `c` table requests before it fit the table budget, and the suspended continuation keeps the rest of it. -/
theorem commandsL_cut (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKindL (KemSK := KemSK)) n) (index : Nat) (owners : List EncodedEntry)
    (log : Log) (state : NativeState KemSK) :
    ∀ reached ∈ support (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
        (PqxdhDeploymentLaterServerCommands.scan work index) owners log state), ∀ raw next,
      reached.1.1 = .pending raw next → ∃ c : ℕ, keyCount reached.2 ≤ keyCount state + c ∧ c + 1 ≤ n ∧
        ∀ reply, (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) (n - c - 1) := by
  intro reached member raw next pending
  rw [run_clientL (Response := Response)] at member
  have composed := compose_run (clientL (Response := Response) setup codec identityIndex)
    (implL setup codec checks identityIndex publicIdentity) (PqxdhDeploymentLaterServerCommands.scan work index)
    (owners, log) state
  have lifted : (reached.1.1, (reached.1.2, reached.2)) ∈ support ((simulateQ (compose
      (clientL (Response := Response) setup codec identityIndex)
        (implL setup codec checks identityIndex publicIdentity))
        (PqxdhDeploymentLaterServerCommands.scan work index)).run ((owners, log), state)) := by
    rw [composed, support_map]
    exact ⟨reached, member, rfl⟩
  have step : ∀ query (current : Local × NativeState KemSK),
      ∀ result ∈ support ((compose (clientL (Response := Response) setup codec identityIndex)
        (implL setup codec checks identityIndex publicIdentity) query).run current),
      keyCount result.2.2 ≤ keyCount current.2 + ((if TableKindL query then 1 else 0 : ℕ) : ℕ∞) := by
    intro query current result reachedStep
    rw [compose, StateT.run_mk, support_map] at reachedStep
    obtain ⟨inner, innerReached, rfl⟩ := reachedStep
    exact potential_run (implL setup codec checks identityIndex publicIdentity) keyCount NativeKindL
      (fun native nativeState nativeResult nativeReached =>
        implL_grows setup codec checks identityIndex publicIdentity native nativeState nativeResult nativeReached)
      _ _ (client_boundL setup codec identityIndex query current.1) current.2 inner innerReached
  exact scanL_potential _ (fun current => keyCount current.2) step work n bounded index ((owners, log), state) _ lifted
    raw next pending

end Prefix

/-! ### The table cache at the cut of the logged KEM-ideal branch -/

section Start

open PqxdhDeploymentLaterServerOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque rejectRun)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The completion of a rejected logged raw accept is a completed logged opaque cut. -/
theorem rejectRunL_complete (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (owners : List EncodedEntry)
    (log : Log) (state : NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (cut : OpaqueCut Reader KemSK X R)
    (reached : cut ∈ support (rejectRun setup codec checks identityIndex publicIdentity observe raw next owners log
      state collected logged)) :
    ∃ outcome, cut = .complete outcome := by
  rw [rejectRun, mem_support_bind_iff] at reached
  obtain ⟨_, _, reached⟩ := reached
  rw [support_map] at reached
  obtain ⟨outcome, _, same⟩ := reached
  exact ⟨outcome, same.symm⟩

/-- The table-cache keys of an active logged opaque cut fit the table budget together with the remaining budget of its continuation. -/
def FitsCutL (n : ℕ) : OpaqueCut Reader KemSK X R → Prop
  | .complete _ => True
  | .pending _ _ _ _ native _ _ next => ∃ c : ℕ, (cacheKeys native.1.cache).encard ≤ c ∧ c + 1 ≤ n ∧
      ∀ reply, (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) (n - c - 1)

/-- Every cut reached by the explicit logged opaque scan from an empty table fits the table budget. A rejected verification and a rejection before encapsulation complete the run, including whatever the rest of the program (its terminal reads, the Server read and its post phase, for the compiled LQ-F program) does inside the prefix. -/
theorem opaqueScanL_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKindL (KemSK := KemSK)) n) (index : Nat) (owners : List EncodedEntry)
    (log : Log) (state : NativeState KemSK) (empty : keyCount state = 0) :
    ∀ cut ∈ support (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index
      owners log state), FitsCutL n cut := by
  intro cut reached
  rw [opaqueScan, mem_support_bind_iff] at reached
  obtain ⟨found, foundReached, reached⟩ := reached
  have commandsReached := PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ foundReached
  rcases scanCut : found.1.1 with result | ⟨raw, next⟩
  · rw [scanCut] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    trivial
  · rw [scanCut] at reached
    dsimp only at reached
    rcases verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | value
    · rw [verified] at reached
      obtain ⟨_, rfl⟩ := rejectRunL_complete setup codec checks identityIndex publicIdentity observe raw next _ _ _ _ _
        cut reached
      trivial
    · rw [verified] at reached
      dsimp only at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨⟨⟨_ | ephemeral, entry⟩, consumed⟩, _, reached⟩ := reached
      · obtain ⟨_, rfl⟩ := rejectRunL_complete setup codec checks identityIndex publicIdentity observe raw next _ _ _
          _ _ cut reached
        trivial
      · simp only [support_pure, Set.mem_singleton_iff] at reached
        subst reached
        obtain ⟨c, growth, room, remaining⟩ := commandsL_cut (Response := Response) setup codec checks identityIndex
          publicIdentity work n bounded index owners log state found commandsReached raw next scanCut
        rw [empty, zero_add] at growth
        exact ⟨c, growth, room, remaining⟩

/-- Fit of the table cache of an active logged prechallenge context. -/
def FitsL {count : Nat} (n : ℕ) : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some cut) _ _ => FitsCutL n cut
  | _ => True

/-- Every prechallenge context of the logged KEM-ideal branch fits the table budget. -/
theorem sourcePreOpaqueL_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKindL (KemSK := KemSK)) n) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), FitsL n context := by
  intro context reached
  rw [sourcePreOpaque, mem_support_bind_iff] at reached
  obtain ⟨born, _, reached⟩ := reached
  rcases bornCase : born.1 with _ | created
  · rw [bornCase] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    rw [reached]
    trivial
  · rw [bornCase] at reached
    dsimp only at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨others, _, result, resultReached, rfl⟩ := reached
    rcases cutCase : result.1 with _ | cut
    · simp only [FitsL]
    · simp only [FitsL]
      have scanReached := support_option _ _ _ cut result.2 (by rw [← cutCase]; exact resultReached)
      exact opaqueScanL_fits setup codec checks _ _ _ work n bounded index [] [] _ (initial_keys created) cut
        scanReached

/-- Every outcome of G1's prefix for the logged KEM-ideal branch has a fitting context, and its table cache is the cache of that context. -/
theorem sharedStartL_fits (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (n : ℕ)
    (bounded : work.IsQueryBoundP (TableKindL (KemSK := KemSK)) n) :
    ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index), start.1 = cacheOfL start.2.2.1 ∧ FitsL n start.2.2.1 := by
  intro start reached
  simp only [sharedStartL, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact ⟨rfl, sourcePreOpaqueL_fits setup codec checks ensureInit supplied decision work runtime count selected index
    chosen n bounded context contextReached⟩

end Start

/-! ### Table reads after the cut -/

section Post

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The table requests of the logged grouped interface: those of the grouped interface, and the logged accept. -/
def groupKindL : (GSpecL KemSK Response).Domain → Bool
  | .inl query => groupKind (KemSK := KemSK) (Response := Response) query
  | .inr _ => true

/-- Every native step of the logged skeleton makes at most one table read, and only on a table request of the logged grouped interface; the logged accept makes at most one, its root read. -/
theorem skelImplL_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpecL KemSK Response).Domain) :
    ReadsC (skelImplL setup codec checks identityIndex publicIdentity services query)
      (if groupKindL query = true then 1 else 0) := by
  rcases query with query | raw
  · exact skelImpl_reads setup codec checks identityIndex publicIdentity services query
  · intro state
    simp only [groupKindL, ite_true]
    change ((acceptStepL (V := V) setup codec checks identityIndex publicIdentity raw).run state).IsQueryBoundP _ 1
    unfold acceptStepL
    rw [StateT.run_bind]
    refine isQueryBoundP_bind (n := 0) (m := 1) trivial fun first _ => ?_
    rw [StateT.run_bind]
    refine isQueryBoundP_bind (n := 0) (m := 1) ?_ fun second _ => ?_
    · change ((fun result => (result, first.2)) <$> simulateQ (encLift (V := V)) _).IsQueryBoundP _ 0
      rw [isQueryBoundP_map_iff]
      exact simulate_free (encLift (KemSK := KemSK) (V := V)) _
        (fun query => query_free _ _ (by simp [tableRead?])) _
    · rw [StateT.run_bind]
      exact isQueryBoundP_bind (n := 1) (m := 0) (readsC_liftT (readsN_acceptTail setup publicIdentity _ _) _)
        fun _ _ => trivial

/-- Every logged-source request makes at most one table request of the logged grouped interface, and only if it is a table request of the logged source. -/
theorem groupedClientL_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    ((groupedClientL (Response := Response) setup codec selected challenge identityIndex query).run held).IsQueryBoundP
      (fun query => groupKindL (KemSK := KemSK) (Response := Response) query = true)
      (if TableKindL query then 1 else 0) := by
  rw [groupedClientL_log]
  have lifted : ∀ {β : Type} (work : OracleComp (GSpec KemSK Response) β) (k : ℕ),
      work.IsQueryBoundP (fun query => groupKind (KemSK := KemSK) (Response := Response) query = true) k →
      IsQueryBoundP
        (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _)) work)
        (fun query => groupKindL (KemSK := KemSK) (Response := Response) query = true) k := by
    intro _ work k bounded
    refine IsQueryBoundP.simulateQ_of_step bounded (fun query group => query_one _ _)
      (fun query group => query_free _ _ ?_)
    simpa [groupKindL] using group
  rcases query with ((coin | request) | read) | later
  · simp only [logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (groupedClient_bound setup codec selected challenge _ held.1)
  · cases request
    case accept raw =>
      simp only [logClient, StateT.run, isQueryBoundP_map_iff]
      exact query_one _ _
    all_goals
      simp only [logClient, StateT.run, isQueryBoundP_map_iff]
      exact lifted _ _ (groupedClient_bound setup codec selected challenge _ held.1)
  · simp only [logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (groupedClient_bound setup codec selected challenge _ held.1)
  · simp only [logClient, StateT.run, isQueryBoundP_map_iff]
    exact lifted _ _ (query_free _ _ (by simp [groupKind]))

open PqxdhDeploymentLaterServerOpaque (OpaqueContext)

variable {A X R : Type}

/-- The resumed logged client of the skeleton makes at most one table read for the Server's resumption and one per table request of the continuation. -/
theorem skelResumeL_reads (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (services : Services V Response) (m : ℕ)
    (bounded : ∀ reply, (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) m) :
    (skelResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners log
      next selected ciphertext services).IsQueryBoundP (fun query => tableRead? query = true) (1 + m) := by
  unfold skelResumeL
  refine isQueryBoundP_bind
    (IsQueryBoundP.simulateQ_run_StateT_of_step (resume_root setup codec checks identityIndex publicIdentity raw value
      ephemeral _ _ game consumed)
      (fun query state => resumeImpl_reads setup.hmac game.sessions services query state) _)
    fun answer _ => ?_
  have tagged : (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1).IsQueryBoundP
      (TableKindL (KemSK := KemSK)) m := by
    unfold PqxdhDeploymentLaterServerCut.tagged
    rw [isQueryBoundP_map_iff]
    exact bounded answer.1
  refine IsQueryBoundP.simulateQ_run_StateT_of_step ?_ (fun query state =>
    skelImplL_reads setup codec checks identityIndex publicIdentity services query state) answer.2
  exact IsQueryBoundP.simulateQ_run_StateT_of_step tagged (fun query current =>
    groupedClientL_bound setup codec selected ciphertext identityIndex query current) _

/-- The remaining table budget of the continuation of an active logged prechallenge context. -/
def ContinuationBoundL {count : Nat} (m : ℕ) : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some (.pending _ _ _ _ _ _ _ next)) _ _ =>
      ∀ reply, (next reply).IsQueryBoundP (TableKindL (KemSK := KemSK)) m
  | _ => True

/-- The logged skeleton's postchallenge phase makes at most `1 + m` direct reads. -/
theorem postSkelL_direct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (m : ℕ) (bounded : ContinuationBoundL m context) :
    (postSkelL setup codec checks decision count selected services chosen challenge context).IsQueryBoundP
      (fun query => directRead? query = true) (1 + m) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkelL]
    split
    · rw [isQueryBoundP_map_iff]
      refine IsQueryBoundP.of_imp (fun query direct => direct_table query direct) ?_
      refine fwd_reads _ _ _ ?_
      refine fwdOption_reads _ _ _ ?_ _
      refine fwd_reads _ _ _ ?_
      exact skelResumeL_reads setup codec checks _ _ _ raw value ephemeral consumed native.2 owners log next
        selected.val challenge services m bounded
    · trivial

/-- The client of G1's shared world for the logged KEM-ideal branch makes at most `1 + m` direct reads. -/
theorem sharedClientL_direct (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext) (m : ℕ)
    (bounded : ContinuationBoundL m context.2.1) :
    (sharedClientL setup codec checks decision count selected context).IsQueryBoundP
      PqxdhExtractRomHiddenSuffix.IsDirect (1 + m) := by
  refine IsQueryBoundP.simulateQ_of_step (postSkelL_direct setup codec checks decision count selected _ context.1
    context.2.2 context.2.1 m bounded) (fun query direct => ?_) (fun query direct => ?_)
  · rcases query with coin | (point | point)
    · simp [directRead?] at direct
    · simp [directRead?] at direct
    · exact query_one _ _
  · rcases query with coin | (point | point)
    · exact query_free _ _ (by simp [PqxdhExtractRomHiddenSuffix.IsDirect])
    · simp only [compileHidden, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, isQueryBoundP_map_iff]
      exact query_free _ _ (by simp [PqxdhExtractRomHiddenSuffix.IsDirect])
    · simp [directRead?] at direct

/-- The client of an inactive logged prechallenge context makes no direct read. -/
theorem sharedClientL_inactive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)
    (inactive : ∀ created others raw value ephemeral consumed native owners log next state runtime,
      context.2.1 ≠ .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state
        runtime) :
    (sharedClientL setup codec checks decision count selected context).IsQueryBoundP
      PqxdhExtractRomHiddenSuffix.IsDirect 0 := by
  obtain ⟨chosen, context, challenge⟩ := context
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  · trivial
  · trivial
  · trivial
  · exact absurd rfl (inactive created others raw value ephemeral consumed native owners log next state runtime)

end Post

/-! ### G1 for the logged KEM-ideal branch -/

section Split

open PqxdhDeploymentLaterServerOpaque (OpaqueContext opaqueBranch)
open PqxdhExtractRomHiddenSuffix (sharedGame splitGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- Stage S1c over the logged source, the G1 instance: the shared world of stage S1b over the logged source and G1's split world are distinguishable with advantage at most the logged source's table budget over `2^256` (coefficient one). -/
theorem shared_splitL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind)) :
    (sharedGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected)).boolDistAdvantage
      (splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected)) ≤
      (tableBudget budget : ℝ) / 2 ^ 256 := by
  have fits := sharedStartL_fits (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index (tableBudget budget) (certified_tableL work budget certified)
  have finite : ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work
      runtime count selected index), (cacheKeys start.1).Finite ∧ ∃ c : ℕ, (cacheKeys start.1).encard ≤ c ∧
        c ≤ tableBudget budget ∧ (sharedClientL setup codec checks decision count selected start.2).IsQueryBoundP
          PqxdhExtractRomHiddenSuffix.IsDirect (tableBudget budget - c) := by
    intro start reached
    obtain ⟨cache, fit⟩ := fits start reached
    obtain ⟨table, chosen, context, challenge⟩ := start
    dsimp only at cache fit ⊢
    subst cache
    have inactive : ∀ context : OpaqueContext Reader KemSK A X count,
        (∀ created others raw value ephemeral consumed native owners log next state runtime,
          context ≠ .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state
            runtime) →
        cacheOfL context = ∅ →
        (cacheKeys (cacheOfL context)).Finite ∧ ∃ c : ℕ, (cacheKeys (cacheOfL context)).encard ≤ c ∧
          c ≤ tableBudget budget ∧ (sharedClientL setup codec checks decision count selected
            (chosen, context, challenge)).IsQueryBoundP PqxdhExtractRomHiddenSuffix.IsDirect
              (tableBudget budget - c) := by
      intro context other empty
      rw [empty, cacheKeys_empty]
      exact ⟨Set.finite_empty, 0, by simp, Nat.zero_le _,
        (sharedClientL_inactive setup codec checks decision count selected _ other).mono (Nat.zero_le _)⟩
    rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners,
      log, next⟩), state, runtime⟩
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    · exact inactive _ (fun _ _ _ _ _ _ _ _ _ _ _ _ same => by cases same) rfl
    obtain ⟨c, keysCount, room, remaining⟩ := fit
    refine ⟨Set.finite_of_encard_le_coe keysCount, c, keysCount, by omega, ?_⟩
    refine (sharedClientL_direct setup codec checks decision count selected
      (chosen, .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state
        runtime, challenge) (tableBudget budget - c - 1) remaining).mono (by omega)
  refine PqxdhExtractRomHiddenSuffix.hidden_suffix_bound _ _ (tableBudget budget) keys
    (fun start => tableBudget budget - (keys start).card) ?_ ?_ ?_
  · intro start reached point present
    exact keys_cover start (finite start reached).1 point present
  · intro start reached
    obtain ⟨fin, c, keysCount, room, direct⟩ := finite start reached
    exact direct.mono (Nat.sub_le_sub_left (keys_card start fin c keysCount) _)
  · intro start reached
    obtain ⟨fin, c, keysCount, room, _⟩ := finite start reached
    have := keys_card start fin c keysCount
    omega

/-- Stage S1c over the logged source. The logged opaque KEM-ideal branch (theorem T6 for the logged source) and G1's split world on the logged prefix and client (`sharedStartL`, `sharedClientL`) are distinguishable with advantage at most `(qAccept + qFinish + qHmac) / 2^256`, the logged source's caps of raw accepts, Beacon finishes and public HMAC requests over `2^256` (coefficient one). The premise is the logged source budget `certified` (caps per source14 kind through `PqxdhDeploymentLaterServerReserve.laterKind`); the Server read has no kind and reads no table. The compiled LQ-F program meets `certified` at the transported caps (`PqxdhDeploymentLaterServerCompileBudget.compile_server_certified`), whose HMAC cap is `qHmac + qHmac₂`, and at these caps the bound is `(qAccept + qFinish + (qHmac + qHmac₂)) / 2^256` (`PqxdhDeploymentLaterServerItemTargets.later_guess_term`), so post-run HMAC queries are charged with coefficient one. Three cases arise for the selected accept: (a) it is active and its KEM key is the challenger's, and each post-run HMAC query after the cut makes at most one direct read of G1's client; (b) it is active with another KEM key, and the branch returns `false` at once, runs no continuation (the post phase included) and makes no read; (c) it is never reached or rejects before encapsulation, and the whole program finishes inside the prefix, the context is inactive and its client makes no read, so the charge for that prefix outcome is zero within the same bound. In the split world the hidden entries are keyed by their 128-byte coordinates alone, no secret is drawn, and the KEM candidate is not the suffix of any key of the shared Extract-table cache. This step is valid only because the zero-key 192-byte Extract slice is modelled as a random oracle (route R1): R1 gives the hidden entries at distinct coordinates their mutual independence in both worlds. In LQ-F the post-run adversary knows both hidden entries' 128-byte DH coordinates exactly, so the unpredictability of the entries and their independence rest on R1 alone. -/
theorem opaqueBranchL_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind)) :
    (opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false).boolDistAdvantage
      (splitGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index) (sharedClientL setup codec checks decision count selected)) ≤
      ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 := by
  rw [PqxdhDeploymentLaterServerItemShared.opaqueBranchL_shared]
  exact shared_splitL setup codec checks ensureInit supplied decision work runtime count selected index budget
    certified

end Split

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.tableKindL_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.tableKindL_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.certified_tableL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.certified_tableL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.scanL_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.scanL_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.scanL_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.scanL_potential

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.acceptL_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.acceptL_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.implL_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.implL_grows

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.client_boundL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.client_boundL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.commandsL_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.commandsL_cut

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.opaqueScanL_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.opaqueScanL_fits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sourcePreOpaqueL_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sourcePreOpaqueL_fits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedStartL_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedStartL_fits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.skelImplL_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.skelImplL_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.groupedClientL_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.groupedClientL_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.skelResumeL_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.skelResumeL_reads

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.postSkelL_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.postSkelL_direct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedClientL_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedClientL_direct

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedClientL_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.sharedClientL_inactive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.shared_splitL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.shared_splitL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.opaqueBranchL_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemSplit.opaqueBranchL_split
