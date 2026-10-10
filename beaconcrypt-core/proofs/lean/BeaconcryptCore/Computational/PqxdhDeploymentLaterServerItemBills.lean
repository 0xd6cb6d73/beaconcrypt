-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemKeys
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemKeyTransferBills

/-! LQ-F upstream, unit A2: the bills of the item 2 reductions over the logged source (stage S8 and theorem T8b's bills; LQ-F upstream design-v2, section 4.4, module `…ItemBills`). Besides the guessing term, the loss `slotLossL` of the U-L1 targets consists of advantages of constructed reductions: the two one-query HMAC-SHA-512 PRF reductions `indexedReduction setup.hmac rootClientL slot` (slots 0 and 1) and the four G2 key-schedule reductions on each `entryDkL k` (`k < 2`). `laterSlot_bills` gives each of them its challenge-query count and its complete local bill at the frozen coin bill `rootBillL` of unit D1 (`laterSlot_bills_compiled` at the compiled LQ-F program and the transported caps), and `idealKeysL_bills` does the same for theorem T7 over the logged source (`entryDL`).

- The continuation suspended at the cut of the logged scan inherits every query bound of the logged-source program (`scanL_inherit`, `commandsL_inherit`, `opaqueScanL_inherit`, `sourcePreOpaqueL_inherit`, `sharedStartL_inherit`; the classical chain of `PqxdhRegistrationJointKemRootExpandCount` for `PqxdhDeploymentLaterServerCommands.scan`, which forwards the Server read unchanged).
- Weights: the logged grouped interface charges the classical weight `PqxdhRegistrationJointKemRootCosts.wG` to every classical request except a private-pool request, which it charges its pool weight `wPool` (at most `wG`, `wPool_le`), and `96 + encapsCost` to the logged accept (`wGL`). Every logged-source request then costs at most `wSourceL` of its kind (`groupedClientL_cost`): the classical `wSource` of its source14 kind, and 0 for the Server read, which is one identity-pool reveal (no creation, no coin; LQ-F upstream design-v2, decision D8). The logged skeleton's steps cost at most their weight (`skelImplL_cost`; the logged accept by its classical projection, `acceptStepL_fst`).
- The postchallenge phase costs at most `64 + Σ wSource · budget` (`skelResumeL_cost`, `postSkelL_cost`, through `PqxdhRegistrationJointKemRootCosts.source_sum` this is `postBill`), and the logged prefix at most the classical `prefixBill` (`sourcePreOpaqueL_total`, `sharedStartL_total`): `PqxdhDeploymentLaterServerKemHop.pre_source` and `PqxdhDeploymentLaterServerOpaque.pre_opaque` identify the logged opaque prephase with the evaluated prephase of the KEM adversary at the logged exposure, whose allowances are `PqxdhDeploymentLaterServerBills.pre_uniform`, `pre_base` and `pre_decapsulations` (the classical numbers). So the logged root clients draw at most `rootBillL` coins (`rootClientL_coins`, `entryClientL_coins`), and the distinguishers at most `rootBillL + 64` (`entryDL_total`) and `rootBillL + 216` (`entryDkL_total`).

Every bill takes a cap `reads` on the Server reads of the program, as `LaterServerBills.adversary_bound` does: the weighted composition `wBound_kinds` needs a cap for every request kind; the Server read weighs 0, so the cap enters no bill. The compiled LQ-F program meets it with one (`PqxdhDeploymentLaterServerCompileBudget.compile_server_reads`). The bills are resource bounds: they make no security claim and add no premise to the targets. The premises are the logged source budget, `KemBound setup caps` and the runtime initialization bound `initBound`, the premises of the classical stage S8. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemPostSkeleton (GSpec Services SkelState groupedPoolLift acceptStep)
open PqxdhRegistrationJointKemRomSplit (compose compose_run support_option)
open PqxdhRegistrationJointKemRootCosts (WBound wBound_map wBound_map_iff wBound_query wBound_bind wBound_kinds
  wBound_simulate wBound_run wBound_weight_mono isQueryBoundP_of_wBound wBound_liftComp_inl wBound_of_total wG wPool
  wPool_le wEnc wSkel wRoot wResume wSource wEntry wTable2 skelImpl_cost groupedClient_cost resumeImpl_cost resume_cost
  lower_cost source_sum ServiceBills nativeServices_bills factoredServices_bills preBill prefixBill rootBill
  publicLocal_cost publicLocalV_cost table_total firstTable_step indexedTable_step rootSample_total pinned_total)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerCommands (Local)
open PqxdhDeploymentLaterServerReserve (laterKind)
open PqxdhDeploymentLaterServerItemTargets (GSpecL skelImplL groupedClientL skelResumeL postSkelL sharedStartL
  rootClientL entryClientL entryDL entryDkL rootBillL)
open PqxdhDeploymentLaterServerItemFree (clientL implL run_clientL)
open PqxdhDeploymentLaterServerItemOnce (groupedClientL_run entryClientL_two rootClientL_two)

/-! ### The continuation at the cut inherits the logged source's query bounds -/

section Scan

open PqxdhDeploymentLaterServerSource (Spec)
open PqxdhDeploymentLaterServerCommands (Cut scan)

variable {KemSK Result σ ι' : Type} {spec' : OracleSpec ι'}

/-- One forwarded request of the logged scan: the continuation of the rest inherits the bound. -/
theorem inheritL_forward (P : (Spec KemSK).Domain → Prop) [DecidablePred P]
    (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec')))
    (query : (Spec KemSK).Domain) (next : (Spec KemSK).Range query → OracleComp (Spec KemSK) Result) (n : ℕ)
    (bounded : (liftM ((Spec KemSK).query query) >>= next : OracleComp (Spec KemSK) Result).IsQueryBoundP P n)
    (index : Nat) (state : σ)
    (ih : ∀ reply (n : ℕ), (next reply).IsQueryBoundP P n → ∀ state,
      ∀ result ∈ support ((simulateQ handler (scan (next reply) index)).run state), ∀ raw rest,
        result.1 = .pending raw rest → ∀ reply, (rest reply).IsQueryBoundP P n) :
    ∀ result ∈ support ((simulateQ handler (liftM ((Spec KemSK).query query) >>= fun reply =>
        scan (next reply) index)).run state), ∀ raw rest,
      result.1 = .pending raw rest → ∀ reply, (rest reply).IsQueryBoundP P n := by
  intro result reached raw rest pending reply
  rw [isQueryBoundP_query_bind_iff] at bounded
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
  obtain ⟨middle, _, later⟩ := reached
  refine (ih middle.1 _ (bounded.2 middle.1) middle.2 result later raw rest pending reply).mono ?_
  split <;> omega

/-- The continuation suspended by the logged scan at the selected raw accept inherits every query bound of the logged-source program (`PqxdhRegistrationJointKemRootExpand.scan_inherit` for `PqxdhDeploymentLaterServerCommands.scan`). -/
theorem scanL_inherit (P : (Spec KemSK).Domain → Prop) [DecidablePred P]
    (handler : QueryImpl (Spec KemSK) (StateT σ (OracleComp spec')))
    (work : OracleComp (Spec KemSK) Result) (n : ℕ) (bounded : work.IsQueryBoundP P n) (index : Nat) (state : σ) :
    ∀ result ∈ support ((simulateQ handler (scan work index)).run state), ∀ raw next,
      result.1 = .pending raw next → ∀ reply, (next reply).IsQueryBoundP P n := by
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
      · exact inheritL_forward P handler _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · cases request with
        | accept raw =>
            cases index with
            | zero =>
                intro result reached raw' rest pending reply
                change result ∈ support ((simulateQ handler (pure (Cut.pending raw next) :
                  OracleComp (Spec KemSK) _)).run state) at reached
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
                subst reached
                cases pending
                rw [isQueryBoundP_query_bind_iff] at bounded
                refine (bounded.2 reply).mono ?_
                split <;> omega
            | succ index =>
                exact inheritL_forward P handler _ next n bounded index state
                  (fun reply n bounded state => ih reply n bounded index state)
        | _ =>
            exact inheritL_forward P handler _ next n bounded index state
              (fun reply n bounded state => ih reply n bounded index state)
      · exact inheritL_forward P handler _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)
      · exact inheritL_forward P handler _ next n bounded index state
          (fun reply n bounded state => ih reply n bounded index state)

end Scan

section Start

open PqxdhDeploymentLaterServerOpaque (OpaqueCut OpaqueContext opaqueScan sourcePreOpaque)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The continuation at a reached cut of the logged-source program, interpreted by the logged command handler, inherits every query bound of the program. -/
theorem commandsL_inherit (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (n : ℕ) (bounded : work.IsQueryBoundP P n)
    (index : Nat) (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    ∀ reached ∈ support (PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
        (PqxdhDeploymentLaterServerCommands.scan work index) owners log state), ∀ raw next,
      reached.1.1 = .pending raw next → ∀ reply, (next reply).IsQueryBoundP P n := by
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
  exact scanL_inherit P _ work n bounded index ((owners, log), state) _ lifted raw next pending

/-- The continuation of an active logged opaque cut keeps a bound. -/
def InheritsCutL (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P] (n : ℕ) :
    OpaqueCut Reader KemSK X R → Prop
  | .complete _ => True
  | .pending _ _ _ _ _ _ _ next => ∀ reply, (next reply).IsQueryBoundP P n

/-- Every cut reached by the explicit logged opaque scan inherits every query bound of the logged-source program. -/
theorem opaqueScanL_inherit (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (n : ℕ) (bounded : work.IsQueryBoundP P n)
    (index : Nat) (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    ∀ cut ∈ support (opaqueScan (Reader := Reader) setup codec checks identityIndex publicIdentity observe work index
      owners log state), InheritsCutL P n cut := by
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
      obtain ⟨_, rfl⟩ := PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete setup codec checks identityIndex
        publicIdentity observe raw next _ _ _ _ _ cut reached
      trivial
    · rw [verified] at reached
      dsimp only at reached
      rw [mem_support_bind_iff] at reached
      obtain ⟨⟨⟨_ | ephemeral, entry⟩, consumed⟩, _, reached⟩ := reached
      · obtain ⟨_, rfl⟩ := PqxdhDeploymentLaterServerItemSplit.rejectRunL_complete setup codec checks identityIndex
          publicIdentity observe raw next _ _ _ _ _ cut reached
        trivial
      · simp only [support_pure, Set.mem_singleton_iff] at reached
        subst reached
        exact commandsL_inherit P setup codec checks identityIndex publicIdentity work n bounded index owners log state
          found commandsReached raw next scanCut

/-- The continuation of an active logged prechallenge context keeps a bound. -/
def InheritsL (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P] {count : Nat}
    (n : ℕ) : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some cut) _ _ => InheritsCutL P n cut
  | _ => True

/-- Every logged prechallenge context of the logged KEM-ideal branch inherits every query bound of the logged-source program. -/
theorem sourcePreOpaqueL_inherit (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) (n : ℕ)
    (bounded : work.IsQueryBoundP P n) :
    ∀ context ∈ support (sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index chosen), InheritsL P n context := by
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
    · simp only [InheritsL]
    · simp only [InheritsL]
      have scanReached := support_option _ _ _ cut result.2 (by rw [← cutCase]; exact resultReached)
      exact opaqueScanL_inherit P setup codec checks _ _ _ work n bounded index [] [] _ cut scanReached

/-- Every outcome of G1's prefix for the logged KEM-ideal branch has a context whose continuation inherits every query bound of the logged-source program. -/
theorem sharedStartL_inherit (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (n : ℕ) (bounded : work.IsQueryBoundP P n) :
    ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index), InheritsL P n start.2.2.1 := by
  intro start reached
  simp only [sharedStartL, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨chosen, _, context, contextReached, encapsulated, _, rfl⟩ := reached
  exact sourcePreOpaqueL_inherit P setup codec checks ensureInit supplied decision work runtime count selected index
    chosen n bounded context contextReached

end Start

/-! ### Weights of the logged interfaces -/

section Weights

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The logged grouped interface: the classical weight `wG`, except a private-pool request, which weighs its pool weight, and `96 + encapsCost` for the logged accept. -/
def wGL (caps : KemCaps) : (GSpecL KemSK Response).Domain → ℕ
  | .inl (.inl (.inl (.inl pool))) => wPool (KemSK := KemSK) caps pool
  | .inl query => wG (KemSK := KemSK) (Response := Response) caps query
  | .inr _ => 96 + caps.encapsCost

/-- The logged grouped weight of a classical request is at most its classical weight. -/
theorem wGL_le (caps : KemCaps) (query : (GSpec KemSK Response).Domain) :
    wGL (KemSK := KemSK) (Response := Response) caps (.inl query) ≤ wG caps query := by
  rcases query with ((pool | tail) | shared) | pending
  · exact wPool_le caps pool
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

/-- The weight of a logged-source kind: the classical source weight of a source14 kind, and 0 for the Server read. -/
def wSourceL (caps : KemCaps) : Option SourceKind → ℕ
  | some kind => wSource caps kind
  | none => 0

/-- Every step of the logged skeleton costs at most its logged grouped weight: classical requests by `PqxdhRegistrationJointKemRootCosts.skelImpl_cost` (a private-pool request forwards one pool request), the logged accept by its classical projection (`acceptStepL_fst`). -/
theorem skelImplL_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (services : Services V Response) (bills : ServiceBills services)
    (query : (GSpecL KemSK Response).Domain) (state : SkelState KemSK V) :
    WBound ((skelImplL setup codec checks identityIndex publicIdentity services query).run state) (wEnc (V := V) caps)
      (wGL caps query) := by
  rcases query with (((pool | tail) | shared) | pending) | raw
  · change WBound ((fun reply => (reply, state)) <$>
      PqxdhRegistrationJointKemPostSkeleton.encLift (KemSK := KemSK) (V := V) (.inl pool)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · exact skelImpl_cost setup codec checks caps bounded identityIndex publicIdentity services bills
      (.inl (.inl (.inr tail))) state
  · exact skelImpl_cost setup codec checks caps bounded identityIndex publicIdentity services bills (.inl (.inr shared))
      state
  · exact skelImpl_cost setup codec checks caps bounded identityIndex publicIdentity services bills (.inr pending) state
  · have classical := skelImpl_cost setup codec checks caps bounded identityIndex publicIdentity services bills
      (.inl (.inr (.accept raw))) state
    change WBound ((acceptStep (V := V) setup codec checks identityIndex publicIdentity raw).run state) _ _ at classical
    rw [← PqxdhDeploymentLaterServerItemTargets.acceptStepL_fst, wBound_map_iff] at classical
    exact classical

/-- Every logged-source request costs at most `wSourceL` of its kind on the logged grouped interface: a source14 request by `PqxdhRegistrationJointKemRootCosts.groupedClient_cost`, the raw accept by one logged accept request, and the Server read by one identity-pool reveal, which weighs 0. -/
theorem groupedClientL_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) (caps : KemCaps)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    WBound ((groupedClientL (Response := Response) setup codec selected challenge identityIndex query).run held)
      (wGL caps) (wSourceL caps (laterKind query)) := by
  rcases query with query | later
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      change WBound ((fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _)) _ _
      exact wBound_map _ ((wBound_query _ _ _).mpr (by
        simp [wGL, wSourceL, laterKind, wSource, sourceKind, PqxdhRegistrationSchedule.sourceKind]))
    · rw [groupedClientL_run setup codec selected challenge identityIndex query (fun raw same => accept ⟨raw, same⟩)
        held]
      refine wBound_map _ (wBound_simulate _ (wG caps) (wGL caps) (fun query => (wBound_query _ _ _).mpr
        (wGL_le caps query)) ?_)
      exact groupedClient_cost setup codec selected challenge caps query held.1
  · change WBound ((fun seed => ((seed, held.2), held)) <$>
      simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
        (groupedPoolLift (Response := Response) (.inl (.inr (.reveal identityIndex))))) _ _
    refine wBound_map _ ?_
    change WBound (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
      (((GSpec KemSK Response).query (.inl (.inl (.inl (.inl (.inr (.reveal identityIndex)))))) :
        OracleComp (GSpec KemSK Response) _))) _ _
    rw [simulateQ_spec_query]
    exact (wBound_query _ _ _).mpr (by simp [wGL, wSourceL, laterKind, wPool, PqxdhDynamicIdentityPool.IsCreate,
      PqxdhDynamicIdentityPool.IsUniform])

end Weights

/-! ### The logged postchallenge phase -/

section Post

open PqxdhDeploymentLaterServerOpaque (OpaqueContext)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The budget of the logged-source kinds: the source budget on source14 kinds, the read cap on the Server read. -/
def budgetL (budget : SourceKind → ℕ) (reads : ℕ) : Option SourceKind → ℕ
  | some kind => budget kind
  | none => reads

/-- The weighted logged budget is the classical weighted budget: the Server read weighs 0. -/
theorem sumL (caps : KemCaps) (budget : SourceKind → ℕ) (reads : ℕ) :
    ∑ kind, wSourceL caps kind * budgetL budget reads kind = ∑ kind, wSource caps kind * budget kind := by
  rw [Fintype.sum_option]
  simp [wSourceL, budgetL]

/-- The resumed client of the logged skeleton costs at most the Server's resumption and the weighted budget of the continuation; the Server reads weigh nothing. -/
theorem skelResumeL_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (services : Services V Response) (bills : ServiceBills services)
    (budget : SourceKind → ℕ) (reads : ℕ)
    (inherits : ∀ reply kind, (next reply).IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = kind)
      (budgetL budget reads kind)) :
    WBound (skelResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners
      log next selected ciphertext services) (wEnc (V := V) caps) (64 + ∑ kind, wSource caps kind * budget kind) := by
  unfold skelResumeL
  refine wBound_bind (wBound_run _ (wResume caps) _ (fun query state => resumeImpl_cost caps setup.hmac game.sessions
    services query state) (resume_cost setup codec checks caps bounded identityIndex publicIdentity raw value ephemeral
      _ _ game consumed) _) fun answer _ => ?_
  refine wBound_run _ (wGL caps) _ (fun query state => skelImplL_cost setup codec checks caps bounded identityIndex
    publicIdentity services bills query state) ?_ answer.2
  refine wBound_run _ (fun query => wSourceL caps (laterKind (KemSK := KemSK) query)) _ (fun query current =>
    groupedClientL_cost setup codec selected ciphertext identityIndex caps query current) ?_ _
  rw [← sumL caps budget reads]
  refine wBound_kinds laterKind (wSourceL caps) (budgetL budget reads) fun kind => ?_
  unfold PqxdhDeploymentLaterServerCut.tagged
  rw [isQueryBoundP_map_iff]
  exact inherits answer.1 kind

/-- The logged skeleton's postchallenge phase costs, in the skeleton's weight, at most the Server's resumption and the weighted budget of the continuation at the cut. -/
theorem postSkelL_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (bills : ServiceBills services) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (budget : SourceKind → ℕ) (reads : ℕ)
    (inherits : ∀ kind, InheritsL (fun query => laterKind (KemSK := KemSK) query = kind) (budgetL budget reads kind)
      context) :
    WBound (postSkelL setup codec checks decision count selected services chosen challenge context) (wSkel (V := V))
      (64 + ∑ kind, wSource caps kind * budget kind) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkelL]
    split
    · refine wBound_map _ (lower_cost setup caps bounded _ _ _ _ _ _ ?_ _)
      exact skelResumeL_cost setup codec checks caps bounded _ _ _ raw value ephemeral consumed native.2 owners log next
        selected.val challenge services bills budget reads fun reply kind => inherits kind reply
    · trivial

end Post

/-! ### The logged prefix -/

section Prefix

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The logged stopped-source prefix up to the selected raw accept draws at most the classical `preBill`: it is the evaluated prephase of the KEM adversary at the logged exposure (`PqxdhDeploymentLaterServerKemHop.pre_source`, `PqxdhDeploymentLaterServerOpaque.pre_opaque`), whose allowances are those of `PqxdhDeploymentLaterServerBills.pre_uniform`, `pre_base` and `pre_decapsulations`. -/
theorem sourcePreOpaqueL_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (chosen : MlKem768PublicKey × KemSK) :
    (PqxdhDeploymentLaterServerOpaque.sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index chosen).IsTotalQueryBound
      (preBill caps qInit supplied count budget) := by
  have total := PqxdhPrivateRootGameBudgets.evalKem_uniform_bound setup.baseImpl setup.kem chosen.2 caps.baseUniform
    caps.decapsCost bounded.base (fun ciphertext => PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl
      caps.baseUniform bounded.base _ caps.decapsUniform caps.decapsBase (bounded.decapsUniform _ _)
      (bounded.decapsBase _ _))
    (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected chosen.1)
    _ _ _
    (PqxdhDeploymentLaterServerBills.pre_uniform setup codec checks caps bounded ensureInit qInit initBound supplied
      decision work budget reads certified serverReads runtime count selected index chosen.1)
    (PqxdhDeploymentLaterServerBills.pre_base setup codec checks caps bounded ensureInit supplied decision work budget
      reads certified serverReads runtime count selected index chosen.1)
    (PqxdhDeploymentLaterServerBills.pre_decapsulations setup codec checks caps bounded ensureInit supplied decision
      work budget reads certified serverReads runtime count selected index chosen.1)
  rw [PqxdhDeploymentLaterServerKemHop.pre_source, PqxdhDeploymentLaterServerOpaque.pre_opaque, IsTotalQueryBound,
    isQueryBound_map_iff] at total
  exact total

/-- G1's prefix of the logged KEM-ideal branch draws at most the classical `prefixBill`. -/
theorem sharedStartL_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsTotalQueryBound (prefixBill caps qInit supplied count budget) := by
  unfold sharedStartL prefixBill
  have encaps : ∀ key, (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)).IsTotalQueryBound
      caps.encapsCost := fun key => PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform
    bounded.base _ caps.encapsUniform caps.encapsBase (bounded.encapsUniform key) (bounded.encapsBase key)
  refine (isTotalQueryBound_bind (n₂ := preBill caps qInit supplied count budget + (caps.encapsCost + 0))
    (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded) fun chosen => ?_).mono (by omega)
  refine isTotalQueryBound_bind (sourcePreOpaqueL_total setup codec checks caps bounded ensureInit qInit initBound
    supplied decision work budget reads certified serverReads runtime count selected index chosen) fun context => ?_
  refine isTotalQueryBound_bind (encaps chosen.1) fun encapsulated => ?_
  trivial

end Prefix

/-! ### The logged root clients -/

section Clients

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The inherited per-kind bounds of the logged-source program at every outcome of the logged prefix. -/
theorem sharedStartL_kinds (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    ∀ start ∈ support (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index), ∀ kind,
      InheritsL (fun query => laterKind (KemSK := KemSK) query = kind) (budgetL budget reads kind) start.2.2.1 := by
  intro start reached kind
  refine sharedStartL_inherit (fun query => laterKind query = kind) setup codec checks ensureInit supplied decision work
    runtime count selected index _ ?_ start reached
  rcases kind with _ | kind
  · exact serverReads
  · exact certified kind

/-- Stage S8 over the logged source, the coins of the logged root client: at most `rootBillL` for every oracle answer. The Server read cap `reads` enters no bill. -/
theorem rootClientL_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index).IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin (rootBillL caps qInit supplied count budget) := by
  unfold rootClientL PqxdhRegistrationJointKemRootExpand.internalize rootBillL rootBill
  refine isQueryBoundP_bind (PqxdhCorrelatedExpandQueryBounds.rootCoins_uniform _ _ (sharedStartL_total setup codec
    checks caps bounded ensureInit qInit initBound supplied decision work budget reads certified serverReads runtime
    count selected index)) fun start reached => ?_
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  refine isQueryBoundP_of_wBound _ (w := wRoot) (fun query coin => ?_) ?_
  · rcases query with _ | _
    · exact le_rfl
    · exact coin.elim
  · refine wBound_run _ wSkel wRoot (fun query cache => publicLocal_cost query cache) ?_ start.1
    rw [← source_sum]
    exact postSkelL_cost setup codec checks caps bounded decision count selected _
      (nativeServices_bills setup codec checks) start.2.1 start.2.2.2 start.2.2.1 budget reads
      (sharedStartL_kinds setup codec checks ensureInit supplied decision work budget reads certified serverReads
        runtime count selected index start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached))

/-- Stage S8 over the logged source, the coins of the logged factored root client: at most `rootBillL` coins for every oracle answer. -/
theorem entryClientL_coins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    WBound (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index) (wEntry 0) (rootBillL caps qInit supplied count budget) := by
  unfold entryClientL PqxdhRegistrationJointKemEntryFactor.internalizeV rootBillL rootBill
  refine wBound_bind (wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl) (wBound_of_total (sharedStartL_total setup
    codec checks caps bounded ensureInit qInit initBound supplied decision work budget reads certified serverReads
    runtime count selected index))) fun start reached => ?_
  rw [StateT.run'_eq]
  refine wBound_map _ (wBound_run _ wSkel (wEntry 0) (fun query cache => publicLocalV_cost query cache) ?_ start.1)
  rw [← source_sum]
  exact postSkelL_cost setup codec checks caps bounded decision count selected _
    (factoredServices_bills setup codec checks) start.2.1 start.2.2.2 start.2.2.1 budget reads
    (sharedStartL_kinds setup codec checks ensureInit supplied decision work budget reads certified serverReads runtime
      count selected index start (OracleComp.mem_support_of_mem_support_liftComp _ _ start reached))

/-- Stage S8 over the logged source, the distinguisher of entry 0: every run draws at most `rootBillL + 64`. -/
theorem entryDL_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (entryDL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
      value).IsTotalQueryBound (rootBillL caps qInit supplied count budget + 64) := by
  have coins := entryClientL_coins (Reader := Reader) setup codec checks caps bounded ensureInit qInit initBound
    supplied decision work budget reads certified serverReads runtime count selected index
  have weighted : WBound (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index) (wTable2 0) (rootBillL caps qInit supplied count budget) :=
    wBound_weight_mono (fun query => by rcases query with _ | _ <;> exact le_rfl) coins
  exact table_total (PqxdhRegistrationJointKemEntryFactor.firstTable value
      (PqxdhServerAuthKeySchedule.fromRoot setup.source <$> ($ᵗ PqxdhSecretInputKdf.RootOutput))) 32
    (firstTable_step value _ 32 (rootSample_total setup.source)) _ _ 2 weighted
    (entryClientL_two setup codec checks ensureInit supplied decision work runtime count selected index) (∅, none)

/-- Stage S8 over the logged source, the distinguishers of stage S7: every run of `entryDkL k` draws at most `rootBillL + 216`. -/
theorem entryDkL_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (k : ℕ)
    (value : PqxdhServerAuthKeySchedule.Output) :
    (entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index k
      value).IsTotalQueryBound (rootBillL caps qInit supplied count budget + 216) := by
  have coins := entryClientL_coins (Reader := Reader) setup codec checks caps bounded ensureInit qInit initBound
    supplied decision work budget reads certified serverReads runtime count selected index
  have weighted : WBound (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index) (wTable2 0) (rootBillL caps qInit supplied count budget) :=
    wBound_weight_mono (fun query => by rcases query with _ | _ <;> exact le_rfl) coins
  exact table_total (PqxdhRegistrationJointKemSecondEntry.indexedImpl
      (PqxdhRegistrationJointKemSecondEntry.pin k value (PqxdhRegistrationJointKemSecondEntry.sampler setup.source k)))
    108 (indexedTable_step _ 108 (pinned_total setup.source k value)) _ _ 2 weighted
    (entryClientL_two setup codec checks ensureInit supplied decision work runtime count selected index) (∅, 0)

end Clients

/-! ### The bills of the reductions -/

section Bills

open PqxdhRegistrationJointKemKeyTransfer (PrfBills)
open PqxdhServerAuthEntryFactor (EntryComponentBills)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec Handle)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The PRF reductions of stages S2 and T over the logged source at every slot: one challenge query, at most `rootBillL + 64 · 2` local uniform queries, and at most `64 + rootBillL + 64 · 2` draws in each of their two games. -/
theorem prfL_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (slot : ℕ) :
    PrfBills setup.hmac (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
      count selected index) slot (rootBillL caps qInit supplied count budget) := by
  have coins := rootClientL_coins (Reader := Reader) setup codec checks caps bounded ensureInit qInit initBound supplied
    decision work budget reads certified serverReads runtime count selected index
  have roots := rootClientL_two (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index
  have queries := PqxdhCorrelatedExpandQueryBounds.indexed_bounds setup.hmac _ slot _ _ coins roots
  have games := PqxdhCorrelatedExpandQueryBounds.indexed_uniform_ledger setup.hmac _ slot _ _ coins roots
  exact ⟨queries.2, queries.1, games.1, games.2⟩

/-- The bills of theorem T7 over the logged source: every reduction of its bound with its challenge-query counts and its complete bills, from the logged source budget, a Server-read cap that enters no bill, `KemBound setup caps` and `initBound`. -/
theorem idealKeysL_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClientL (Reader := Reader) setup codec checks ensureInit
      supplied decision work runtime count selected index) slot (rootBillL caps qInit supplied count budget)) ∧
    EntryComponentBills setup.source setup.hmac (entryDL (Reader := Reader) setup codec checks ensureInit supplied
      decision work runtime count selected index) (rootBillL caps qInit supplied count budget + 64) :=
  ⟨fun slot _ => prfL_bills setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget
      reads certified serverReads runtime count selected index slot,
    PqxdhServerAuthEntryFactor.entry_component_bills setup.source setup.hmac _ _ fun value =>
      entryDL_total setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget reads
        certified serverReads runtime count selected index value⟩

/-- The bills of the U-L1 loss `slotLossL`: the two PRF reductions of `rootClientL` and the four key-schedule reductions on each of `entryDkL 0` and `entryDkL 1`, with their challenge-query counts and complete bills at the frozen coin bill `rootBillL`, from the logged source budget, a Server-read cap that enters no bill, `KemBound setup caps` and `initBound`. -/
theorem laterSlot_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (budget : SourceKind → ℕ) (reads : ℕ)
    (certified : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some kind)
      (budget kind))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClientL (Reader := Reader) setup codec checks ensureInit
      supplied decision work runtime count selected index) slot (rootBillL caps qInit supplied count budget)) ∧
    ∀ k ∈ Finset.range 2, EntryComponentBills setup.source setup.hmac (entryDkL (Reader := Reader) setup codec checks
      ensureInit supplied decision work runtime count selected index k)
      (rootBillL caps qInit supplied count budget + 216) :=
  ⟨fun slot _ => prfL_bills setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget
      reads certified serverReads runtime count selected index slot,
    fun k _ => PqxdhServerAuthEntryFactor.entry_component_bills setup.source setup.hmac _ _ fun value =>
      entryDkL_total setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget reads
        certified serverReads runtime count selected index k value⟩

/-- The bills of `slotLossL` at the compiled LQ-F program and the per-target decision of `later_slots_two`, at the transported caps `laterTransported bounds budget post` (`compile_server_certified`) and the Server-read cap 1 (`compile_server_reads`), which enters no bill. -/
theorem laterSlot_bills_compiled {Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (checks : Checks) (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (post : PostBudget)
    (postRespects : ∀ output reveal, post.Respects (second output reveal))
    (event : PqxdhDeploymentKemTransfer.Observed Out → Bool)
    (claim : PqxdhDeploymentKemTransfer.Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) :
    (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClientL (Reader := Reader) setup codec checks ensureInit none
      (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
      budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val) slot
      (rootBillL caps qInit none budget.create (laterTransported bounds budget post))) ∧
    ∀ k ∈ Finset.range 2, EntryComponentBills setup.source setup.hmac (entryDkL (Reader := Reader) setup codec checks
      ensureInit none
      (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
      budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val k)
      (rootBillL caps qInit none budget.create (laterTransported bounds budget post) + 216) :=
  laterSlot_bills setup codec checks caps bounded ensureInit qInit initBound none
    (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
    (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second)
    (laterTransported bounds budget post) 1
    (PqxdhDeploymentLaterServerCompileBudget.compile_server_certified setup codec route bounds mode first second budget
      respects post postRespects)
    (PqxdhDeploymentLaterServerCompileBudget.compile_server_reads setup codec route bounds mode first second) runtime
    budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val

end Bills

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.inheritL_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.inheritL_forward

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.scanL_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.scanL_inherit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.commandsL_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.commandsL_inherit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.opaqueScanL_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.opaqueScanL_inherit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sourcePreOpaqueL_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sourcePreOpaqueL_inherit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_inherit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_inherit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.wGL_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.wGL_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.skelImplL_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.skelImplL_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.groupedClientL_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.groupedClientL_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sumL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sumL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.skelResumeL_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.skelResumeL_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.postSkelL_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.postSkelL_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sourcePreOpaqueL_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sourcePreOpaqueL_total

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_total

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_kinds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.sharedStartL_kinds

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.rootClientL_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.rootClientL_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryClientL_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryClientL_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryDL_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryDL_total

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryDkL_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.entryDkL_total

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.prfL_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.prfL_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.idealKeysL_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.idealKeysL_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.laterSlot_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.laterSlot_bills

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.laterSlot_bills_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemBills.laterSlot_bills_compiled
