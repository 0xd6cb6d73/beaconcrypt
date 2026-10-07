-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentKeyMatch
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge

/-! Freshness of the compiled program (CE-5, `approved_goodkem` and `kernel_reads_unrevealed` over the complete interface). In the annotated initialized source14 execution that the KEM, root and report theorems are stated for, every step other than an identity-field read or a KEM-field read appends to the private identity and KEM transcripts only creation, signing, static DH and decapsulation observations: Server birth and Beacon creation record creations, a bundle records its three signatures, an accept and a finish record static DH requests and a finish records its decapsulation; Server commands, coins, prekey, one-time and kernel reads and the Server kernel reveal leave both pools unchanged. Hence a program with zero identity-read and zero KEM-read caps, such as the compiled program of any complete-interface adversary in either mode and its tagged form used by T4, ends every run with no reveal observation in either pool: `GoodKem` holds for every KEM creation index, and `revealedAt` is false for every identity index. No assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentQuiet
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhJointGapDh
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Result : Type}

/-- An identity-pool observation that discloses a seed. -/
def identityReveal : PqxdhDynamicIdentityPool.Observation → Bool
  | ⟨.inr (.reveal _), _⟩ => true
  | _ => false

/-- A KEM-pool observation that discloses a secret key. -/
def kemReveal : PqxdhLiveKemBirth.Observation KemSK → Bool
  | ⟨.reveal _, _⟩ => true
  | _ => false

/-- Neither private pool has recorded a disclosure. -/
def Quiet (pool : PqxdhRegistrationJointPreparation.Pool KemSK) : Prop :=
  pool.1.transcript.any identityReveal = false ∧ pool.2.transcript.any kemReveal = false

/-- Recording a non-reveal identity observation keeps the pools quiet. -/
theorem quiet_identity (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (query : PqxdhDynamicIdentityPool.DynamicSpec.Domain) (answer : PqxdhDynamicIdentityPool.DynamicSpec.Range query)
    (state : PqxdhDynamicIdentityPool.SourceState) (quiet : Quiet pool) (kept : state.transcript = pool.1.transcript)
    (notReveal : identityReveal ⟨query, answer⟩ = false) :
    Quiet (PqxdhDynamicIdentityPool.record query answer state, pool.2) := by
  refine ⟨?_, quiet.2⟩
  simp only [PqxdhDynamicIdentityPool.record, List.any_append, kept, quiet.1, List.any_cons, List.any_nil, notReveal,
    Bool.or_false]

/-- Recording a non-reveal KEM observation keeps the pools quiet. -/
theorem quiet_kem (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (query : PqxdhLiveKemBirth.Query)
    (answer : PqxdhLiveKemBirth.Range KemSK query) (state : PqxdhLiveKemBirth.Pool KemSK) (quiet : Quiet pool)
    (kept : state.transcript = pool.2.transcript) (notReveal : kemReveal ⟨query, answer⟩ = false) :
    Quiet (pool.1, PqxdhLiveKemBirth.record query answer state) := by
  refine ⟨quiet.1, ?_⟩
  simp only [PqxdhLiveKemBirth.record, List.any_append, kept, quiet.2, List.any_cons, List.any_nil, notReveal,
    Bool.or_false]

/-- Beacon creation records one identity creation and one KEM creation. -/
theorem quiet_create (setup : Setup baseSpec KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (material : PqxdhRegistrationJointCreation.Material KemSK) (quiet : Quiet pool) :
    Quiet (PqxdhRegistrationJointCreation.serviceView setup pool material).2 := by
  obtain ⟨identityQuiet, kemQuiet⟩ := quiet
  refine ⟨?_, ?_⟩ <;>
    simp [PqxdhRegistrationJointCreation.serviceView, PqxdhDynamicIdentityPool.createdReply, PqxdhLiveKemBirth.created,
      PqxdhDynamicIdentityPool.record, PqxdhLiveKemBirth.record, identityReveal, kemReveal, identityQuiet, kemQuiet]

/-- A bundle records exactly its three signatures, or nothing. -/
theorem quiet_bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat)
    (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (quiet : Quiet pool)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec identityIndex owner pool.1)) :
    Quiet (result.2, pool.2) := by
  have after : ∀ generated,
      Quiet ((PqxdhRegistrationJointBundle.after setup codec identityIndex owner generated pool.1).2, pool.2) := by
    intro generated
    unfold PqxdhRegistrationJointBundle.after
    split
    · exact quiet
    · obtain ⟨identityQuiet, kemQuiet⟩ := quiet
      dsimp only
      split <;> refine ⟨?_, kemQuiet⟩ <;>
        simp [PqxdhJointPhase1SourceWriter.signedState, PqxdhJointPhase1SourceWriter.recordSign,
          PqxdhDynamicIdentityPool.record, identityReveal, identityQuiet]
  unfold PqxdhRegistrationJointBundle.trace at supported
  split at supported
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨scalar, _, rfl⟩ := supported
    exact after (some scalar)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact after none
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact quiet

/-- An auxiliary Server prefix callback keeps both pools. -/
theorem onAux_pool {State Value : Type} (work : StateT State ProbComp Value)
    (current : PqxdhRegistrationJointServerPrefix.State KemSK State) (reached : Value × PqxdhRegistrationJointServerPrefix.State KemSK State)
    (member : reached ∈ support ((PqxdhRegistrationJointServerPrefix.onAux work).run current)) : reached.2.1 = current.1 := by
  simp only [PqxdhRegistrationJointServerPrefix.onAux, StateT.run, support_map, Set.mem_image] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

/-- The Server's raw-accept prefix records only static DH requests in the identity pool. -/
theorem quiet_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointFinish.State KemSK) (quiet : Quiet state.1) (result : Option Nat ×
      PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex
      raw).run state)) :
    Quiet result.2.1 := by
  have prefixQuiet : ∀ (start : PqxdhRegistrationJointServerPrefix.State KemSK (List Pqxdh.Bytes)), Quiet start.1 →
      ∀ reached ∈ support ((simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
        (serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run start), Quiet reached.2.1 := by
    intro start startQuiet
    refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _ (fun current => Quiet current.1) ?_ _
      start startQuiet
    intro query current currentQuiet reached member
    cases query with
    | staticDh input =>
        simp only [PqxdhRegistrationJointServerPrefix.annotated, PqxdhServerStaticDhSource.nativeImpl, StateT.run_bind,
          mem_support_bind_iff] at member
        obtain ⟨_, visited, rfl⟩ := member
        change _ ∈ support (pure _ : ProbComp _) at visited
        rw [support_pure, Set.mem_singleton_iff] at visited
        subst visited
        obtain ⟨identityQuiet, kemQuiet⟩ := currentQuiet
        refine ⟨?_, kemQuiet⟩
        simp [PqxdhDynamicIdentityPool.record, identityReveal, identityQuiet]
    | _ =>
        rw [onAux_pool _ current reached member]
        exact currentQuiet
  simp only [PqxdhRegistrationJointServerAccept.source, PqxdhRegistrationJointServerAccept.run, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨_, afterGet⟩, getMember, ⟨collected, afterPrepare⟩, prepareMember, tailMember⟩ := supported
  simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, support_map, Set.mem_image] at getMember tailMember
  obtain ⟨_, _, getEq⟩ := getMember
  obtain ⟨_, _, rfl⟩ := tailMember
  simp only [Prod.mk.injEq] at getEq
  obtain ⟨_, rfl⟩ := getEq
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, support_map, Set.mem_image] at prepareMember
  obtain ⟨reached, reachedMember, same⟩ := prepareMember
  simp only [Prod.mk.injEq] at same
  obtain ⟨_, rfl⟩ := same
  exact prefixQuiet _ quiet reached reachedMember

/-- A finish records only its decapsulation and static DH requests. -/
theorem quiet_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex kemIndex : Nat)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : PqxdhRegistrationJointFinish.State KemSK)
    (quiet : Quiet state.1)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhRegistrationJointFinish.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointFinish.annotated setup codec identityIndex kemIndex)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state)) :
    Quiet result.2.1 := by
  refine OracleComp.simulateQ_run_preserves_inv_of_query (spec' := unifSpec) _ (fun current => Quiet current.1) ?_ _
    state quiet result supported
  intro query current currentQuiet reached member
  rcases query with query | query
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onPool, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    obtain ⟨identityQuiet, kemQuiet⟩ := currentQuiet
    cases query with
    | decapsulate ciphertext key =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        refine ⟨identityQuiet, ?_⟩
        simp [PqxdhLiveKemBirth.record, kemReveal, kemQuiet]
    | dhIdentity seed point =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        refine ⟨?_, kemQuiet⟩
        simp [PqxdhDynamicIdentityPool.record, identityReveal, identityQuiet]
    | _ =>
        simp only [PqxdhRegistrationJointPreparation.annotated, support_map, Set.mem_image] at innerMember
        obtain ⟨_, _, rfl⟩ := innerMember
        exact ⟨identityQuiet, kemQuiet⟩
  · simp only [PqxdhRegistrationJointFinish.annotated, PqxdhRegistrationJointFinish.onNative, StateT.run, support_map,
      Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact currentQuiet

/-- Every annotated source step other than an identity-field or KEM-field read keeps both pools quiet. -/
theorem quiet_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notIdentity : sourceKind query ≠ .inr 0) (notKem : sourceKind query ≠ .inr 1)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (quiet : Quiet state.pool)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex
      query).run state)) :
    Quiet result.2.pool := by
  have sharedQuiet : ∀ {Value : Type} (work : NativeGame KemSK Value)
      (reached : Value × PqxdhRegistrationJointSchedule.State KemSK),
      reached ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) → Quiet reached.2.pool := by
    intro Value work reached member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨_, _, rfl⟩ := member
    exact quiet
  rcases query with request | ⟨index, field⟩
  · rcases request with coin | command
    · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
        PqxdhRegistrationJointSchedule.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact quiet
    · cases command with
      | create pin keyId =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create, StateT.run, support_map,
            Set.mem_image] at supported
          obtain ⟨material, _, rfl⟩ := supported
          exact quiet_create setup state.pool material quiet
      | bundle address =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact quiet
          · rename_i entry _
            simp only [support_map, Set.mem_image] at supported
            obtain ⟨traced, tracedMember, rfl⟩ := supported
            exact quiet_bundle setup codec entry.identityIndex entry.owner state.pool quiet traced tracedMember
      | accept raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointServerSchedule.onBackend,
            StateT.run, support_map, Set.mem_image] at supported
          obtain ⟨accepted, acceptedMember, rfl⟩ := supported
          exact quiet_accept setup codec checks seed identityIndex raw (state.pool, state.shared) quiet accepted
            acceptedMember
      | build session payload => exact sharedQuiet _ result supported
      | finish address raw =>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run] at supported
          split at supported
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact quiet
          · rename_i entry _
            simp only [support_map, Set.mem_image] at supported
            obtain ⟨finished, finishedMember, rfl⟩ := supported
            exact quiet_finish setup codec entry.identityIndex entry.kemIndex raw entry.owner (state.pool, state.shared)
              quiet finished finishedMember
      | hmac key message => exact sharedQuiet _ result supported
      | hash bytes => exact sharedQuiet _ result supported
      | reveal keyId => exact sharedQuiet _ result supported
  · simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
      support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [PqxdhRegistrationJointLiveRead.sourceStep]
    split
    · exact quiet
    · rename_i entry _
      cases field with
      | identity => exact absurd rfl notIdentity
      | kem => exact absurd rfl notKem
      | prekey => exact quiet
      | oneTime => exact quiet
      | kernel => exact quiet

/-- A program with zero identity-read and zero KEM-read caps keeps both pools quiet along its whole annotated run. -/
theorem quiet_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (noIdentity : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 0) 0)
    (noKem : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 1) 0)
    (state : PqxdhRegistrationJointSchedule.State KemSK) (quiet : Quiet state.pool)
    (result : Result × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointServerSchedule.source setup codec checks seed
      identityIndex) program).run state)) :
    Quiet result.2.pool := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact quiet
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noIdentity noKem
      obtain ⟨identityAllowed, identityRest⟩ := noIdentity
      obtain ⟨kemAllowed, kemRest⟩ := noKem
      have notIdentity : sourceKind (KemSK := KemSK) query ≠ .inr 0 := by
        rcases identityAllowed with free | impossible
        · exact free
        · omega
      have notKem : sourceKind (KemSK := KemSK) query ≠ .inr 1 := by
        rcases kemAllowed with free | impossible
        · exact free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, middle⟩, first, second⟩ := supported
      have middleQuiet := quiet_step setup codec checks seed identityIndex query notIdentity notKem state quiet _ first
      have identityNext := identityRest reply
      have kemNext := kemRest reply
      simp only [notIdentity, notKem, ite_false] at identityNext kemNext
      exact ih reply identityNext kemNext middle middleQuiet second

/-- Server birth records at most one identity creation. -/
theorem quiet_birth (joint : Primitives) (ensureInit : StateT A ProbComp Bool) (sender : Std.U64)
    (supplied : Option Pqxdh.Bytes) (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (quiet : Quiet state.1)
    (result : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : result ∈ support ((PqxdhRegistrationJointServerBirth.source joint ensureInit sender supplied).run
      state)) :
    Quiet result.2.1 := by
  simp only [PqxdhRegistrationJointServerBirth.source, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨born, _, rfl⟩ := supported
  obtain ⟨identityQuiet, kemQuiet⟩ := quiet
  rcases born with ⟨_ | created, runtime⟩
  · exact ⟨identityQuiet, kemQuiet⟩
  · refine ⟨?_, kemQuiet⟩
    simp only [PqxdhRegistrationJointServerBirth.install]
    split <;> simp [PqxdhDynamicIdentityPool.record, identityReveal, identityQuiet]

/-- A program with zero identity-read and zero KEM-read caps leaves both pools quiet at the end of its whole initialized annotated execution, from quiet pools. -/
theorem quiet_initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (noIdentity : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 0) 0)
    (noKem : program.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 1) 0)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (quiet : Quiet state.1)
    (result : Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : result ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit
      supplied program).run state)) :
    Quiet result.2.1 := by
  simp only [PqxdhRegistrationJointInitializedSchedule.source, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  have bornQuiet := quiet_birth setup.joint ensureInit setup.serverKeyId supplied state quiet born bornMember
  rcases born with ⟨_ | created, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact bornQuiet
  · simp only [support_map, Set.mem_image] at supported
    obtain ⟨executed, executedMember, rfl⟩ := supported
    exact quiet_run setup codec checks created.seed _ program noIdentity noKem _ bornQuiet executed executedMember

/-- A quiet KEM pool has disclosed no creation index. -/
theorem goodKem_of_quiet {count : Nat} (kemIndex : Fin count) (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A X)
    (quiet : Quiet final.2.1) : PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex final := by
  unfold PqxdhRegistrationJointKemRawBridge.GoodKem
  rw [List.any_eq_false]
  intro observation member disclosed
  have revealed : kemReveal observation = true := by
    rcases observation with ⟨query, answer⟩
    cases query <;> simp_all [PqxdhDynamicKemStopping.disclosed, kemReveal]
  have none := List.any_eq_false.mp quiet.2 observation member
  exact none revealed

/-- A quiet identity pool has revealed no identity index. -/
theorem unrevealed_of_quiet (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (quiet : Quiet pool) (index : Nat) :
    PqxdhRegistrationJointRoutedReveals.revealedAt index pool.1.transcript = false := by
  unfold PqxdhRegistrationJointRoutedReveals.revealedAt
  rw [List.any_eq_false]
  intro observation member revealed
  have flagged : identityReveal observation = true := by
    rcases observation with ⟨query, answer⟩
    rcases query with coin | (_ | ⟨_, _⟩ | _) <;> simp_all [PqxdhRegistrationJointRoutedReveals.revealAt, identityReveal]
  have none := List.any_eq_false.mp quiet.1 observation member
  exact none flagged

/-- The initial private pools of the KEM theorems are quiet. -/
theorem quiet_empty : Quiet ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty) :
    PqxdhRegistrationJointPreparation.Pool KemSK) :=
  ⟨rfl, rfl⟩

/-- The compiled program of a complete-interface adversary that respects a budget, in either mode, and its tagged form at any raw-accept ordinal issue no identity-field and no KEM-field read. -/
theorem compiled_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (budget : PqxdhDeploymentInterface.Budget) (respects : budget.Respects adversary) (index : Nat) :
    (PqxdhRegistrationJointAcceptCutTag.tag (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
      adversary) index).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 0) 0 ∧
    (PqxdhRegistrationJointAcceptCutTag.tag (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
      adversary) index).IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inr 1) 0 :=
  ⟨PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ 0
      (PqxdhDeploymentCompileSecrecy.compile_full_no_secret_read setup codec route bounds mode adversary budget respects 0
        (by decide)),
    PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ 0
      (PqxdhDeploymentCompileSecrecy.compile_full_no_secret_read setup codec route bounds mode adversary budget respects 1
        (by decide))⟩

/-- `approved_goodkem`: in the actual initialized execution that T4 is stated for, the tagged compiled program of a complete-interface adversary that respects a budget, in either mode and at any raw-accept ordinal, ends every run with no KEM key disclosed: `GoodKem` holds for every creation index. -/
theorem approved_goodkem (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (index : Nat) (runtime : A) {count : Nat} (kemIndex : Fin count)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A
      ((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local))
    (supported : final ∈ support ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome
      setup), result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied
        (PqxdhRegistrationJointAcceptCutTag.tag (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode
          adversary) index)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex final := by
  rw [support_map] at supported
  obtain ⟨result, member, rfl⟩ := supported
  obtain ⟨noIdentity, noKem⟩ := compiled_unread setup codec route bounds mode adversary budget respects index
  exact goodKem_of_quiet kemIndex _
    (quiet_initialized setup codec checks ensureInit supplied _ noIdentity noKem _ quiet_empty result member)

/-- `kernel_reads_unrevealed`: in the same execution, the compiled program's Server kernel reveals and established-kernel reads, its only field reads, leave the identity-reveal history empty: no identity index is ever revealed. -/
theorem kernel_reads_unrevealed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (index : Nat) (runtime : A)
    (result : Option (PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      (((X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentCompile.Local) × PqxdhRegistrationJointAcceptCutTag.Tag)) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A)
    (supported : result ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit
      supplied (PqxdhRegistrationJointAcceptCutTag.tag (PqxdhDeploymentCompileSecrecy.compileFull setup codec route
        bounds mode adversary) index)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (identityIndex : Nat) :
    PqxdhRegistrationJointRoutedReveals.revealedAt identityIndex result.2.1.1.transcript = false := by
  obtain ⟨noIdentity, noKem⟩ := compiled_unread setup codec route bounds mode adversary budget respects index
  exact unrevealed_of_quiet _ (quiet_initialized setup codec checks ensureInit supplied _ noIdentity noKem _
    quiet_empty result supported) identityIndex

end BeaconcryptCore.Computational.PqxdhDeploymentQuiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_kem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_kem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_create' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.onAux_pool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.onAux_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_accept

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_birth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_birth

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_initialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.goodKem_of_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.goodKem_of_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.unrevealed_of_quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.unrevealed_of_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.quiet_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.compiled_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.compiled_unread

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.approved_goodkem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.approved_goodkem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentQuiet.kernel_reads_unrevealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentQuiet.kernel_reads_unrevealed
