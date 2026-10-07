-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerOpaque
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBills

/-! LQ-F: query bills of the KEM adversary at the logged exposure. The logged command run is the simulation of one flattened exposed handler (`exposed`, `run_exposed`). Every source14 request of that handler has the four bills (generated identities, logical decapsulations, uniform work, exposed encapsulations) of the same request in the existing exposed command compiler (`exposed_source`, through `LaterServerCommands.query_embed` and `KemProgramBills.commands` on the one-request program), and the Server read has none: it is one identity-pool reveal, which is neither a creation, a decapsulation, uniform work nor an encapsulation (`exposed_later`). The weighted composition `FinitePartitionQueryBounds.weighted_bound` over the request kinds of the logged source then gives the logged command program the bills of `KemProgramBills.commands` on the source14 requests of the program, for any finite cap on the Server reads (`commands_bills`, with `weighted`, `single_sum` and the linearity `total_single` of the native uniform allowance). The rest follows `KemRawBills` with the logged definitions: the logged `exposeAt` hides every encapsulation of the fully exposed logged program except the selected one (`exposeAt_hides`) and issues at most one exposed encapsulation (`accept_bound`, `exposeAt_bound`), so it has the four allowances of `KemRawBills.exposeAt_bills` (`exposeAt_bills`); the generic prephase of the KEM hop supplies the saved continuation certificates (`pre_bound`, `saved`), and the proof-carrying adversary at the logged exposure has exactly the caps of `KemRawBills.adversary_bound` (`scan_bills`, `pre_uniform`, `pre_excluded`, `pre_decapsulations`, `pre_base`, `annotated_bound`, `adversary_post`, `adversary_bound`). The Server reads add nothing to any bill; their cap is a premise only because `weighted_bound` needs a cap for every request kind, and it enters no conclusion. No assumption is added; `KemBound` and the initializer bill are the existing uniform-bill premises. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (Outcome Budget)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemCutBounds (Count Residual)
open PqxdhRegistrationJointKemExposedCounts (IsEncapsulation)
open PqxdhRegistrationJointKemProgramBills (Bounds)
open PqxdhDynamicKemJointBounds (IsIdentityCreate IsDecapsulation IsUniform)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhDeploymentLaterServerSource (Log Spec)
open PqxdhDeploymentLaterServerCommands (Local impl commands)
open PqxdhDeploymentLaterServerReserve (laterKind)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R Result : Type}

/-- The exposed logged command handler with owners, log and native state flattened into one state. -/
noncomputable def exposed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (Spec KemSK)
      (StateT (Local × NativeState KemSK) (OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK))) :=
  fun query state => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((impl setup codec checks identityIndex publicIdentity query).run state.1).run state.2

/-- One step of the flattened exposed handler. -/
theorem exposed_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (query : (Spec KemSK).Domain)
    (state : Local × NativeState KemSK) :
    (exposed setup codec checks identityIndex publicIdentity query).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((impl setup codec checks identityIndex publicIdentity query).run state.1).run state.2 := rfl

/-- The logged run is the simulation of the flattened exposed handler. -/
theorem run_exposed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) Result)
    (held : Local) (state : NativeState KemSK) :
    PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work held.1 held.2 state =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (exposed setup codec checks identityIndex publicIdentity) work).run (held, state) := by
  induction work using OracleComp.inductionOn generalizing held state with
  | pure value => simp [PqxdhDeploymentLaterServerCommands.run]
  | query_bind query next ih =>
    simp only [PqxdhDeploymentLaterServerCommands.run] at ih ⊢
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, exposed_run, bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 result.2

/-- The budget of a single source14 request of the given kind. -/
def single (kind : PqxdhRegistrationJointRevealCosts.SourceKind) : Budget := fun source => if kind = source then 1 else 0

/-- Every source14 request of the flattened exposed handler has the four bills of the same request in the existing exposed command compiler. -/
theorem exposed_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (held : Local) (state : NativeState KemSK) :
    Bounds ((exposed setup codec checks identityIndex publicIdentity (.inl query)).run (held, state))
      (single (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query) (.inl 1))
      (single (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query) (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps
        (single (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query)))
      (single (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query) (.inl 3)) := by
  have embedded := PqxdhDeploymentLaterServerCommands.query_embed setup codec checks identityIndex publicIdentity query
    held.1 held.2 state
  have one := PqxdhRegistrationJointKemProgramBills.commands setup codec checks caps bounded identityIndex
    publicIdentity ((PqxdhRegistrationJointKemCommands.SourceSpec KemSK).query query)
    (single (PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query))
    (fun source => by
      rw [isQueryBoundP_query_iff]
      simp only [single]
      split_ifs with same <;> simp [same])
    held.1 state
  simp only [PqxdhRegistrationJointKemEncapsulation.commands, simulateQ_spec_query] at one
  rw [← embedded] at one
  rw [exposed_run]
  obtain ⟨creates, decaps, uniform, encaps⟩ := one
  exact ⟨by simpa only [isQueryBoundP_map_iff] using creates, by simpa only [isQueryBoundP_map_iff] using decaps,
    by simpa only [isQueryBoundP_map_iff] using uniform, by simpa only [isQueryBoundP_map_iff] using encaps⟩

/-- The Server read issues one identity-pool reveal and no counted request: no generated identity, no decapsulation, no uniform work and no exposed encapsulation. -/
theorem exposed_later (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (read : Unit) (held : Local) (state : NativeState KemSK) :
    Bounds ((exposed setup codec checks identityIndex publicIdentity (.inr read)).run (held, state)) 0 0 0 0 := by
  rw [exposed_run]
  change Bounds ((fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun seed => (((seed, held.2), held), state)) <$>
      ((PqxdhRegistrationJointKemEncapsulation.Spec KemSK).query (.inl (.inl (.inr (.reveal identityIndex)))) :
        OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) _))) 0 0 0 0
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff] <;>
    simp [Count, IsIdentityCreate, IsDecapsulation, IsUniform, IsEncapsulation, PqxdhDynamicIdentityPool.IsCreate,
      PqxdhDynamicIdentityPool.IsUniform]

/-- The per-request cost of a logged-source request: the source14 component for a source14 kind and nothing for the Server read (kind `none`). -/
def cost (component : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) :
    Option PqxdhRegistrationJointRevealCosts.SourceKind → Nat
  | some kind => component kind
  | none => 0

/-- The weighted bill of a logged-source budget is the source14 bill: the Server read costs nothing, whatever its cap `reads`. -/
theorem weighted (component : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) (budget : Budget) (reads : Nat) :
    ∑ kind : Option PqxdhRegistrationJointRevealCosts.SourceKind, cost component kind * kind.elim reads budget =
      ∑ kind, component kind * budget kind := by
  rw [Fintype.sum_option]
  simp [cost]

/-- A single coordinate is selected by the weighted sum of the single-request budgets. -/
theorem single_sum (target : PqxdhRegistrationJointRevealCosts.SourceKind) (budget : Budget) :
    ∑ kind, single kind target * budget kind = budget target := by
  simp [single, ite_mul, Finset.sum_ite_eq']

/-- The native uniform allowance is linear in the budget: the weighted sum of the single-request allowances is the allowance of the whole budget. -/
theorem total_single (caps : KemCaps) (budget : Budget) :
    ∑ kind, PqxdhRegistrationJointOpenUniform.total caps (single kind) * budget kind =
      PqxdhRegistrationJointOpenUniform.total caps budget := by
  simp only [Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.sum_univ_zero, PqxdhRegistrationJointOpenUniform.total,
    single]
  simp
  ring

/-- The logged command program has the four bills of the existing exposed command compiler on the source14 requests of the program; the Server reads add nothing. -/
theorem commands_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (Spec KemSK) Result) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    Bounds (commands setup codec checks identityIndex publicIdentity work owners log state)
      (budget (.inl 1)) (budget (.inl 5)) (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)) := by
  have partition : ∀ kind, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = kind)
      (kind.elim reads budget) := by
    rintro (_ | kind)
    · exact serverReads
    · exact certified kind
  have compose (predicate : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain → Prop)
      [DecidablePred predicate] (component : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
      (step : ∀ query state, ((exposed setup codec checks identityIndex publicIdentity query).run state).IsQueryBoundP
        predicate (cost component (laterKind (KemSK := KemSK) query))) :
      (commands setup codec checks identityIndex publicIdentity work owners log state).IsQueryBoundP predicate
        (∑ kind, component kind * budget kind) := by
    rw [commands, isQueryBoundP_map_iff]
    rw [show PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work owners log
        state = PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work
          (owners, log).1 (owners, log).2 state from rfl, run_exposed, isQueryBoundP_map_iff, ← weighted component budget reads]
    exact FinitePartitionQueryBounds.weighted_bound (laterKind (KemSK := KemSK)) (cost component)
      (fun kind => kind.elim reads budget) (exposed setup codec checks identityIndex publicIdentity) predicate work
      partition step ((owners, log), state)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← single_sum (.inl 1) budget]
    apply compose
    rintro (query | read) ⟨held, native⟩
    · exact (exposed_source setup codec checks caps bounded identityIndex publicIdentity query held native).creates
    · exact (exposed_later setup codec checks identityIndex publicIdentity read held native).creates
  · rw [← single_sum (.inl 5) budget]
    apply compose
    rintro (query | read) ⟨held, native⟩
    · exact (exposed_source setup codec checks caps bounded identityIndex publicIdentity query held native).decaps
    · exact (exposed_later setup codec checks identityIndex publicIdentity read held native).decaps
  · rw [← total_single caps budget]
    apply compose
    rintro (query | read) ⟨held, native⟩
    · exact (exposed_source setup codec checks caps bounded identityIndex publicIdentity query held native).uniform
    · exact (exposed_later setup codec checks identityIndex publicIdentity read held native).uniform
  · rw [← single_sum (.inl 3) budget]
    apply compose
    rintro (query | read) ⟨held, native⟩
    · exact (exposed_source setup codec checks caps bounded identityIndex publicIdentity query held native).encaps
    · exact (exposed_later setup codec checks identityIndex publicIdentity read held native).encaps

open PqxdhRegistrationJointKemRawBills (Hides hides_refl hides_all hides_bind hides_bound residual_hook)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointKemChallenge (Context)
open PqxdhRegistrationJointKemCutSupport (ContextBound)
open PqxdhRegistrationJointKemPostBills (uniformCap CcaBills)

/-- The logged `exposeAt` hides every encapsulation of the fully exposed logged command program on the tagged logged program except the selected one. -/
theorem exposeAt_hides (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    Hides setup
      (PqxdhDeploymentLaterServerCut.exposeAt setup codec checks identityIndex publicIdentity observe work index owners
        log state)
      (commands setup codec checks identityIndex publicIdentity
        (observe <$> PqxdhDeploymentLaterServerCommands.tag work index) owners log state) := by
  rw [PqxdhDeploymentLaterServerCommands.tag, map_bind, commands, PqxdhDeploymentLaterServerCommands.run_bind,
    map_bind]
  unfold PqxdhDeploymentLaterServerCut.exposeAt
  apply hides_bind setup (hides_all setup _)
  rintro ⟨⟨cut, after, logAt⟩, native⟩
  cases cut with
  | complete result =>
    have same : (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
        PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
          (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (.complete result)) after logAt native =
        pure ((observe (result, none), after), native) := by
      simp [PqxdhDeploymentLaterServerCommands.tagFinish, PqxdhDeploymentLaterServerCommands.run]
    dsimp only
    rw [same]
    exact .pure _
  | pending raw next =>
    dsimp only
    rw [show (fun result => ((result.1.1, result.1.2.1), result.2)) <$>
        PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity
          (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (.pending raw next)) after logAt native =
        commands setup codec checks identityIndex publicIdentity
          (observe <$> PqxdhDeploymentLaterServerCommands.tagFinish (.pending raw next)) after logAt native from rfl,
      PqxdhDeploymentLaterServerCut.pending_commands]
    exact hides_bind setup (hides_refl setup _) (fun answer => hides_all setup _)

/-- The exposed logged accept has at most one exposed encapsulation, as the exposed accept it forgets to. -/
theorem accept_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run
      state).IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) 1 := by
  have old := PqxdhRegistrationJointKemExposedCounts.accept_bound setup codec checks identityIndex publicIdentity raw
    state
  rw [← PqxdhDeploymentLaterServerCommands.accept_fst, isQueryBoundP_map_iff] at old
  exact old

/-- The logged `exposeAt` issues at most one exposed encapsulation request on every path. -/
theorem exposeAt_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    (PqxdhDeploymentLaterServerCut.exposeAt setup codec checks identityIndex publicIdentity observe work index owners
      log state).IsQueryBoundP (IsEncapsulation (KemSK := KemSK)) 1 := by
  unfold PqxdhDeploymentLaterServerCut.exposeAt
  rw [← Nat.zero_add 1]
  apply isQueryBoundP_bind (PqxdhRegistrationJointAcceptKemCut.hide_free setup _)
  rintro ⟨⟨cut, after, logAt⟩, native⟩ _
  cases cut with
  | complete result => trivial
  | pending raw next =>
    rw [← Nat.add_zero 1]
    exact isQueryBoundP_bind (accept_bound setup codec checks identityIndex publicIdentity raw native)
      (fun answer _ => PqxdhRegistrationJointAcceptKemCut.hide_free setup _)

/-- The four exposed-program allowances of the logged `exposeAt`, exactly those of `KemRawBills.exposeAt_bills`. -/
theorem exposeAt_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R)
    (work : OracleComp (Spec KemSK) X) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (index : Nat) (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    Bounds (PqxdhDeploymentLaterServerCut.exposeAt setup codec checks identityIndex publicIdentity observe work
        index owners log state)
      (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) 1 := by
  have exposed := commands_bills setup codec checks caps bounded identityIndex publicIdentity
    (observe <$> PqxdhDeploymentLaterServerCommands.tag work index) budget reads
    (fun source => (isQueryBoundP_map_iff _ _ _).mpr
      (PqxdhDeploymentLaterServerBridge.tag_bound work index _ _ (certified source)))
    ((isQueryBoundP_map_iff _ _ _).mpr (PqxdhDeploymentLaterServerBridge.tag_bound work index _ _ serverReads))
    owners log state
  have hides := exposeAt_hides setup codec checks identityIndex publicIdentity observe work index owners log state
  constructor
  · have result := hides_bound setup
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .identityCreate) hides _ _ 0
      (by simpa only [PqxdhRegistrationJointKemProgramBills.creates_class] using exposed.creates) exposed.encaps
      (fun request => PqxdhRegistrationJointKemCutInterpreted.encaps_private setup request .identityCreate (by decide))
    simpa only [PqxdhRegistrationJointKemProgramBills.creates_class, Nat.zero_mul, Nat.add_zero] using result
  · have result := hides_bound setup
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .decapsulate) hides _ _ 0
      (by simpa only [PqxdhRegistrationJointKemProgramBills.decaps_class] using exposed.decaps) exposed.encaps
      (fun request => PqxdhRegistrationJointKemCutInterpreted.encaps_private setup request .decapsulate (by decide))
    simpa only [PqxdhRegistrationJointKemProgramBills.decaps_class, Nat.zero_mul, Nat.add_zero] using result
  · exact hides_bound setup _ hides _ _ _ exposed.uniform exposed.encaps
      (PqxdhRegistrationJointKemCutInterpreted.encaps_uniform setup caps bounded)
  · exact exposeAt_bound setup codec checks identityIndex publicIdentity observe work index owners log state

/-- The executable prephase of the generic KEM hop supplies the saved continuation allowance of every residual fact of its scanned program. -/
theorem pre_bound (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (scanned : PqxdhDeploymentLaterServerKemHop.Scanned KemSK) (runtime : A) (count : Nat) (selected : Fin (count + 1))
    (challengeKey : MlKem768PublicKey)
    (predicate : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat)
    (residual : ∀ created : PqxdhRegistrationJointServerBirth.ClientCreated Unit, ∀ cut,
      cut ∈ support (scanned created) → Residual predicate cap cut)
    (context : Context KemSK A Bool count)
    (reached : context ∈ support
      (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied scanned runtime count selected challengeKey)) :
    ContextBound predicate cap context := by
  unfold PqxdhDeploymentLaterServerKemHop.pre at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨⟨born, after⟩, _, reached⟩ := reached
  cases born with
  | none =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    trivial
  | some created =>
    rw [mem_support_bind_iff] at reached
    obtain ⟨others, _, reached⟩ := reached
    rw [mem_support_bind_iff] at reached
    obtain ⟨⟨cut, state⟩, scannedReached, reached⟩ := reached
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    cases cut with
    | none => trivial
    | some cut =>
      exact residual created cut (PqxdhRegistrationJointKemCutSupport.successful_support _ _ _ state cut scannedReached)

/-- Every valid saved context of the proof-carrying adversary at the logged exposure has all four source-derived continuation certificates, with the allowances of `KemRawBills.saved`. -/
theorem saved (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (context : PqxdhDeploymentLaterServerKemHop.Saved setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected) :
    PqxdhRegistrationJointKemSavedBills.Certificate context.2.val (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) 0 := by
  have bills (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :=
    exposeAt_bills setup codec checks caps bounded created.server.server.metadata.identityIndex
      created.publicIdentity (decideTag decision) work budget reads certified serverReads index [] []
      (PqxdhRegistrationJointInitializedAccept.initial created)
  constructor
  · exact pre_bound setup ensureInit supplied _ runtime count selected context.1 _ _
      (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).creates cut reached) context.2.val context.2.property
  · exact pre_bound setup ensureInit supplied _ runtime count selected context.1 _ _
      (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).decaps cut reached) context.2.val context.2.property
  · exact pre_bound setup ensureInit supplied _ runtime count selected context.1 _ _
      (fun created cut reached => PqxdhRegistrationJointKemCutBounds.residual setup _ 0 _ _
        (bills created).uniform cut reached) context.2.val context.2.property
  · exact pre_bound setup ensureInit supplied _ runtime count selected context.1 _ _
      (fun created cut reached => residual_hook setup _ 0 1 (bills created).encaps cut reached)
      context.2.val context.2.property

set_option backward.isDefEq.respectTransparency false in
/-- Every postchallenge context of the proof-carrying adversary at the logged exposure has the caps of `KemRawBills.adversary_post`. -/
theorem adversary_post (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (transcript : MlKemChallengeTranscript (PqxdhDeploymentLaterServerKemHop.Saved setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected))
    (candidate : MlKemSharedSecret) :
    CcaBills ((PqxdhDeploymentLaterServerKemHop.certified setup ensureInit supplied
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count
        selected).postChallenge transcript candidate)
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  have bill := PqxdhRegistrationJointKemPostBills.post_bound setup caps bounded count selected transcript.context.2.val
    transcript.publicKey transcript.ciphertext candidate _ _ _ _
    (saved setup codec checks caps bounded ensureInit supplied decision work runtime count selected index budget reads
      certified serverReads transcript.context)
  rw [PqxdhRegistrationJointKemRawBills.uniform_cap] at bill
  constructor
  · simpa only [PqxdhDeploymentLaterServerKemHop.certified, isQueryBoundP_map_iff] using bill.uniform
  · simpa only [PqxdhDeploymentLaterServerKemHop.certified, isQueryBoundP_map_iff] using bill.base
  · simpa only [PqxdhDeploymentLaterServerKemHop.certified, isQueryBoundP_map_iff] using bill.decaps

/-- The KEM scan of the logged exposure inherits the private request caps of the hidden logged command program of the decision program, and its uniform cap pays every actual encapsulation. -/
theorem scan_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (index : Nat) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    PqxdhRegistrationJointKemCutInterpreted.Bills
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created)
      (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget + caps.encapsCost * budget (.inl 3)) := by
  have actualBills := PqxdhRegistrationJointKemCutInterpreted.actual_bills setup caps bounded _ _ _ _ _
    (commands_bills setup codec checks caps bounded created.server.server.metadata.identityIndex created.publicIdentity
      (decideTag decision <$> PqxdhDeploymentLaterServerCommands.tag work index) budget reads
      (fun source => (isQueryBoundP_map_iff _ _ _).mpr
        (PqxdhDeploymentLaterServerBridge.tag_bound work index _ _ (certified source)))
      ((isQueryBoundP_map_iff _ _ _).mpr (PqxdhDeploymentLaterServerBridge.tag_bound work index _ _ serverReads))
      [] [] (PqxdhRegistrationJointInitializedAccept.initial created))
  have finished (predicate : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
      (bound : (simulateQ (actual setup) (commands setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (decideTag decision <$> PqxdhDeploymentLaterServerCommands.tag work index) [] []
        (PqxdhRegistrationJointInitializedAccept.initial created))).IsQueryBoundP predicate cap) :
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created).IsQueryBoundP
        predicate cap := by
    apply PqxdhRegistrationJointKemCutBounds.bind_prefix _ (PqxdhRegistrationJointKemCut.finish setup)
    rw [PqxdhDeploymentLaterServerCut.scanned, PqxdhRegistrationJointKemCut.scan_finish,
      PqxdhDeploymentLaterServerCut.exposeAt_actual]
    exact bound
  exact ⟨finished _ _ actualBills.creates, finished _ _ actualBills.decaps, finished _ _ actualBills.uniform⟩

/-- Full prephase uniform allowance of the KEM adversary at the logged exposure, the allowance of `KemRawBills.pre_uniform`. -/
theorem pre_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (budget : Budget)
    (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected
        target).IsQueryBoundP
      IsMlKemUniformQuery ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))) := by
  unfold PqxdhDeploymentLaterServerKemHop.pre
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
    (PqxdhRegistrationJointServerBirth.client_uniform setup ensureInit qInit initBound setup.serverKeyId supplied _))
  rintro ⟨(_ | created), after⟩ _
  · simp
  · apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
      (PqxdhLiveKemSelection.family_uniform _ caps.keygenCost count
        (PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded)))
    intro others _
    have bills := scan_bills setup codec checks caps bounded decision work budget reads certified serverReads index
      created
    simpa only [uniformCap, bind_pure_comp, isQueryBoundP_map_iff] using
      PqxdhDynamicKemJointBounds.pre_uniform setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _ _ _
        bills.creates bills.uniform bills.decaps (after.1.1, PqxdhDynamicKemRouter.empty)
        caps.decapsUniform (PqxdhRegistrationJointKemCosts.local_uniform setup caps bounded)

/-- Local constructor and reservation work of the prephase have no external nonuniform CCA query, for every scanned program. -/
theorem pre_excluded (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (scanned : PqxdhDeploymentLaterServerKemHop.Scanned KemSK) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inl (.inl coin))) (q : Nat)
    (suffix : ∀ created joint others,
      ((((simulateQ (PqxdhDynamicKemJointRouter.pre setup.joint setup.kem selected.val
        (PqxdhDynamicKemRouter.selectedReservation selected target others))
        (scanned created)).run).run (joint, PqxdhDynamicKemRouter.empty))).IsQueryBoundP predicate q) :
    (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied scanned runtime count selected
      target).IsQueryBoundP predicate q := by
  unfold PqxdhDeploymentLaterServerKemHop.pre
  rw [← Nat.zero_add q]
  apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
  rintro ⟨(_ | created), after⟩ _
  · simp
  · rw [← Nat.zero_add q]
    apply isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ predicate noCoins)
    intro others _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using suffix created after.1.1 others

/-- The prephase at the logged exposure has at most `qFinish` logical CCA decapsulation queries. -/
theorem pre_decapsulations (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected
        target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery (budget (.inl 5)) :=
  pre_excluded setup ensureInit supplied _ runtime count selected target
    IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_decaps setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded decision work budget reads certified serverReads index created).decaps
      (joint, PqxdhDynamicKemRouter.empty))

/-- The prephase at the logged exposure retains every local decapsulation base query, at most `decapsBase * qFinish`. -/
theorem pre_base (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (budget : Budget) (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) (target : MlKem768PublicKey) :
    (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected
        target).IsQueryBoundP IsMlKemBaseQuery (caps.decapsBase * budget (.inl 5)) :=
  pre_excluded setup ensureInit supplied _ runtime count selected target
    IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery]) _
    (fun created joint others => PqxdhDynamicKemJointBounds.pre_base setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected target others) _ _
      (scan_bills setup codec checks caps bounded decision work budget reads certified serverReads index created).decaps
      (joint, PqxdhDynamicKemRouter.empty) IsMlKemBaseQuery
      (fun _ => by simp [IsMlKemBaseQuery]) (fun _ => by simp [IsMlKemBaseQuery])
      caps.decapsBase (PqxdhRegistrationJointKemCosts.local_base setup caps bounded))

/-- Forward support annotation leaves every prephase resource bound unchanged, for every scanned program. -/
theorem annotated_bound (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (scanned : PqxdhDeploymentLaterServerKemHop.Scanned KemSK) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (target : MlKem768PublicKey)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : (PqxdhDeploymentLaterServerKemHop.pre setup ensureInit supplied scanned runtime count selected
      target).IsQueryBoundP predicate cap) :
    (PqxdhDeploymentLaterServerKemHop.annotatedPre setup ensureInit supplied scanned runtime count selected
      target).IsQueryBoundP predicate cap := by
  rw [← PqxdhDeploymentLaterServerKemHop.prefix_erase setup ensureInit supplied scanned runtime count selected
    target] at bounded
  exact (isQueryBoundP_map_iff _ _ _).mp bounded

set_option backward.isDefEq.respectTransparency false in
/-- The proof-carrying KEM adversary at the logged exposure is bounded with exactly the caps of `KemRawBills.adversary_bound`; the Server reads add nothing, whatever their finite cap. -/
theorem adversary_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (budget : Budget)
    (reads : Nat)
    (certified : ∀ source, work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = some source)
      (budget source))
    (serverReads : work.IsQueryBoundP (fun query => laterKind (KemSK := KemSK) query = none) reads)
    (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    (PqxdhDeploymentLaterServerKemHop.certified setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count
        selected).MakesAtMostQueries
      ((qInit + if supplied.isNone then 32 else 0) +
        (caps.keygenCost * count + uniformCap caps (budget (.inl 1)) (budget (.inl 5))
          (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3))))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5))
      (uniformCap caps (budget (.inl 1)) (budget (.inl 5))
        (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)))
      (caps.decapsBase * budget (.inl 5)) (budget (.inl 5)) := by
  constructor
  · intro target
    refine ⟨?_, ?_, ?_⟩
    · exact annotated_bound setup ensureInit supplied _ runtime count selected target _ _
        (pre_uniform setup codec checks caps bounded ensureInit qInit initBound supplied decision work budget reads
          certified serverReads runtime count selected index target)
    · exact annotated_bound setup ensureInit supplied _ runtime count selected target _ _
        (pre_base setup codec checks caps bounded ensureInit supplied decision work budget reads certified serverReads
          runtime count selected index target)
    · exact annotated_bound setup ensureInit supplied _ runtime count selected target _ _
        (pre_decapsulations setup codec checks caps bounded ensureInit supplied decision work budget reads certified
          serverReads runtime count selected index target)
  · intro transcript candidate
    have bills := adversary_post setup codec checks caps bounded ensureInit supplied decision work runtime count
      selected index budget reads certified serverReads transcript candidate
    exact ⟨bills.uniform, bills.base, bills.decaps⟩

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.run_exposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.run_exposed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_source

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposed_later

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.single_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.single_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.total_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.total_single

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.commands_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.commands_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_hides' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_hides

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.accept_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.exposeAt_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.saved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.saved

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.adversary_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.adversary_post

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.scan_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.scan_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_excluded

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_decapsulations

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.pre_base

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.annotated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.annotated_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.adversary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBills.adversary_bound
