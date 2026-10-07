-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthTrack

/-! The chain from the deployment experiment to the root-audited singleton run of `R_c`, for one Server seed and one creation index (CE-8). On the compiled program run natively from the constructed Server's initial state, the A1 failure of `c` on the transcript has the probability of the A1 failure on the registration view of the program's journal frozen at the stop of `c` (`native_frozen`: `journal_erase`, `compiled_regs`, `unmatched_frozen` and `frozen_journal`). From a state with no owner, the target's material is drawn first (`PqxdhDeploymentServerAuthEager.swap`), the eager run is localized to the singleton side (`PqxdhDeploymentServerAuthLocalize.localize`, with `compiled_unread` and `draw_support`), and the singleton side is `R_c` routed into the source14 handler on the singleton that the early draw creates and bundles (`frozen_single`). That singleton is the typed constructor and first bundle of the original R1 singleton (`typed_draw`), whose client return value has the distribution of the root-audited singleton run (`typed_root`, from `typed_audit` and `audited_root`). On that run, for every Server seed the generator can draw, the A1 failure of `c` under the seed's binding is a common authentication failure (`root_failure`, from `PqxdhDeploymentServerAuthTrack.adversary_unmatched` and `PqxdhDeploymentServerAuthJournal.audited_failure`). `seed_bound` composes these steps. No security claim is made here beyond the stated inequality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry regsOf regsOfSource Unmatched)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner Emb localCreate localBundle dflt stopAt freeze inputBinding)
open PqxdhDeploymentServerAuthLocal (State base Pre Bad)
open PqxdhDeploymentServerAuthEager (draw)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X Result : Type}

/-! ## Draws of the target -/

/-- A simulation by an oracle implementation can only return what the simulated program can return. -/
theorem support_simulateQ_subset {κ κ' : Type} {spec : OracleSpec κ} {spec' : OracleSpec κ'} {α : Type}
    (impl : QueryImpl spec (OracleComp spec')) (program : OracleComp spec α) :
    support (simulateQ impl program) ⊆ support program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      intro value member
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        mem_support_bind_iff] at member
      obtain ⟨reply, _, inner⟩ := member
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query _ _, ih reply inner⟩

/-- A published bundle of the native Phase 1 program leaves its owner in InitSent. -/
theorem bundle_published {I : Type} (projection : PqxdhLivePhase1Bundle.Public I ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (state : PqxdhBeaconPhase1Publication.State (I := I) (D := ScalarBytes) (K := PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (result : Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := ScalarBytes)
      (K := PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (member : result ∈ support (PqxdhLivePhase1Bundle.bundle projection state)) (bytes : Pqxdh.Bytes)
    (published : result.1 = some bytes) :
    PqxdhDeploymentEligibility.phaseClass result.2.beacon.phase = .initSent := by
  have after : ∀ generated, result ∈ support (PqxdhLivePhase1Bundle.afterGenerated projection generated state) →
      PqxdhDeploymentEligibility.phaseClass result.2.beacon.phase = .initSent := by
    intro generated reached
    unfold PqxdhLivePhase1Bundle.afterGenerated at reached
    cases prepared : PqxdhBeaconPhase1Publication.prepare state generated with
    | none =>
        simp only [prepared, support_pure, Set.mem_singleton_iff] at reached
        rw [reached] at published
        cases published
    | some ready =>
        simp only [prepared, mem_support_bind_iff] at reached
        obtain ⟨signed, _, reached⟩ := reached
        cases signed with
        | none =>
            simp only [support_pure, Set.mem_singleton_iff] at reached
            rw [reached] at published
            cases published
        | some candidate =>
            have inner := support_simulateQ_subset _ _ reached
            unfold PqxdhBeaconPhase1Publication.afterSigning at inner
            simp only [prepared, mem_support_bind_iff] at inner
            obtain ⟨serialized, _, inner⟩ := inner
            cases serialized with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at inner
                rw [inner] at published
                cases published
            | some written =>
                simp only [support_pure, Set.mem_singleton_iff] at inner
                rw [inner]
                rfl
  unfold PqxdhLivePhase1Bundle.bundle at member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨generated, _, reached⟩ := member
    exact after generated reached
  · exact after none member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member] at published
    cases published

/-- The target material drawn before the run: the created owner is Fresh and, when its first bundle is published, the bundled owner is in InitSent. -/
theorem draw_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (binding : Word32 × Std.U64)
    (pre : Pre KemSK) (member : pre ∈ support (draw setup codec binding)) :
    PqxdhDeploymentEligibility.phaseClass pre.created.beacon.phase = .fresh ∧
      ∀ bytes, pre.reply = some bytes → PqxdhDeploymentEligibility.phaseClass pre.bundled.beacon.phase = .initSent := by
  simp only [draw, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨created, createdMember, bundled, bundledMember, rfl⟩ := member
  refine ⟨PqxdhDeploymentServerAuthEager.localCreate_fresh setup _ _ created createdMember, fun bytes published => ?_⟩
  exact bundle_published _ _ bundled (support_simulateQ_subset _ _ bundledMember) bytes published

/-- The compiled program issues no identity, KEM, prekey or one-time read. -/
theorem compiled_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    (compileFull setup codec route bounds mode adversary).IsQueryBoundP (Bad (KemSK := KemSK)) 0 := by
  have each : ∀ field : Fin 5, field ≠ 4 → (compileFull setup codec route bounds mode adversary).IsQueryBoundP
      (fun request => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) request = .inr field) 0 :=
    fun field notKernel => PqxdhDeploymentCompileSecrecy.compile_full_unread setup codec route bounds mode adversary field
      notKernel
  generalize compileFull setup codec route bounds mode adversary = program at each ⊢
  induction program using OracleComp.inductionOn with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind query next ih =>
      have free : ∀ field : Fin 5, field ≠ 4 →
          PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inr field := by
        intro field notKernel same
        have bound := each field notKernel
        rw [isQueryBoundP_query_bind_iff] at bound
        rcases bound.1 with free | impossible
        · exact free same
        · omega
      have good : ¬ Bad (KemSK := KemSK) query := by
        rcases query with request | ⟨index, field⟩
        · exact id
        · intro bad
          apply free (PqxdhRegistrationJointRevealCosts.fieldIndex field)
          · cases field <;> simp_all [PqxdhRegistrationJointRevealCosts.fieldIndex, Bad]
          · rfl
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl good, fun reply => ?_⟩
      simp only [good, ite_false]
      refine ih reply fun field notKernel => ?_
      have bound := each field notKernel
      rw [isQueryBoundP_query_bind_iff] at bound
      have rest := bound.2 reply
      simp only [free field notKernel, ite_false] at rest
      exact rest

/-- The typed singleton prefix, the target's create on the initial state followed by its first bundle, is the early draw of the target's material. -/
theorem typed_draw {β : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (binding : Word32 × Std.U64)
    (next : Option Pqxdh.Bytes × State KemSK → ProbComp β) :
    (do
      let made ← (PqxdhRegistrationSchedule.create setup binding.1 binding.2).run
        (PqxdhRegistrationSchedule.initial created)
      let published ← (PqxdhRegistrationSchedule.bundle setup codec 0).run made.2
      next published) =
    (do
      let pre ← draw setup codec binding
      next (pre.reply, ⟨(PqxdhRegistrationSchedule.initial (KemSK := KemSK) created).shared, [pre.bundled]⟩)) := by
  have made : (PqxdhRegistrationSchedule.create setup binding.1 binding.2).run
      (PqxdhRegistrationSchedule.initial (KemSK := KemSK) created) =
      (fun owner => (0, ⟨(PqxdhRegistrationSchedule.initial (KemSK := KemSK) created).shared, [owner]⟩)) <$>
        localCreate setup binding.1 binding.2 :=
    PqxdhDeploymentServerAuthLocal.create_local setup binding.1 binding.2 _
  rw [made, bind_map_left]
  simp only [draw, bind_assoc, pure_bind]
  refine bind_congr fun owner => ?_
  rw [PqxdhDeploymentServerAuthLocal.bundle_found setup codec 0 _ owner rfl, bind_map_left]
  rfl

set_option linter.deprecated false in
/-- Two computations with the same distribution give every event the same probability. -/
theorem probEvent_evalSPMF {α : Type} (first second : ProbComp α) (same : 𝒮[first] = 𝒮[second]) (event : α → Prop) :
    Pr[event | first] = Pr[event | second] := by
  unfold probEvent
  rw [same]


set_option linter.deprecated false in
/-- The A1 failure of `c` on the transcript of the compiled program under the native handler has the probability of the A1 failure on the registration view of the program's journal frozen at the stop of `c`. -/
theorem native_frozen (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (c : Nat) (binding : Word32 × Std.U64) (state : State KemSK) :
    Pr[fun result : ((X × Ledger) × Local) × State KemSK =>
        Unmatched setup.source.crypto codec binding c (regsOf result.1.1.2.transcript) |
      (simulateQ (base setup codec checks seed) (compileFull setup codec route bounds mode adversary)).run state] =
    Pr[fun outcome : (((X × Ledger) × Local) × List (SourceEntry KemSK)) × State KemSK =>
        Unmatched setup.source.crypto codec binding c (regsOfSource outcome.1.2) |
      (simulateQ (base setup codec checks seed)
        (freeze dflt (stopAt c) (compileFull setup codec route bounds mode adversary))).run state] := by
  have erased : (simulateQ (base setup codec checks seed) (compileFull setup codec route bounds mode adversary)).run state =
      (fun outcome => (outcome.1.1, outcome.2)) <$> (simulateQ (base setup codec checks seed)
        (PqxdhDeploymentServerAuthFreeze.journal dflt (compileFull setup codec route bounds mode adversary))).run state := by
    conv_lhs => rw [← PqxdhDeploymentServerAuthFreeze.journal_erase dflt (compileFull setup codec route bounds mode adversary)]
    rw [simulateQ_map, StateT.run_map]
  rw [erased, probEvent_map]
  rw [probEvent_ext (q := fun outcome : (((X × Ledger) × Local) × List (SourceEntry KemSK)) × State KemSK =>
      Unmatched setup.source.crypto codec binding c
        (regsOfSource (PqxdhDeploymentServerAuthEvent.untilStop (stopAt c) outcome.1.2))) ?_]
  · have frozen := probEvent_evalSPMF _ _ (PqxdhDeploymentServerAuthFreeze.frozen_journal dflt (stopAt c)
      (base setup codec checks seed) (compileFull setup codec route bounds mode adversary)
      (PqxdhDeploymentServerAuthFreeze.stopAt_nil c) state)
      (fun journal => Unmatched setup.source.crypto codec binding c (regsOfSource journal))
    rw [probEvent_map, probEvent_map] at frozen
    exact frozen
  · intro outcome member
    have program : outcome.1 ∈ support (PqxdhDeploymentServerAuthFreeze.journal dflt
        (compileFull setup codec route bounds mode adversary)) := by
      apply support_simulateQ_run'_subset (base setup codec checks seed) _ state
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ member
    have regs := PqxdhDeploymentServerAuthTrace.compiled_regs setup codec route bounds mode adversary outcome.1 program
    rw [PqxdhDeploymentServerAuthFreeze.unmatched_frozen]
    simp only [Function.comp_apply, regs]


/-- The protected binding of a Server seed: the 32-byte identity word and the Server key ID. -/
def seedBinding (setup : Setup baseSpec KemSK) (seed : IdentitySeed) : Word32 × Std.U64 :=
  (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys seed).ed25519, setup.serverKeyId)

/-- The ServerAuth input of a Server seed and an optional published Phase 1. -/
def seedInput (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (published : Option Pqxdh.Bytes) : AuthInput :=
  ⟨setup.joint.publicKeys seed, setup.serverKeyId, published, none⟩

set_option linter.deprecated false in
/-- From a state with no owner, the frozen journal of a program that issues no identity, KEM, prekey or one-time read has, under the native handler, the distribution of the frozen journal returned by `R_c` on the singleton that the early draw of the target's material creates and bundles: the A1 failure on the two views has the same probability. -/
theorem frozen_single (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) (state : State KemSK) (empty : state.owners = [])
    (crypto : Pqxdh.Crypto) :
    Pr[fun outcome : (Result × List (SourceEntry KemSK)) × State KemSK =>
        Unmatched crypto codec (seedBinding setup seed) c (regsOfSource outcome.1.2) |
      (simulateQ (base setup codec checks seed) (freeze dflt (stopAt c) program)).run state] =
    Pr[fun outcome : ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) × State KemSK) =>
        Unmatched crypto codec (seedBinding setup seed) c (regsOfSource outcome.1.1.1.2) |
      do
        let pre ← draw setup codec (seedBinding setup seed)
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route
            (PqxdhDeploymentServerAuthEmbed.adversary setup codec c program (seedInput setup seed pre.reply)))).run
          ⟨state.shared, [pre.bundled]⟩] := by
  rw [probEvent_evalSPMF _ _ (PqxdhDeploymentServerAuthEager.swap setup codec checks seed c (seedBinding setup seed)
    (freeze dflt (stopAt c) program) state (by simp [empty]))]
  rw [show (fun outcome : (Result × List (SourceEntry KemSK)) × State KemSK =>
      Unmatched crypto codec (seedBinding setup seed) c (regsOfSource outcome.1.2)) =
      (fun journal => Unmatched crypto codec (seedBinding setup seed) c (regsOfSource journal)) ∘
        (fun outcome : (Result × List (SourceEntry KemSK)) × State KemSK => outcome.1.2) from rfl,
    ← probEvent_map, map_bind]
  rw [show (fun outcome : ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) ×
      State KemSK) => Unmatched crypto codec (seedBinding setup seed) c (regsOfSource outcome.1.1.1.2)) =
      (fun journal => Unmatched crypto codec (seedBinding setup seed) c (regsOfSource journal)) ∘
        (fun outcome : ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) ×
          State KemSK) => outcome.1.1.1.2) from rfl,
    ← probEvent_map, map_bind]
  refine probEvent_bind_congr fun pre member => ?_
  congr 1
  obtain ⟨createdFresh, bundledSent⟩ := draw_support setup codec _ pre member
  set single : State KemSK := ⟨state.shared, [pre.bundled]⟩ with singleEq
  set input := seedInput setup seed pre.reply with inputEq
  have stateEq : (⟨single.shared, []⟩ : State KemSK) = state := by
    cases state
    simp_all
  have localized := congrArg (fun run => (fun outcome : Result × (List (SourceEntry KemSK) × (State KemSK ×
      PqxdhDeploymentServerAuthLocal.Phase)) => outcome.2.1) <$> run)
    (PqxdhDeploymentServerAuthLocalize.localize setup codec checks seed c input
      (seedBinding setup seed) pre rfl rfl createdFresh bundledSent program unread single rfl)
  simp only [Functor.map_map, stateEq] at localized
  have eagerRun := PqxdhDeploymentServerAuthLocalize.stack_run
    (PqxdhDeploymentServerAuthLocal.eager setup codec checks seed c (seedBinding setup seed) pre)
    (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program [] (state, .waiting)
  have outerRun := PqxdhDeploymentServerAuthLocalize.stack_run
    (PqxdhDeploymentServerAuthLocalize.stack (PqxdhDeploymentServerAuthLocalize.routed setup codec checks seed)
      (PqxdhDeploymentServerAuthEmbed.embed setup codec c input))
    (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program [] (Emb.empty, single)
  have innerRun := PqxdhDeploymentServerAuthLocalize.stack_run
    (PqxdhDeploymentServerAuthLocalize.routed setup codec checks seed)
    (PqxdhDeploymentServerAuthEmbed.embed setup codec c input) (freeze dflt (stopAt c) program) Emb.empty single
  have erased : PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input =
      Prod.fst <$> PqxdhDeploymentServerAuthEmbed.adversary setup codec c program input :=
    (PqxdhServerAuthApiJournal.erase _).symm
  have left : (fun outcome : (Result × List (SourceEntry KemSK)) × State KemSK => outcome.1.2) <$>
      ((fun result : (Result × List (SourceEntry KemSK)) × (State KemSK × PqxdhDeploymentServerAuthLocal.Phase) =>
          (result.1, result.2.1)) <$>
        (simulateQ (PqxdhDeploymentServerAuthLocal.eager setup codec checks seed c (seedBinding setup seed) pre)
          (freeze dflt (stopAt c) program)).run (state, .waiting)) =
      (fun outcome : Result × (List (SourceEntry KemSK) × (Emb KemSK × State KemSK)) => outcome.2.1) <$>
        (simulateQ (PqxdhDeploymentServerAuthLocalize.singleSide setup codec checks seed c input) program).run
          ([], (Emb.empty, single)) := by
    rw [Functor.map_map]
    change _ <$> (simulateQ (PqxdhDeploymentServerAuthLocal.eager setup codec checks seed c (seedBinding setup seed) pre)
      ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program).run [])).run (state, .waiting) = _
    rw [eagerRun, Functor.map_map]
    exact localized.symm
  have right : (fun outcome : ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) ×
      State KemSK) => outcome.1.1.1.2) <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route
          (PqxdhDeploymentServerAuthEmbed.adversary setup codec c program input))).run single =
      (fun outcome : Result × (List (SourceEntry KemSK) × (Emb KemSK × State KemSK)) => outcome.2.1) <$>
        (simulateQ (PqxdhDeploymentServerAuthLocalize.singleSide setup codec checks seed c input) program).run
          ([], (Emb.empty, single)) := by
    have routedEq : (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route
          (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input))).run single =
        (simulateQ (PqxdhDeploymentServerAuthLocalize.routed setup codec checks seed)
          (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input)).run single := by
      rw [PqxdhDeploymentServerAuthLocalize.routed, QueryImpl.simulateQ_compose]
    have advEq : (fun outcome : ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) ×
        State KemSK) => outcome.1.1.1.2) <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route
            (PqxdhDeploymentServerAuthEmbed.adversary setup codec c program input))).run single =
        (fun outcome : (((Result × List (SourceEntry KemSK)) × Emb KemSK) × State KemSK) => outcome.1.1.2) <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route
            (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input))).run single := by
      rw [erased, simulateQ_map, simulateQ_map, StateT.run_map, Functor.map_map]
    rw [advEq, routedEq]
    change _ <$> (simulateQ (PqxdhDeploymentServerAuthLocalize.routed setup codec checks seed)
      ((simulateQ (PqxdhDeploymentServerAuthEmbed.embed setup codec c input) (freeze dflt (stopAt c) program)).run
        Emb.empty)).run single = _
    rw [innerRun, Functor.map_map]
    change _ <$> (simulateQ (PqxdhDeploymentServerAuthLocalize.stack (PqxdhDeploymentServerAuthLocalize.routed setup
      codec checks seed) (PqxdhDeploymentServerAuthEmbed.embed setup codec c input))
      ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program).run [])).run
        (Emb.empty, single) = _
    rw [outerRun, Functor.map_map]
    rfl
  rw [left, right]


set_option linter.deprecated false in
/-- On the singleton that the early draw creates and bundles, every event of the client's return value has its probability in the root-audited singleton run of the same client, for every identity index and origin of the constructed Server. -/
theorem typed_root {Value : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (identityIndex : Nat) (origin : PqxdhLiveServerConstruction.Origin)
    (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Value) (event : Value → Prop) :
    Pr[fun outcome : Value × State KemSK => event outcome.1 |
      do
        let pre ← draw setup codec (seedBinding setup seed)
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route (work pre.reply))).run
          ⟨(PqxdhRegistrationSchedule.initial (KemSK := KemSK)
            (PqxdhLiveServerConstruction.initialized setup.joint identityIndex setup.serverKeyId origin seed)).shared,
            [pre.bundled]⟩] =
    Pr[fun audit => event audit.1 | PqxdhRegistrationR1RootAudit.rootAudited setup codec checks seed work] := by
  have shared : (PqxdhRegistrationSchedule.initial (KemSK := KemSK)
      (PqxdhLiveServerConstruction.initialized setup.joint identityIndex setup.serverKeyId origin seed)).shared =
      (PqxdhRegistrationSchedule.initial (KemSK := KemSK)
        (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin seed)).shared := rfl
  rw [shared, ← typed_draw setup codec (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId origin seed)
    (seedBinding setup seed) (fun published => (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
      (simulateQ PqxdhRegistrationR1Restriction.route (work published.1))).run published.2)]
  have typed := PqxdhRegistrationR1Initial.typed_audit setup codec checks seed origin work
  have erased := congrArg (fun run => Pr[fun outcome : Value × PqxdhRegistrationSchedule.State KemSK => event outcome.1 |
    run]) typed
  simp only [probEvent_map] at erased
  rw [← PqxdhRegistrationR1RootAudit.audited_root, probEvent_map] at erased
  exact erased

/-- On every root-audited singleton run of `R_c`, for every Server seed the generator can draw, the A1 failure of `c` on the frozen journal under the seed's binding is a common authentication failure. -/
theorem root_failure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (seed : IdentitySeed)
    (seeded : seed ∈ support sampleSeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK
      ((((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec)))
    (member : audit ∈ support (PqxdhRegistrationR1RootAudit.rootAudited setup codec checks seed
      (fun published => PqxdhDeploymentServerAuthEmbed.adversary setup codec c program (seedInput setup seed published))))
    (failure : Unmatched setup.source.crypto codec (seedBinding setup seed) c (regsOfSource audit.1.1.1.2)) :
    PqxdhServerAuthCommonProbability.decision setup codec checks audit.2 = true := by
  have client := PqxdhDeploymentServerAuthJournal.audited_client setup codec checks seed _ audit member
  obtain ⟨⟨raw, payload, finished⟩, unmatched⟩ := PqxdhDeploymentServerAuthTrack.adversary_unmatched
    setup.source.crypto setup codec c program (seedInput setup seed audit.2.context.published.1) audit.1 client failure
  exact PqxdhDeploymentServerAuthJournal.audited_failure setup codec checks phase1 seed seeded
    (fun input => PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input) audit member raw payload finished
    unmatched

set_option linter.deprecated false in
/-- For one Server seed the generator can draw and one creation index `c`, the A1 failure of `c` under the seed's binding on the transcript of the compiled program, run natively from the constructed Server's initial state, is at most the common authentication failure of the root-audited singleton run of `R_c`. -/
theorem seed_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (route : RawCtxServerRouting.SenderDecoder)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (c : Nat) (seed : IdentitySeed)
    (seeded : seed ∈ support sampleSeed) (identityIndex : Nat) (origin : PqxdhLiveServerConstruction.Origin) :
    Pr[fun result : ((X × Ledger) × Local) × State KemSK =>
        Unmatched setup.source.crypto codec (seedBinding setup seed) c (regsOf result.1.1.2.transcript) |
      (simulateQ (base setup codec checks seed) (compileFull setup codec route bounds mode adversary)).run
        (PqxdhRegistrationSchedule.initial
          (PqxdhLiveServerConstruction.initialized setup.joint identityIndex setup.serverKeyId origin seed))] ≤
    Pr[fun audit => PqxdhServerAuthCommonProbability.decision setup codec checks audit.2 = true |
      PqxdhRegistrationR1RootAudit.rootAudited setup codec checks seed (fun published =>
        PqxdhDeploymentServerAuthEmbed.adversary setup codec c (compileFull setup codec route bounds mode adversary)
          (seedInput setup seed published))] := by
  rw [native_frozen, frozen_single setup codec checks seed c _ (compiled_unread setup codec route bounds mode adversary)
    _ rfl setup.source.crypto]
  have step := typed_root setup codec checks seed identityIndex origin (fun published =>
    PqxdhDeploymentServerAuthEmbed.adversary setup codec c (compileFull setup codec route bounds mode adversary)
      (seedInput setup seed published))
    (fun value : (((((X × Ledger) × Local) × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec) =>
      Unmatched setup.source.crypto codec (seedBinding setup seed) c (regsOfSource value.1.1.2))
  exact step.trans_le (probEvent_mono fun audit member failure =>
    root_failure setup codec checks phase1 seed seeded c _ audit member failure)


end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.support_simulateQ_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.support_simulateQ_subset

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.bundle_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.bundle_published

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.draw_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.draw_support

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.compiled_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.compiled_unread

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.typed_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.typed_draw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.probEvent_evalSPMF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.probEvent_evalSPMF

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.native_frozen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.native_frozen

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.frozen_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.frozen_single

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.typed_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.typed_root

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.root_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.root_failure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.seed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthChain.seed_bound
