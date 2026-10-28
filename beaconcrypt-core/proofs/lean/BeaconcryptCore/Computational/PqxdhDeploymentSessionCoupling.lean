-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionAgreement

/-! Private state-carrying localization for deployment session agreement. The original CE-A1 probability transfer keeps only the public registration journal. These equalities retain the complete reassembled native state, including both primitive caches, alongside that journal. Only the existing analysis histories are erased. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhServerAuthEntryFactor (Context)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentServerAuthEvent (SourceEntry)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Emb freeze dflt stopAt)
open PqxdhDeploymentServerAuthLocal (State Pre Phase base multiOf Bad)
open PqxdhDeploymentServerAuthChain (seedBinding seedInput draw_support)
open PqxdhRegistrationR1Restriction (eraseShared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Read a localized singleton outcome back as its original multi-owner source state. The private ServerAuth journal is omitted; the program's result, full source journal and every native field remain. -/
def localizedView (pre : Pre KemSK)
    (outcome : (((Result × List (SourceEntry KemSK)) × Emb KemSK) ×
      State KemSK)) : (Result × List (SourceEntry KemSK)) × State KemSK :=
  (outcome.1.1, eraseShared (multiOf pre outcome.1.2 outcome.2))

/-- The same complete-state view before forgetting the eager target phase. -/
def eagerView (outcome : (Result × List (SourceEntry KemSK)) × (State KemSK × Phase)) :
    (Result × List (SourceEntry KemSK)) × State KemSK :=
  (outcome.1, eraseShared outcome.2.1)

/-- At fixed actual target draws, localization preserves the program's return value, the frozen journal and the entire reassembled source state. -/
theorem localized_frozen_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) (state : State KemSK) (empty : state.owners = [])
    (pre : Pre KemSK) (member : pre ∈ support (PqxdhDeploymentServerAuthEager.draw setup codec (seedBinding setup seed))) :
    localizedView pre <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route
          (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program
            (seedInput setup seed pre.reply)))).run ⟨state.shared, [pre.bundled]⟩ =
      eagerView <$>
        (simulateQ (PqxdhDeploymentServerAuthLocal.eager setup codec checks seed c (seedBinding setup seed) pre)
          (freeze dflt (stopAt c) program)).run (state, .waiting) := by
  obtain ⟨createdFresh, bundledSent⟩ := draw_support setup codec _ pre member
  have localized := congrArg (fun run => (fun outcome : Result ×
      (List (SourceEntry KemSK) × (State KemSK × Phase)) =>
        ((outcome.1, outcome.2.1), outcome.2.2.1)) <$> run)
    (PqxdhDeploymentServerAuthLocalize.localize setup codec checks seed c
      (seedInput setup seed pre.reply) (seedBinding setup seed) pre rfl rfl createdFresh bundledSent
      program unread (⟨state.shared, [pre.bundled]⟩ : State KemSK) rfl)
  have stateEq : (⟨state.shared, []⟩ : State KemSK) = state :=
    congrArg (PqxdhRegistrationSchedule.State.mk state.shared) empty.symm
  simp only [Functor.map_map, stateEq] at localized
  rw [← QueryImpl.simulateQ_compose]
  change localizedView pre <$>
      (simulateQ (PqxdhDeploymentServerAuthLocalize.routed setup codec checks seed)
        ((simulateQ (PqxdhDeploymentServerAuthEmbed.embed setup codec c (seedInput setup seed pre.reply))
          ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program).run [])).run
            Emb.empty)).run ⟨state.shared, [pre.bundled]⟩ =
    eagerView <$> (simulateQ (PqxdhDeploymentServerAuthLocal.eager setup codec checks seed c
      (seedBinding setup seed) pre)
        ((simulateQ (PqxdhDeploymentServerAuthEmbed.freezeImpl dflt (stopAt c)) program).run [])).run
          (state, .waiting)
  simp only [PqxdhDeploymentServerAuthLocalize.stack_run, Functor.map_map]
  simpa only [localizedView, eagerView, Prod.map, id_eq,
    PqxdhDeploymentServerAuthLocalize.singleSide, PqxdhDeploymentServerAuthLocalize.eagerSide,
    PqxdhDeploymentServerAuthLocalize.reassemble, PqxdhDeploymentServerAuthLocalize.eraseEager] using localized

/-- The early-draw reduction preserves the full frozen deployment state in distribution, not only the public journal event used by CE-A1. -/
theorem frozen_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) (state : State KemSK) (empty : state.owners = []) :
    EvalDistEq
      (Prod.map id eraseShared <$>
        (simulateQ (base setup codec checks seed) (freeze dflt (stopAt c) program)).run state)
      (do
        let pre ← PqxdhDeploymentServerAuthEager.draw setup codec (seedBinding setup seed)
        localizedView pre <$>
          (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
            (simulateQ PqxdhRegistrationR1Restriction.route
              (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program
                (seedInput setup seed pre.reply)))).run ⟨state.shared, [pre.bundled]⟩) := by
  refine ((PqxdhDeploymentServerAuthEager.swap setup codec checks seed c (seedBinding setup seed)
    (freeze dflt (stopAt c) program) state (by simp [empty])).map (Prod.map id eraseShared)).trans ?_
  simp only [map_bind, Functor.map_map]
  refine EvalDistEq.bind_congr_of_support _ fun pre member => ?_
  rw [localized_frozen_state setup codec checks seed c program unread state empty pre member]
  exact .rfl

/-- The early target material is reconstructed from its actual private generation context, not by matching public keys. -/
def contextPre (setup : Setup baseSpec KemSK) (context : Context KemSK) : Pre KemSK :=
  ⟨PqxdhRegistrationR1Restriction.ownerValue context.beaconSeed context.scalar context.keys.1
      (freshBeacon setup (context.publicValue setup) context.keys.2),
    context.published.1,
    PqxdhRegistrationR1Restriction.ownerValue context.beaconSeed context.scalar context.keys.1 context.published.2⟩

/-- Materializing the initial concrete owner commutes with the optional first bundle, retaining its exact returned owner even on publication failure. -/
theorem local_bundle_materialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed identity : IdentitySeed) (selected : PqxdhJointGapDh.ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK) :
    PqxdhDeploymentServerAuthEmbed.localBundle setup codec 0
      (PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1
        (freshBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) keys.2)) =
      (fun published => (published.1,
        PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1 published.2)) <$>
        (do
          let oneTime ← PqxdhJointGapDh.sampleScalar
          phase1Run setup codec identity (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected)
            oneTime keys.1 keys.2) := by
  have same := congrArg (Functor.map (fun result : Option Pqxdh.Bytes × State KemSK =>
      (result.1, result.2.owners.headD
        (PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1
          (freshBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) keys.2)))))
    (PqxdhRegistrationR1Initial.bundle_initial setup codec seed identity selected keys.1 keys.2
      (freshBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) keys.2))
  rw [PqxdhDeploymentServerAuthLocal.bundle_found setup codec 0 _ _ rfl] at same
  simpa only [Functor.map_map, PqxdhRegistrationR1Restriction.singleton,
    PqxdhRegistrationR1Initial.sourceInitial, initialGameState, List.set_cons_zero,
    List.headD_cons, Prod.mk.eta, id_map'] using same

/-- Private source-order generation context for a fixed Server seed. -/
noncomputable def contextDraw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) : ProbComp (Context KemSK) := do
  let material ← PqxdhRegistrationJointCreation.material setup
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let published ← phase1Run setup codec material.seed
    (PqxdhJointGapDh.challenge setup.joint setup.dh seed material.prekey) oneTime material.keys.1 material.keys.2
  pure ⟨seed, material.prekey, material.seed, oneTime, material.keys, published⟩

/-- Reindexing the actual early draw retains its complete created and bundled owner, not just the optional public reply. -/
theorem draw_materialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed) :
    PqxdhDeploymentServerAuthEager.draw setup codec (seedBinding setup seed) =
      contextPre setup <$> contextDraw setup codec seed := by
  simp only [PqxdhDeploymentServerAuthEager.draw, PqxdhDeploymentServerAuthEmbed.localCreate,
    contextDraw, PqxdhRegistrationJointCreation.material, map_bind, bind_assoc, pure_bind, map_pure]
  refine bind_congr fun identity => bind_congr fun selected => bind_congr fun keys => ?_
  change (do
    let bundled ← PqxdhDeploymentServerAuthEmbed.localBundle setup codec 0
      (PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1
        (freshBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) keys.2))
    pure (⟨PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1
      (freshBeacon setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) keys.2),
        bundled.1, bundled.2⟩ : Pre KemSK)) = _
  rw [local_bundle_materialized setup codec seed identity selected keys, bind_map_left, bind_assoc]
  rfl

/-- The original generated Server state, before any dynamic owner is allocated. -/
def initial (setup : Setup baseSpec KemSK) (seed : IdentitySeed) : State KemSK :=
  PqxdhRegistrationSchedule.initial
    (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId .generated seed)

/-- The unused compatibility owner of the original generated Server interpreter. -/
def compatibility (setup : Setup baseSpec KemSK) (seed : IdentitySeed) :
    RawCtxBeaconLifecycle.State Unit (Unit ⊕ PqxdhJointGapDh.ScalarBytes) KemSK :=
  PqxdhRegistrationSchedule.bookkeeping
    (PqxdhLiveServerConstruction.initialized setup.joint 0 setup.serverKeyId .generated seed)

/-- Read one private callback occurrence execution as the complete concrete singleton source state. -/
def occurrenceView (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (outcome : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) × PqxdhJointDhExtractFamily.State) :
    Result × State KemSK :=
  (outcome.1.1, PqxdhRegistrationR1Restriction.singleton context.beaconSeed context.scalar context.keys.1
    (compatibility setup context.seed) (eraseObservers (outcome.2, outcome.1.2.1)))

/-- Every actual source-order generation and optional publication result supplies the complete native-state root audit, jointly with the continuation result. -/
theorem fixed_root_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed identity : IdentitySeed) (selected oneTime : PqxdhJointGapDh.ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ PqxdhJointGapDh.ScalarBytes) KemSK)
    (supported : published ∈ support (phase1Run setup codec identity
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected) oneTime keys.1 keys.2))
    (work : OracleComp ServerAuthSpec Result) :
    Prod.map id eraseShared <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route work)).run
          ⟨(initial setup seed).shared,
            [PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1 published.2]⟩ =
      occurrenceView setup ⟨seed, selected, identity, oneTime, keys, published⟩ <$>
        PqxdhServerAuthRootExecution.execution setup codec checks
          ⟨seed, selected, identity, oneTime, keys, published⟩ work := by
  have native := PqxdhRegistrationR1Audit.singleton_program setup codec checks seed identity selected keys.1
    (compatibility setup seed) work (PqxdhRegistrationR1Initial.sourceInitial setup seed selected published.2)
    (inv_initial setup codec identity (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected)
      oneTime keys.1 keys.2 published supported)
    (phase1_handles setup codec identity (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected)
      oneTime keys.1 keys.2 published supported)
  rw [← PqxdhRegistrationR1RootAudit.native_root setup codec checks
    ⟨seed, selected, identity, oneTime, keys, published⟩ work
    (inv_initial setup codec identity (PqxdhJointGapDh.challenge setup.joint setup.dh seed selected)
      oneTime keys.1 keys.2 published supported)] at native
  have initialEq : PqxdhRegistrationR1Restriction.singleton identity selected keys.1 (compatibility setup seed)
      (eraseObservers (PqxdhRegistrationR1Initial.sourceInitial setup seed selected published.2)) =
      (⟨(initial setup seed).shared,
        [PqxdhRegistrationR1Restriction.ownerValue identity selected keys.1 published.2]⟩ : State KemSK) := rfl
  change Prod.map id eraseShared <$> _ =
    (fun outcome : (Result × PqxdhServerAuthRootOccurrences.Audit KemSK) × PqxdhJointDhExtractFamily.State =>
      (outcome.1.1, PqxdhRegistrationR1Restriction.singleton identity selected keys.1
        (compatibility setup seed) (eraseObservers (outcome.2, outcome.1.2.1)))) <$>
      PqxdhServerAuthRootExecution.execution setup codec checks
        ⟨seed, selected, identity, oneTime, keys, published⟩ work
  simpa only [initialEq, Functor.map_map, PqxdhRegistrationR1RootAudit.nativeOf,
    Prod.map, Function.comp_def, id_eq] using native

/-- The complete operational singleton state read from a same-run private root audit. -/
def singletonAuditView (setup : Setup baseSpec KemSK)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK Result) : Result × State KemSK :=
  (audit.1, PqxdhRegistrationR1Restriction.singleton audit.2.context.beaconSeed audit.2.context.scalar
    audit.2.context.keys.1 (compatibility setup audit.2.context.seed)
      (eraseObservers (audit.2.primitive, audit.2.state.1)))

/-- The early draw and complete continuation share one private root audit. The left side retains the exact early draw jointly with the entire native state; the right side reconstructs it from the same generation occurrence. -/
theorem contextual_root_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (work : Option Pqxdh.Bytes → OracleComp ServerAuthSpec Result) :
    (do
      let pre ← PqxdhDeploymentServerAuthEager.draw setup codec (seedBinding setup seed)
      (fun result => (pre, result)) <$> (Prod.map id eraseShared <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route (work pre.reply))).run
            ⟨(initial setup seed).shared, [pre.bundled]⟩)) =
      (fun audit => (contextPre setup audit.2.context, singletonAuditView setup audit)) <$>
        PqxdhRegistrationR1RootAudit.rootAudited setup codec checks seed work := by
  rw [draw_materialized]
  simp only [contextDraw, PqxdhRegistrationR1RootAudit.rootAudited, map_bind, bind_map_left,
    bind_assoc, bind_pure_comp]
  refine bind_congr fun material => bind_congr fun oneTime =>
    OracleComp.bind_congr_of_forall_mem_support _ fun published supported => ?_
  have coupled := congrArg (Functor.map (fun result =>
      (contextPre setup ⟨seed, material.prekey, material.seed, oneTime, material.keys, published⟩, result)))
    (fixed_root_state setup codec checks seed material.seed material.prekey oneTime material.keys published
      supported (work published.1))
  simpa only [Functor.map_map, contextPre, occurrenceView, singletonAuditView] using coupled

/-- Existing analysis-history erasure commutes with reassembling the full source state. -/
theorem localizedView_erase (pre : Pre KemSK) (value : (Result × List (SourceEntry KemSK)) × Emb KemSK)
    (state : State KemSK) :
    localizedView pre (value, eraseShared state) = localizedView pre (value, state) := rfl

/-- Keeping the reduction's private query journal changes neither its output nor the reassembled state. -/
theorem recorded_localized_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (pre : Pre KemSK) (state : State KemSK) :
    localizedView pre <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ PqxdhRegistrationR1Restriction.route
          (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program
            (seedInput setup seed pre.reply)))).run state =
      (fun result => localizedView pre (result.1.1, result.2)) <$>
        (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
          (simulateQ PqxdhRegistrationR1Restriction.route
            (PqxdhDeploymentServerAuthEmbed.adversary setup codec c program
              (seedInput setup seed pre.reply)))).run state := by
  rw [← PqxdhServerAuthApiJournal.erase
    (PqxdhDeploymentServerAuthEmbed.embedded setup codec c program (seedInput setup seed pre.reply))]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The actual CE-A1 reduction result, including its public source journal, private embedding state and private authentication-query journal. -/
abbrev ReducedResult (KemSK Result : Type) :=
  (((Result × List (SourceEntry KemSK)) × Emb KemSK) × QueryLog ServerAuthSpec)

/-- A root-labelled target-prefix extension of the deployment source execution. Its generation context and callback receipts are private analysis output. -/
noncomputable def audited (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) :
    ProbComp (PqxdhRegistrationR1RootAudit.RootAudit KemSK (ReducedResult KemSK Result)) :=
  PqxdhRegistrationR1RootAudit.rootAudited setup codec checks seed
    (fun published => PqxdhDeploymentServerAuthEmbed.adversary setup codec c program (seedInput setup seed published))

/-- Reassemble every original source field from the private root-labelled execution. Only proof histories are erased; no cache, owner, pending token or native counter is projected away. -/
def auditedView (setup : Setup baseSpec KemSK)
    (audit : PqxdhRegistrationR1RootAudit.RootAudit KemSK (ReducedResult KemSK Result)) :
    (Result × List (SourceEntry KemSK)) × State KemSK :=
  localizedView (contextPre setup audit.2.context) (audit.1.1, (singletonAuditView setup audit).2)

/-- The private root-labelled execution erases to the full frozen deployment source state in distribution. This is the state-carrying link needed to transport the eleven-field root agreement and accepted record fields. -/
theorem frozen_root_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) :
    EvalDistEq
      (Prod.map id eraseShared <$>
        (simulateQ (base setup codec checks seed) (freeze dflt (stopAt c) program)).run (initial setup seed))
      (auditedView setup <$> audited setup codec checks seed c program) := by
  have coupled := congrArg (Functor.map
      (fun paired : Pre KemSK × (ReducedResult KemSK Result × State KemSK) =>
        localizedView paired.1 (paired.2.1.1, paired.2.2)))
    (contextual_root_state setup codec checks seed
      (fun published => PqxdhDeploymentServerAuthEmbed.adversary setup codec c program (seedInput setup seed published)))
  simp only [map_bind, Functor.map_map, Prod.map, id_eq, localizedView_erase] at coupled
  change _ = auditedView setup <$> audited setup codec checks seed c program at coupled
  refine (frozen_state setup codec checks seed c program unread (initial setup seed) rfl).trans ?_
  rw [← coupled]
  simp only [recorded_localized_state]
  exact .rfl

end BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.localized_frozen_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.localized_frozen_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.frozen_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.frozen_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.local_bundle_materialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.local_bundle_materialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.draw_materialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.draw_materialized

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.fixed_root_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.fixed_root_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.contextual_root_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.contextual_root_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.recorded_localized_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.recorded_localized_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.frozen_root_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.frozen_root_state

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.localizedView_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionCoupling.localizedView_erase
