-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplatePolicy
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplateScope
/-! Literal identity-create counts survive the operational censor, template erasure, public policy and independent hash-coin language. Instrumentation and hash draws add no identity creation. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Target := RegistrationNativeIdentityTemplateCensorRecognition.Spec
variable {A : Type}

def SourceCreate : Source.Domain → Prop
  | .inl (.inl (.inr .create)) => True
  | _ => False
instance : DecidablePred SourceCreate := fun query => by unfold SourceCreate; split <;> infer_instance

def TargetCreate : Target.Domain → Prop
  | .inl (.inl (.inl (.inl (.inr .create)))) => True
  | _ => False
instance : DecidablePred TargetCreate := fun query => by unfold TargetCreate; split <;> infer_instance

private theorem prepare_scope (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) (placeholder : Ed25519Signature) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run before)).AllQueriesSatisfy (fun query => ¬TargetCreate query) := by
  unfold RegistrationNativeIdentityCensorOperational.promote RegistrationNativeIdentityCensorCompiler.prepare
  dsimp only [StateT.run]
  split
  · split
    · simp only [simulateQ_bind, RegistrationNativeIdentityCensorCompiler.select, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase]
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr (not_false)
      · intro chosen
        cases chosen with
        | false =>
          simp only [Bool.false_eq_true, ite_false, simulateQ_pure]
          exact allQueriesSatisfy_pure _ _
        | true =>
          simp only [ite_true, simulateQ_bind, RegistrationNativeIdentityCensorCompiler.inspect,
            simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
            RegistrationNativeIdentityTemplateCensorRecognition.erase]
          apply allQueriesSatisfy_bind
          · exact (allQueriesSatisfy_query_iff _ _).mpr (not_false)
          · intro inspected
            exact allQueriesSatisfy_pure _ _
    · simp only [pure_bind]
      exact allQueriesSatisfy_pure _ _
  · simp only [simulateQ_pure]
    exact allQueriesSatisfy_pure _ _

private theorem lift_scope (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A)
    (safe : (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work).AllQueriesSatisfy (fun query => ¬TargetCreate query))
    (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) A).run before)).AllQueriesSatisfy (fun query => ¬TargetCreate query) := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (do let answer ← work; pure (answer,before))).AllQueriesSatisfy _
  rw [simulateQ_bind]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

private theorem signing_scope (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) (placeholder : Ed25519Signature) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)).AllQueriesSatisfy (fun query => ¬TargetCreate query) := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, simulateQ_bind]
  apply allQueriesSatisfy_bind (prepare_scope selected handle message before placeholder)
  intro prepared
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · apply lift_scope
    rw [simulateQ_spec_query]
    exact allQueriesSatisfy_pure _ _
  · apply lift_scope
    simp only [RegistrationNativeIdentityCensorOperational.embed, simulateQ_spec_query,
      RegistrationNativeIdentityTemplateCensorRecognition.erase]
    exact (allQueriesSatisfy_query_iff _ _).mpr not_false

private theorem hash_scope (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before)).AllQueriesSatisfy (fun query => ¬TargetCreate query) := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
    | some _ => simulateQ RegistrationNativeIdentityCensorOperational.embed
        ((RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes)).run before)
    | none => do
        let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query (.inr (.template selected before.target
          (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) :
          OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
        pure (reply,before))).AllQueriesSatisfy _
  cases routed : (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
  | none =>
    simp only [simulateQ_bind, simulateQ_spec_query,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr not_false
    · intro reply
      exact allQueriesSatisfy_pure _ _
  | some input =>
    unfold RegistrationNativeIdentityCensorCompiler.implementation
    dsimp only [StateT.run]
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr not_false
    · intro reply
      exact allQueriesSatisfy_pure _ _

private theorem protocol_count (placeholder : Ed25519Signature) (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run before)).IsQueryBoundP TargetCreate
          (if SourceCreate (.inl request) then 1 else 0) := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      (do let answer ← RegistrationNativeIdentityCensorCompiler.protocol request; pure (answer,before)))).IsQueryBoundP _ _
  simp only [RegistrationNativeIdentityCensorCompiler.protocol, bind_pure_comp]
  rcases request with (coin | request) | report
  · simp [RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase, SourceCreate, TargetCreate, isQueryBoundP_query_iff]
  · cases request <;> simp [RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase, SourceCreate, TargetCreate, isQueryBoundP_query_iff]
  · simp [RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase, SourceCreate, TargetCreate, isQueryBoundP_query_iff]

private def lower (selected : Nat) (placeholder : Ed25519Signature) : QueryImpl Source (StateT Mode (OracleComp Target)) :=
  fun query before => simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder query).run before)

private theorem query_bound (selected : Nat) (placeholder : Ed25519Signature) (request : Source.Domain) (before : Mode) :
    ((lower selected placeholder request).run before).IsQueryBoundP TargetCreate (if SourceCreate request then 1 else 0) := by
  rcases request with ((coin | request) | report) | bytes
  · exact protocol_count placeholder _ before
  · cases request with
    | create | reveal handle => exact protocol_count placeholder _ before
    | service handle request => cases request with
      | staticDh peer => exact protocol_count placeholder _ before
      | sign message =>
        change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)).IsQueryBoundP TargetCreate 0
        simpa only [not_not] using (isQueryBoundP_zero_iff _ _).mpr (signing_scope selected handle message before placeholder)
  · exact protocol_count placeholder _ before
  · change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before)).IsQueryBoundP TargetCreate 0
    simpa only [not_not] using (isQueryBoundP_zero_iff _ _).mpr (hash_scope selected placeholder bytes before)

private theorem lower_run (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source A) (before : Mode) :
    ((simulateQ (lower selected placeholder) work).run before) =
      simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
        ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact bind_congr (fun result => ih result.1 result.2)

/-- The complete actual operational lowering and template erasure retain the literal original identity-create cap under every adaptive reply. -/
theorem operational (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source A) (before : Mode)
    (cap : Nat) (bounded : work.IsQueryBoundP SourceCreate cap) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before)).IsQueryBoundP TargetCreate cap := by
  rw [← lower_run]
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded (query_bound selected placeholder) before

private theorem independent_coins (work : ProbComp A) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.independent
      (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work)).IsQueryBoundP
        RegistrationNativeIdentityIndependentSource.IsCreate 0 := by
  rw [← QueryImpl.simulateQ_compose]
  apply OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim)
  intro coin _
  simp [QueryImpl.apply_compose, RegistrationNativeIdentityTemplateProtocol.coins,
    RegistrationNativeIdentityTemplateProtocol.independent, RegistrationNativeIdentityIndependentSource.IsCreate,
    isQueryBoundP_query_iff]

private noncomputable def policyLower (selected : Nat) :
    QueryImpl Target (StateT RegistrationNativeIdentityTemplatePolicy.Public (OracleComp RegistrationNativeIdentityIndependentSource.Spec)) :=
  fun query before => simulateQ RegistrationNativeIdentityTemplateProtocol.independent
    ((RegistrationNativeIdentityTemplatePolicy.handler selected query).run before)

private theorem policy_query (selected : Nat) (query : Target.Domain) (before : RegistrationNativeIdentityTemplatePolicy.Public) :
    ((policyLower selected query).run before).IsQueryBoundP RegistrationNativeIdentityIndependentSource.IsCreate
      (if TargetCreate query then 1 else 0) := by
  rcases query with ((protocol | message) | scan) | described
  · change (simulateQ RegistrationNativeIdentityTemplateProtocol.independent (do
      let answer ← RegistrationNativeIdentityTemplateProtocol.PublicSpec.query (.inl protocol)
      pure (answer, (RegistrationNativeIdentityCensorPolicySource.update selected protocol answer before.1, before.2)))).IsQueryBoundP _ _
    simp only [bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
    rcases protocol with (coin | request) | report
    · simp [RegistrationNativeIdentityTemplateProtocol.independent, RegistrationNativeIdentityIndependentSource.IsCreate,
        TargetCreate, isQueryBoundP_query_iff]
    · cases request <;> simp [RegistrationNativeIdentityTemplateProtocol.independent,
        RegistrationNativeIdentityIndependentSource.IsCreate, TargetCreate, isQueryBoundP_query_iff]
    · simp [RegistrationNativeIdentityTemplateProtocol.independent, TargetCreate]
  · simp [policyLower, RegistrationNativeIdentityTemplatePolicy.handler, StateT.run, TargetCreate]
  · change (simulateQ RegistrationNativeIdentityTemplateProtocol.independent
      (pure ((),before))).IsQueryBoundP RegistrationNativeIdentityIndependentSource.IsCreate 0
    simp only [simulateQ_pure]
    trivial
  · change (simulateQ RegistrationNativeIdentityTemplateProtocol.independent
      ((fun result => (result.1, (before.1,result.2))) <$>
        simulateQ RegistrationNativeIdentityTemplateProtocol.coins
          ((RegistrationNativeIdentityReindexedCtx.implementation described.input).run before.2))).IsQueryBoundP
            RegistrationNativeIdentityIndependentSource.IsCreate 0
    rw [simulateQ_map, isQueryBoundP_map_iff]
    exact independent_coins _

private theorem policy_run (selected : Nat) (work : OracleComp Target A)
    (before : RegistrationNativeIdentityTemplatePolicy.Public) :
    ((simulateQ (policyLower selected) work).run before) =
      simulateQ RegistrationNativeIdentityTemplateProtocol.independent
        ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact bind_congr (fun result => ih result.1 result.2)

/-- Public policy bookkeeping and independent hash coins retain every literal identity-create charge. -/
theorem policy (selected : Nat) (work : OracleComp Target A)
    (before : RegistrationNativeIdentityTemplatePolicy.Public) (cap : Nat)
    (bounded : work.IsQueryBoundP TargetCreate cap) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.independent
      ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected) work).run before)).IsQueryBoundP
        RegistrationNativeIdentityIndependentSource.IsCreate cap := by
  rw [← policy_run]
  exact OracleComp.IsQueryBoundP.simulateQ_run_StateT_of_step bounded (policy_query selected) before

/-- The actual original source syntax supplies the same complete reserved-family creation bill after both executable compilers. -/
theorem combined (selected : Nat) (placeholder : Ed25519Signature) (work : OracleComp Source A)
    (before : Mode) (policyBefore : RegistrationNativeIdentityTemplatePolicy.Public)
    (cap : Nat) (bounded : work.IsQueryBoundP SourceCreate cap) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.independent
      ((simulateQ (RegistrationNativeIdentityTemplatePolicy.handler selected)
        (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
          ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before))).run policyBefore)).IsQueryBoundP
            RegistrationNativeIdentityIndependentSource.IsCreate cap := by
  exact policy selected _ policyBefore cap (operational selected placeholder work before cap bounded)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.operational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.operational

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.policy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.policy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.combined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCreateCounts.combined
