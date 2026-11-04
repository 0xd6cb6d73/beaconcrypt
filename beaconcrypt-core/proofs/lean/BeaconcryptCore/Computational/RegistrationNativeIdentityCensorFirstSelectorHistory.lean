-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorArmedFresh
/-! Both private source interpretations can add only the literal one-time operand of their source tree to a selected successful history. Masked frontend replies do not erase the genuine private signing receipt. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorHistory
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativeIdentityCensorSource (State)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (poolMessages messages)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
open PqxdhEd25519EufCma (Ed25519Signature)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Old := RegistrationNativeIdentityCensorOperational.Spec
variable {A : Type}

private def Allowed (wanted : Pqxdh.Bytes) : Old.Domain → Prop
  | .inl (.inl (.inl (.inl (.inl (.inr (.service _ (.sign message))))))) => message≠wanted
  | .inr (.omitted _ message) => message≠wanted
  | _ => True

private theorem prepare_scope (wanted : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes) (mode : Mode) :
    ((RegistrationNativeIdentityCensorOperational.promote
      (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run mode).AllQueriesSatisfy (Allowed wanted) := by
  unfold RegistrationNativeIdentityCensorOperational.promote RegistrationNativeIdentityCensorCompiler.prepare
  dsimp only [StateT.run]
  split
  · split
    · simp only [RegistrationNativeIdentityCensorCompiler.select,simulateQ_bind,simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed]
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
      · intro chosen
        cases chosen with
        | false =>
            simp only [Bool.false_eq_true,ite_false,simulateQ_pure]
            exact allQueriesSatisfy_pure _ _
        | true =>
            simp only [ite_true,RegistrationNativeIdentityCensorCompiler.inspect,simulateQ_bind,simulateQ_spec_query,
              RegistrationNativeIdentityCensorOperational.embed]
            apply allQueriesSatisfy_bind
            · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
            · intro reply
              exact allQueriesSatisfy_pure _ _
    · simp only [pure_bind]
      exact allQueriesSatisfy_pure _ _
  · simp only [simulateQ_pure]
    exact allQueriesSatisfy_pure _ _

private theorem signing_scope (wanted : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes)
    (mode : Mode) (other : message≠wanted) :
    ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run mode).AllQueriesSatisfy (Allowed wanted) := by
  rw [RegistrationNativeIdentityCensorOperational.signing,StateT.run_bind]
  apply allQueriesSatisfy_bind (prepare_scope wanted selected handle message mode)
  intro prepared
  simp only [StateT.run_bind,StateT.run_get,pure_bind]
  split
  · change (do let reply ← (Old.query (.inr (.omitted handle message)) : OracleComp Old _)
               pure (reply,prepared.2) : OracleComp Old (Option Ed25519Signature × Mode)).AllQueriesSatisfy _
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨other,fun _=>trivial⟩
  · change (do let reply ← (Old.query (.inl (.inl (.inl (.inl (.inl (.inr (.service handle (.sign message)))))))) : OracleComp Old _)
               pure (reply,prepared.2) : OracleComp Old (Option Ed25519Signature × Mode)).AllQueriesSatisfy _
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨other,fun _=>trivial⟩

private theorem query_scope (fixed wanted : Pqxdh.Bytes) (selected : Nat) (placeholder : Ed25519Signature)
    (different : wanted≠fixed) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (request : Source.Domain) (mode : Mode) (scope : UsesSourceMessage fixed request) :
    ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run mode).AllQueriesSatisfy (Allowed wanted) := by
  rcases request with ((coin|request)|report)|bytes
  · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩
  · cases request with
    | create | reveal handle => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩
    | service handle request => cases request with
      | staticDh peer => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩
      | sign message =>
          have other : message≠wanted := by
            intro equal
            subst message
            exact different (scope role)
          exact signing_scope wanted selected handle message mode other
  · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩
  · change (match (RegistrationNativeIdentityCensorCompiler.hashInput mode bytes).input with
      | some _ => (RegistrationNativeIdentityCensorOperational.promote
          (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run mode
      | none => do let reply ← (Old.query (.inr (.template selected mode.target
          (RegistrationNativeIdentityCensorOperational.parts bytes).1 (RegistrationNativeIdentityCensorOperational.parts bytes).2)) : OracleComp Old _)
                   pure (reply,mode)).AllQueriesSatisfy _
    split
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩
    · exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,fun _=>trivial⟩

private theorem program_scope (fixed wanted : Pqxdh.Bytes) (selected : Nat) (placeholder : Ed25519Signature)
    (different : wanted≠fixed) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp Source A) (scope : work.AllQueriesSatisfy (UsesSourceMessage fixed)) (mode : Mode) :
    ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode).AllQueriesSatisfy (Allowed wanted) := by
  induction work using OracleComp.inductionOn generalizing mode with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at scope
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
      exact allQueriesSatisfy_bind (query_scope fixed wanted selected placeholder different role request mode scope.1)
        (fun result=>ih result.1 (scope.2 result.1) result.2)

private theorem ordinary_fresh (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (wanted : Pqxdh.Bytes)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain)
    (allowed : Allowed wanted (.inl (.inl (.inl (.inl request)))))
    (before : State) (result : PqxdhJointPhase1Reports.ProtocolSpec.Range request × State)
    (supported : result∈support ((RegistrationNativeIdentityCensorSource.protocol joint request).run before))
    (fresh : wanted∉poolMessages selected before.pool) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true) :
    wanted∉poolMessages selected result.2.pool := by
  have projected : (result.1,(result.2.pool,result.2.hash))∈support
      ((RegistrationNativePlatformIdentityCtxSource.implementation joint (.inl request)).run (before.pool,before.hash)) := by
    simp only [RegistrationNativeIdentityCensorSource.protocol,StateT.run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    simp only [RegistrationNativePlatformIdentityCtxSource.implementation,StateT.run,support_map]
    exact ⟨inner,called,rfl⟩
  intro member
  by_cases quiet : RegistrationNativePlatformIdentityCtxSigningHistoryFrame.NoSignFor selected (.inl request)
  · have same := RegistrationNativePlatformIdentityCtxSigningHistoryFrame.query joint selected (.inl request) quiet
      (before.pool,before.hash) (result.1,(result.2.pool,result.2.hash)) projected
    change poolMessages selected result.2.pool=poolMessages selected before.pool at same
    rw [same] at member
    exact fresh member
  · rcases request with (coin|request)|report
    · exact quiet trivial
    · cases request with
      | create | reveal handle => exact quiet trivial
      | service handle request => cases request with
        | staticDh peer => exact quiet trivial
        | sign message =>
            have crossed := RegistrationNativePlatformIdentityCtxOneTimeMessageHistory.query joint selected message
              (.inl (.inl (.inr (.service handle (.sign message))))) (fun _=>rfl)
              (before.pool,before.hash) (result.1,(result.2.pool,result.2.hash)) projected wanted member role
            exact crossed.elim fresh (fun equal=>allowed equal.symm)
    · exact quiet trivial

private theorem query_fresh (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (request : Old.Domain) (allowed : Allowed wanted request) (before : State) (fresh : wanted∉poolMessages selected before.pool)
    (result : Old.Range request × State)
    (supported : result∈support ((RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked request).run before)) :
    wanted∉poolMessages selected result.2.pool := by
  rcases request with (((protocol|message)|scanned)|described)|marker
  · have lower : RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked
        (.inl (.inl (.inl (.inl protocol))))=RegistrationNativeIdentityCensorSource.protocol joint protocol := by
      cases masked <;> rfl
    rw [lower] at supported
    exact ordinary_fresh joint selected wanted protocol allowed before result supported fresh role
  · cases masked <;>
      simp only [RegistrationNativeIdentityCensorTargetSync.lower,Bool.false_eq_true,ite_false,ite_true,
        RegistrationNativeIdentityCensorSource.censored,RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.select,StateT.run] at supported
    all_goals split at supported
    all_goals obtain rfl := eq_of_mem_support_pure _ supported
    all_goals exact fresh
  · cases masked <;>
      change result∈support (pure ((),before)) at supported
    all_goals obtain rfl := eq_of_mem_support_pure _ supported
    all_goals exact fresh
  · cases masked <;>
      simp only [RegistrationNativeIdentityCensorTargetSync.lower,Bool.false_eq_true,ite_false,ite_true,
        RegistrationNativeIdentityCensorSource.censored,RegistrationNativeIdentityCensorSource.implementation,
        RegistrationNativeIdentityCensorSource.physical,StateT.run,support_map] at supported
    all_goals obtain ⟨inner,_called,rfl⟩ := supported
    all_goals exact fresh
  · cases marker with
    | template handle message leading trailing =>
        cases masked <;>
          simp only [RegistrationNativeIdentityCensorTargetSync.lower,Bool.false_eq_true,ite_false,ite_true,
            RegistrationNativeIdentityCensorSource.censored,RegistrationNativeIdentityCensorSource.implementation,
            RegistrationNativeIdentityCensorSource.template,RegistrationNativeIdentityCensorSource.physical,
            StateT.run,Functor.map_map,support_map] at supported
        all_goals obtain ⟨inner,_called,rfl⟩ := supported
        all_goals exact fresh
    | omitted handle message =>
        have run_fresh (out : Option Ed25519Signature × State)
            (called : out∈support ((RegistrationNativeIdentityCensorSource.omitted joint selected handle message).run before)) :
            wanted∉poolMessages selected out.2.pool := by
          simp only [RegistrationNativeIdentityCensorSource.omitted,StateT.run,support_map] at called
          obtain ⟨inner,called,rfl⟩ := called
          have protocol : (inner.1,{before with pool:=inner.2})∈support
              ((RegistrationNativeIdentityCensorSource.protocol joint (.inl (.inr (.service handle (.sign message))))).run before) := by
            simp only [RegistrationNativeIdentityCensorSource.protocol,StateT.run,support_map]
            exact ⟨inner,called,rfl⟩
          exact ordinary_fresh joint selected wanted (.inl (.inr (.service handle (.sign message)))) allowed before (inner.1,{before with pool:=inner.2}) protocol fresh role
        cases masked with
        | false => exact run_fresh result supported
        | true =>
            change result∈support (do
              let called ← (RegistrationNativeIdentityCensorSource.omitted joint selected handle message).run before
              pure (some placeholder,called.2)) at supported
            rw [mem_support_bind_iff] at supported
            obtain ⟨called,queried,returned⟩ := supported
            obtain rfl := eq_of_mem_support_pure _ returned
            exact run_fresh called queried

private theorem program_fresh (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp Old A) (scope : work.AllQueriesSatisfy (Allowed wanted))
    (before : State) (fresh : wanted∉poolMessages selected before.pool) (result : A × State)
    (supported : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked) work).run before)) :
    wanted∉poolMessages selected result.2.pool := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact fresh
  | query_bind request next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at scope
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact ih middle.1 (scope.2 middle.1) middle.2
        (query_fresh joint selected placeholder masked wanted role request scope.1 before fresh middle called) result continued

/-- A genuine private signing-history crossing identifies the actual source operand under either frontend reply interpretation. -/
theorem crossing (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) (fixed wanted : Pqxdh.Bytes) (role : RegistrationNativeIdentitySigningRole.oneTime wanted=true)
    (work : OracleComp Source A) (scope : work.AllQueriesSatisfy (UsesSourceMessage fixed))
    (mode : Mode) (before : State) (fresh : wanted∉poolMessages selected before.pool) (result : (A × Mode) × State)
    (supported : result∈support ((simulateQ (RegistrationNativeIdentityCensorTargetSync.lower joint selected placeholder masked)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run mode)).run before))
    (member : wanted∈poolMessages selected result.2.pool) : wanted=fixed := by
  by_contra different
  exact program_fresh joint selected placeholder masked wanted role _
    (program_scope fixed wanted selected placeholder different role work scope mode) before fresh result supported member

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorHistory.crossing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorFirstSelectorHistory.crossing
