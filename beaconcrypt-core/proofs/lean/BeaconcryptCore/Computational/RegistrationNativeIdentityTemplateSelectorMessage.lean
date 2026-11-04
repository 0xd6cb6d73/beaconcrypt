-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleMessageScope
import BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateCensorRecognition
/-! Actual selector queries name only the original role-one-time source operand. A captured bundle therefore determines its selected message without a private within-bundle guess. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorCompiler (Mode)
open RegistrationNativePlatformIdentityCtxBundleMessageScope (UsesSourceMessage)
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec
abbrev Target := RegistrationNativeIdentityTemplateCensorRecognition.Spec
variable {A : Type}

def Allowed (message : Pqxdh.Bytes) : Target.Domain → Prop
  | .inl (.inl (.inr current)) => current = message
  | _ => True

private theorem prepare_scope (wanted : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes)
    (before : Mode) (placeholder : Ed25519Signature)
    (allowed : RegistrationNativeIdentitySigningRole.oneTime message = true → message = wanted) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (RegistrationNativeIdentityCensorCompiler.prepare selected handle message)).run before)).AllQueriesSatisfy (Allowed wanted) := by
  unfold RegistrationNativeIdentityCensorOperational.promote RegistrationNativeIdentityCensorCompiler.prepare
  dsimp only [StateT.run]
  split
  · rename_i eligible
    split
    · simp only [simulateQ_bind, RegistrationNativeIdentityCensorCompiler.select, simulateQ_spec_query,
        RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase]
      apply allQueriesSatisfy_bind
      · exact (allQueriesSatisfy_query_iff _ _).mpr (allowed eligible.2)
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
          · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
          · intro inspected
            exact allQueriesSatisfy_pure _ _
    · simp only [pure_bind]
      exact allQueriesSatisfy_pure _ _
  · simp only [simulateQ_pure]
    exact allQueriesSatisfy_pure _ _
private theorem lift_scope (wanted : Pqxdh.Bytes) (placeholder : Ed25519Signature)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec A)
    (safe : (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder) work).AllQueriesSatisfy (Allowed wanted))
    (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((StateT.lift work : StateT Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec) A).run before)).AllQueriesSatisfy (Allowed wanted) := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (do let answer ← work; pure (answer,before))).AllQueriesSatisfy _
  rw [simulateQ_bind]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

private theorem signing_scope (wanted : Pqxdh.Bytes) (selected handle : Nat) (message : Pqxdh.Bytes) (before : Mode) (placeholder : Ed25519Signature)
    (allowed : RegistrationNativeIdentitySigningRole.oneTime message = true → message = wanted) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.signing selected handle message).run before)).AllQueriesSatisfy (Allowed wanted) := by
  rw [RegistrationNativeIdentityCensorOperational.signing, StateT.run_bind, simulateQ_bind]
  apply allQueriesSatisfy_bind (prepare_scope wanted selected handle message before placeholder allowed)
  intro prepared
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split
  · apply lift_scope
    rw [simulateQ_spec_query]
    exact allQueriesSatisfy_pure _ _
  · apply lift_scope
    simp only [RegistrationNativeIdentityCensorOperational.embed, simulateQ_spec_query,
      RegistrationNativeIdentityTemplateCensorRecognition.erase]
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem hash_scope (wanted : Pqxdh.Bytes) (selected : Nat) (placeholder : Ed25519Signature) (bytes : Pqxdh.Bytes) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before)).AllQueriesSatisfy (Allowed wanted) := by
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
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _
  | some input =>
    unfold RegistrationNativeIdentityCensorCompiler.implementation
    dsimp only [StateT.run]
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeIdentityCensorOperational.embed,
      RegistrationNativeIdentityTemplateCensorRecognition.erase, simulateQ_pure]
    apply allQueriesSatisfy_bind
    · exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    · intro reply
      exact allQueriesSatisfy_pure _ _

private theorem protocol_scope (wanted : Pqxdh.Bytes) (placeholder : Ed25519Signature)
    (request : PqxdhJointPhase1Reports.ProtocolSpec.Domain) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.promote
        (StateT.lift (RegistrationNativeIdentityCensorCompiler.protocol request))).run before)).AllQueriesSatisfy (Allowed wanted) := by
  change (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
    (simulateQ RegistrationNativeIdentityCensorOperational.embed
      (do let answer ← RegistrationNativeIdentityCensorCompiler.protocol request; pure (answer,before)))).AllQueriesSatisfy _
  rw [simulateQ_bind, simulateQ_bind]
  apply allQueriesSatisfy_bind
  · simp only [RegistrationNativeIdentityCensorCompiler.protocol, simulateQ_spec_query,
      RegistrationNativeIdentityCensorOperational.embed, RegistrationNativeIdentityTemplateCensorRecognition.erase]
    exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  · intro answer
    exact allQueriesSatisfy_pure _ _


/-- A literal source leaf can select only its role-one-time source operand. -/
theorem query (wanted : Pqxdh.Bytes) (selected : Nat) (placeholder : Ed25519Signature)
    (request : Source.Domain) (before : Mode) (allowed : UsesSourceMessage wanted request) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((RegistrationNativeIdentityCensorOperational.implementation selected placeholder request).run before)).AllQueriesSatisfy (Allowed wanted) := by
  rcases request with ((coin | request) | report) | bytes
  · exact protocol_scope wanted placeholder _ before
  · cases request with
    | create | reveal handle => exact protocol_scope wanted placeholder _ before
    | service handle request => cases request with
      | staticDh peer => exact protocol_scope wanted placeholder _ before
      | sign message => exact signing_scope wanted selected handle message before placeholder allowed
  · exact protocol_scope wanted placeholder _ before
  · exact hash_scope wanted selected placeholder bytes before

/-- All adaptive source continuations retain that same source-derived selected message. -/
theorem program (wanted : Pqxdh.Bytes) (selected : Nat) (placeholder : Ed25519Signature)
    (work : OracleComp Source A) (before : Mode) (allowed : work.AllQueriesSatisfy (UsesSourceMessage wanted)) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) work).run before)).AllQueriesSatisfy (Allowed wanted) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    exact allQueriesSatisfy_pure _ _
  | query_bind request next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply allQueriesSatisfy_bind (query wanted selected placeholder request before allowed.1)
    intro result
    exact ih result.1 result.2 (allowed.2 result.1)

open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
/-- The actual captured bundle determines every selector's message from its original tuple, without a private within-bundle guess or successful signing premise. -/
theorem bundled (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (started : beaconcrypt_core.pqxdh.BeaconStart)
    (built : beaconcrypt_core.pqxdh.beacon_start (beaconcrypt_core.pqxdh.BeaconFresh.mk owner.pin.binding) (RegistrationNativeIdentityFrontend.inputs owner)
      (beaconcrypt_core.pqxdh.BeaconCoins.mk (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))) = .ok started)
    (tagged : RegistrationNativeIdentitySigningRole.Tagged started)
    (selected : Nat) (placeholder : Ed25519Signature)
    (nativeBefore : RegistrationNativeIdentityMain.State n KemSK source × Platform) (before : Mode) :
    (simulateQ (RegistrationNativeIdentityTemplateCensorRecognition.erase placeholder)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
        ((RegistrationNativePlatformIdentityCtxMain.beacon setup checks representation created
          (RegistrationNativePlatformIdentityBundle.bundled (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
            setup index owner scalar writer)).run nativeBefore)).run before)).AllQueriesSatisfy
              (Allowed (PqxdhRefinement.absBytes started.message.one_time_key)) := by
  exact program _ selected placeholder _ before
    (RegistrationNativePlatformIdentityCtxBundleMessageScope.bundled setup checks representation created index owner scalar writer
      started built tagged nativeBefore)

end BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.bundled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityTemplateSelectorMessage.bundled
