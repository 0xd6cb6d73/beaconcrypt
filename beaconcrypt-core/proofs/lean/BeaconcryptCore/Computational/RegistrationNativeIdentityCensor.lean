-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityRecognition

/-! A primitive-facing censor omits every signing request for one selected message, forwarding all other actual signatures, static-DH calls and random queries. The selected message's freshness is derived from the actual interpreted signing history. Native selected-publication coverage and its symbolic-hash/source coupling remain separate obligations. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensor
open PqxdhJointIdentity (AdversarySpec IdentitySeed History signedMessages)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {Value : Type}

def Allowed (target : Pqxdh.Bytes) : AdversarySpec.Domain → Prop
  | .inr (.sign message) => message ≠ target
  | _ => True

/-- The placeholder is ordinary client data; neither the challenged seed nor its actual signature is captured. -/
def implementation (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) :
    QueryImpl AdversarySpec (OracleComp AdversarySpec)
  | .inl query => AdversarySpec.query (.inl query)
  | .inr (.sign message) => if message = target then pure placeholder else AdversarySpec.query (.inr (.sign message))
  | .inr (.staticDh peer) => AdversarySpec.query (.inr (.staticDh peer))

private theorem query_allowed (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) (query : AdversarySpec.Domain) :
    AllQueriesSatisfy (implementation target placeholder query) (Allowed target) := by
  cases query with
  | inl query => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  | inr query => cases query with
    | staticDh peer => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
    | sign message =>
      by_cases same : message = target
      · simp only [implementation, same, ite_true]; trivial
      · simp only [implementation, same, ite_false]
        exact (allQueriesSatisfy_query_iff _ _).mpr same

/-- All adaptive branches of the censored client omit the target signing request, including repeated aliases of its message. -/
theorem no_target (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) (work : OracleComp AdversarySpec Value) :
    AllQueriesSatisfy (simulateQ (implementation target placeholder) work) (Allowed target) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact allQueriesSatisfy_bind (query_allowed target placeholder query) ih

private theorem step_fresh (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (target : Pqxdh.Bytes) (history : History) (prior : target ∉ signedMessages history)
    (query : AdversarySpec.Domain) (allowed : Allowed target query)
    (result : AdversarySpec.Range query × History)
    (reached : result ∈ support ((PqxdhJointIdentity.jointImpl primitives seed query).run history)) :
    target ∉ signedMessages result.2 := by
  cases query with
  | inl query =>
    simp only [PqxdhJointIdentity.jointImpl, StateT.run, bind_pure_comp, support_map] at reached
    obtain ⟨reply, _possible, rfl⟩ := reached
    exact prior
  | inr query => cases query with
    | staticDh peer =>
      simp only [PqxdhJointIdentity.jointImpl, StateT.run, mem_support_pure_iff] at reached
      cases reached
      simpa only [PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.append_nil] using prior
    | sign message =>
      simp only [PqxdhJointIdentity.jointImpl, StateT.run, mem_support_pure_iff] at reached
      cases reached
      simp only [PqxdhJointIdentity.signedMessages, PqxdhJointIdentity.requestEvent, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.mem_append, List.mem_singleton]
      exact fun present => present.elim prior (fun same => allowed same.symm)

/-- Actual ordinary signing history stays fresh for every submitted query of an adaptive allowed continuation. -/
theorem fresh_run (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (target : Pqxdh.Bytes) (work : OracleComp AdversarySpec Value) (allowed : AllQueriesSatisfy work (Allowed target))
    (history : History) (prior : target ∉ signedMessages history) (result : Value × History)
    (reached : result ∈ support ((simulateQ (PqxdhJointIdentity.jointImpl primitives seed) work).run history)) :
    target ∉ signedMessages result.2 := by
  induction work using OracleComp.inductionOn generalizing history result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
    cases reached
    exact prior
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨middle, initial, continued⟩ := reached
    exact ih middle.1 (later middle.1) middle.2 (step_fresh primitives seed target history prior query first middle initial) result continued

/-- The actual primitive challenger sees no target-message signing request in the complete censored run; no freshness premise about its final history is assumed. -/
theorem censored_fresh (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (target : Pqxdh.Bytes) (placeholder : Ed25519Signature) (work : OracleComp AdversarySpec Value)
    (history : History) (prior : target ∉ signedMessages history) (result : Value × History)
    (reached : result ∈ support ((simulateQ (PqxdhJointIdentity.jointImpl primitives seed)
      (simulateQ (implementation target placeholder) work)).run history)) :
    target ∉ signedMessages result.2 :=
  fresh_run primitives seed target _ (no_target target placeholder work) history prior result reached

/-- The primitive adversary captures only a message, public program, placeholder and fallback; its challenged seed stays in the ordinary joint interpreter. -/
def reduction (target : Pqxdh.Bytes) (placeholder fallback : Ed25519Signature)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp AdversarySpec (Option Ed25519Signature))
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) : OracleComp AdversarySpec PqxdhJointIdentity.Forgery := do
  let candidate ← simulateQ (implementation target placeholder) (work publicIdentity)
  pure ⟨target, candidate.getD fallback⟩

/-- Actual recognition signal under the censored primitive source; arbitrary invalid candidates are rejected by public verification. -/
def observed (primitives : PqxdhJointIdentity.Primitives) (target : Pqxdh.Bytes) (placeholder : Ed25519Signature)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp AdversarySpec (Option Ed25519Signature)) : ProbComp Bool := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let result ← (simulateQ (PqxdhJointIdentity.jointImpl primitives seed)
    (simulateQ (implementation target placeholder) (work (primitives.publicKeys seed)))).run []
  pure (result.1.any (primitives.verify (primitives.publicKeys seed).ed25519 target))

private theorem captured (primitives : PqxdhJointIdentity.Primitives) (seed : IdentitySeed)
    (target : Pqxdh.Bytes) (placeholder fallback : Ed25519Signature) (work : OracleComp AdversarySpec (Option Ed25519Signature))
    (result : Option Ed25519Signature × History)
    (reached : result ∈ support ((simulateQ (PqxdhJointIdentity.jointImpl primitives seed)
      (simulateQ (implementation target placeholder) work)).run []))
    (valid : result.1.any (primitives.verify (primitives.publicKeys seed).ed25519 target) = true) :
    PqxdhJointIdentity.wins primitives (primitives.publicKeys seed) ⟨target, result.1.getD fallback⟩ result.2 = true := by
  have fresh := censored_fresh primitives seed target placeholder work [] (by simp only [signedMessages, List.filterMap_nil, List.not_mem_nil, not_false_eq_true]) result reached
  rcases result with ⟨candidate, history⟩
  cases candidate with
  | none => simp only [Option.any_none, Bool.false_eq_true] at valid
  | some signature =>
    simpa only [Option.any_some, PqxdhJointIdentity.wins, Option.getD_some,
      fresh, decide_false, Bool.not_false, Bool.and_true] using valid

/-- The literal recognition signal has one ordinary joint Ed/static-DH weak-EUF bill. Target freshness is derived from omitted signing requests, not a supplied final-history/security conclusion. -/
theorem recognition_bound (primitives : PqxdhJointIdentity.Primitives) (target : Pqxdh.Bytes)
    (placeholder fallback : Ed25519Signature)
    (work : PqxdhJointIdentity.PublicIdentity → OracleComp AdversarySpec (Option Ed25519Signature)) :
    Pr{let accepted ← observed primitives target placeholder work}[accepted = true] ≤
      PqxdhJointIdentity.advantage primitives (reduction target placeholder fallback work) := by
  unfold observed PqxdhJointIdentity.advantage PqxdhJointIdentity.game PqxdhJointIdentity.run reduction
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro seed _
  apply prEvent_bind_mono_of_forall_le_of_support
  intro result reached
  by_cases valid : result.1.any (primitives.verify (primitives.publicKeys seed).ed25519 target) = true
  · have wins := captured primitives seed target placeholder fallback _ result reached valid
    simp only [prEvent_pure, valid, wins, ite_true]
    exact le_rfl
  · simp only [prEvent_pure, valid, Bool.false_eq_true, ite_false, zero_le]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.no_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.no_target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.fresh_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.fresh_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.censored_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.censored_fresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.recognition_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensor.recognition_bound
