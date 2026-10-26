-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealGuess
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly

/-!
# `anomaly_le`: the Beacon-side anomaly is bounded by the KEM ciphertext guess (CE-11b, unit U4)

The second half of `anomaly_le` (design-v2 section 7.2, item 6). On the record world with the ideal environment of a target, under `Phase1ReadBack` and `Phase2ReadBack`, the Beacon-side anomaly `PqxdhDeploymentIdealTrace.Anomaly` has probability at most `ctGuessPk` (`anomaly_le_pk_sup`), hence at most `ctGuess` (`anomaly_le`); so has the anomaly on a prefix of the transcript, the exceptional alternative of `PqxdhDeploymentIdealBeacon.ideal_slots_prefix` (`anomaly_prefix_le_pk_sup`, `anomaly_prefix_le`).

- The anomaly, and the anomaly on a prefix, imply a public event of the transcript and the drawn parameters, that the transcript guess is the challenge ciphertext (`PqxdhDeploymentIdealGuess.anomaly_guess`, `PqxdhDeploymentIdealGuess.anomaly_prefix_guess`), whose probability is the same on the challenger's draws followed by the final split game (`PqxdhDeploymentIdealEnv.c1_split`); `guess_le_pk_sup` bounds that event on the record world by `ctGuessPk` without a read-back premise.
- The final split game does not read the challenge ciphertext before the selected raw accept: while the selected accept was not active and marked no session, every command other than the selected raw accept is the same at every challenge (`idealSplit_challenge`, `handler_challenge`, through the U3 bridges `PqxdhDeploymentIdealEnvStep.idealSplit_*`; `coinSend_same` for the secrecy layer's coins and sends). On the game flattened with the secrecy layer (`splitHandler`, `splitHandler_run`), the joint states before the selected raw accept (`Early`: the transcript's raw accept attempts are the accept counter, at most the selected ordinal, the selected accept neither active nor marking) are kept by every other step (`handler_backend`, `splitHandler_transcript`, `early_step`, `early_initial`), the selected raw accept stops both runs with the guess of the same transcript (`SelectedQ`, `cutAt_selected`, `stopGuess`, `selected_stop`), and the guess does not change after it (`stopGuess_keeps`). So the two games at different challenges are coupled identically until the selected raw accept (`split_step`) and the guess has the same law at every challenge (`split_guess_law`, `guessView`, `game_guess`, `game_guess_law`, with `PqxdhDeploymentIdealGuess.lawEq_until_stop`).
- The challenge encapsulation is then drawn after the guess (`LazyOracleDiscard.lawEq_swap`), and a guess of the key pair made before the encapsulation hits it with probability at most `ctGuessPk`, through the best guess of the public key (`pairGuess_le`, with `PqxdhDeploymentIdealAnomaly.encapsHit_max`); `split_guess_le` is the bound on the split side, `evalDist_decide_mono` the support monotonicity of Boolean observations.

`ctGuessPk` is a supremum over all functions of the public key, an information-theoretic quantity of the scheme that no approved assumption bounds (plan section 40). The form that CE-12a's IND-CCA reduction consumes, the anomaly bounded by `PqxdhDeploymentIdealAnomaly.ctGuessBy` at a guesser program constructed from the adversary that does not read the selected secret key (`anomaly_le_pk`, and its prefix form), is not proved here: the guess above is a random variable of the whole selected key pair. It is planned for the follow-up module `PqxdhDeploymentIdealAnomalyGuesser`. These are equalities in law and bounds; no assumption is added.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptCount)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentIdealGuess (guessCt cutAt UntilStop)

variable {KemSK : Type}

/-! ### Handlers that agree on coins and sends -/

section Agree
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A native-interface program that issues only coins and sends runs the same under the handler with any two registration handlers. -/
theorem coinSend_same {Bk : Type} {n : ℕ} {Value : Type} (reg₁ reg₂ : PqxdhDeploymentBackend.RegImpl KemSK Bk n)
    (program : OracleComp PqxdhDeploymentInterface.Spec Value)
    (bounded : program.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (x : XState KemSK Bk n) :
    (simulateQ (handlerWith setup codec route reg₁) program).run x =
      (simulateQ (handlerWith setup codec route reg₂) program).run x := by
  induction program using OracleComp.inductionOn generalizing x with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have kind : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      have restBound : ∀ reply, (next reply).IsQueryBoundP
          (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0 := fun reply => by
        have bound := rest reply
        simp only [kind, Bool.true_eq_false, ite_false] at bound
        exact bound
      have first : handlerWith setup codec route reg₁ query = handlerWith setup codec route reg₂ query := by
        rcases query with coin | command
        · rfl
        · cases command <;> first | rfl | simp [PqxdhDeploymentSecrecy.coinOrSend] at kind
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, first]
      exact bind_congr fun step => ih step.1 (restBound step.1) step.2

end Agree


/-! ### The final split game before the selected raw accept does not read the challenge -/

section Challenge
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The challenger's parameters with another challenge ciphertext. -/
def withChallenge (p : Params KemSK count) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) : Params KemSK count :=
  { p with challenge := challenge }

/-- A query of the native interface is the selected raw accept at an extended state: a raw accept made when the accept counter is the selected ordinal. -/
def SelectedAt (t : Target count) (x : XState KemSK SplitBk 2) : PqxdhDeploymentInterface.Spec.Domain → Prop
  | .inr (.accept _) => x.backend.2.2.accepts = t.accept
  | _ => False

/-- Before the selected raw accept, while no session is marked and the selected accept was not active, the final split form does not read the challenge ciphertext: every command other than the selected raw accept is the same at every challenge. -/
theorem idealSplit_challenge (t : Target count) (p : Params KemSK count) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhRecordLiftInterface.EnvQuery)
    (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false) (unmarked : x.backend.2.2.marks = none)
    (other : ¬ SelectedAt t x (.inr query.val)) :
    (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created query).run x =
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t (withChallenge p challenge) created query).run x := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_create, PqxdhDeploymentIdealEnvStep.idealSplit_create]
      rfl
  | bundle owner =>
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_bundle, PqxdhDeploymentIdealEnvStep.idealSplit_bundle]
  | accept raw =>
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_accept_other setup codec route checks t p created raw x other,
        PqxdhDeploymentIdealEnvStep.idealSplit_accept_other setup codec route checks t _ created raw x other]
  | build session payload =>
      have real : ∀ index coords, x.backend.2.2.marks = some (index, coords) →
          ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome) := fun _ _ marked => by
        rw [unmarked] at marked; cases marked
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_build_real setup codec route checks t p created session payload x real,
        PqxdhDeploymentIdealEnvStep.idealSplit_build_real setup codec route checks t _ created session payload x real]
  | finish owner raw =>
      have real : ¬ (x.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt x.base.native.owners owner = true) := fun chosen => by
        rw [inactive] at chosen; cases chosen.1
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t p created owner raw x real,
        PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t _ created owner raw x real]
  | hmac key message =>
      rw [PqxdhDeploymentIdealEnvStep.idealSplit_hmac, PqxdhDeploymentIdealEnvStep.idealSplit_hmac]
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- The handler of the final split form, before the selected raw accept: every query other than the selected raw accept is the same at every challenge. -/
theorem handler_challenge (t : Target count) (p : Params KemSK count) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false) (unmarked : x.backend.2.2.marks = none)
    (other : ¬ SelectedAt t x query) :
    (handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x =
      (handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t
        (withChallenge p challenge) created) query).run x := by
  rcases query with coin | command
  · simp only [handlerWith]
  · cases command with
    | create pin keyId =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.create pin keyId, trivial⟩ x inactive unmarked other
    | bundle owner =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.bundle owner, trivial⟩ x inactive unmarked other
    | accept raw =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.accept raw, trivial⟩ x inactive unmarked other
    | build session payload =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.build session payload, trivial⟩ x inactive unmarked other
    | finish owner raw =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.finish owner raw, trivial⟩ x inactive unmarked other
    | hmac key message =>
        exact idealSplit_challenge setup codec route checks t p challenge created
          ⟨.hmac key message, trivial⟩ x inactive unmarked other
    | _ => simp only [handlerWith]

end Challenge


/-! ### The flattened split game before the selected raw accept -/

section Flat
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The final split form's handler composed with the secrecy layer, on the product of the ledger and the extended state (as `PqxdhDeploymentIdealKeymatch.ledgerHandler` for the ideal registration). -/
noncomputable def splitHandler (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl PqxdhDeploymentInterface.FullSpec (StateT (Ledger × XState KemSK SplitBk 2) ProbComp) :=
  ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)).mapStateTBase
    (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds)).flattenStateT

/-- One step of the flattened split game: the secrecy layer's step run by the handler. -/
theorem splitHandler_run (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) :
    (splitHandler setup codec route checks t p bounds created query).run state =
      (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
        ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run state.1)).run state.2 := rfl

/-- A query of the complete interface is the selected raw accept at a joint state: a raw accept made when the accept counter is the selected ordinal. -/
def SelectedQ (t : Target count) (state : Ledger × XState KemSK SplitBk 2) : PqxdhDeploymentInterface.Query → Prop
  | .inl query => SelectedAt t state.2 query
  | .inr _ => False

/-- The joint state before the selected raw accept: the transcript's raw accept attempts are the accept counter, which is at most the selected ordinal, and the selected accept was neither active nor marked a session. -/
structure Early (t : Target count) (state : Ledger × XState KemSK SplitBk 2) : Prop where
  count : acceptCount state.1.transcript = state.2.backend.2.2.accepts
  before : state.2.backend.2.2.accepts ≤ t.accept
  inactive : state.2.backend.2.2.active = false
  unmarked : state.2.backend.2.2.marks = none

/-- Before the selected raw accept, every query other than the selected raw accept is the same step of the flattened split game at every challenge. -/
theorem splitHandler_challenge (t : Target count) (p : Params KemSK count)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) (early : Early t state) (other : ¬ SelectedQ t state query) :
    (splitHandler setup codec route checks t p bounds created query).run state =
      (splitHandler setup codec route checks t (withChallenge p challenge) bounds created query).run state := by
  rw [splitHandler_run, splitHandler_run]
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      simulateQ_map, simulateQ_spec_query, StateT.run_map,
      handler_challenge setup codec route checks t p challenge created request state.2 early.inactive early.unmarked other]
  · rw [coinSend_same setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t (withChallenge p challenge) created) _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy state.1)]

/-- Every step of the handler of the final split form before the selected raw accept, other than the selected raw accept, keeps the backend, except a raw accept, which runs the real accept on the backend with the accept counter advanced. -/
theorem handler_backend (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false)
    (unmarked : x.backend.2.2.marks = none) (other : ¬ SelectedAt t x query) :
    ∀ result ∈ support ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p
        created) query).run x),
      ((∀ raw, query ≠ .inr (.accept raw)) ∧ result.2.backend = x.backend) ∨
        ((∃ raw, query = .inr (.accept raw)) ∧ x.backend.2.2.accepts ≠ t.accept ∧
          result.2.backend = PqxdhDeploymentIdealEnvStep.bump x.backend) := by
  intro result member
  have notAccept : ∀ (command : PqxdhDeploymentInterface.Command), (∀ raw, command ≠ .accept raw) →
      ∀ raw, (Sum.inr command : PqxdhDeploymentInterface.Spec.Domain) ≠ .inr (.accept raw) :=
    fun command other raw same => other raw (Sum.inr.inj same)
  rcases query with coin | command
  · refine Or.inl ⟨(fun raw same => by cases same), ?_⟩
    simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · cases command with
    | create pin keyId =>
        refine Or.inl ⟨notAccept _ (fun _ same => by cases same), ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.create pin keyId, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_create] at member
        exact (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1
    | bundle owner =>
        refine Or.inl ⟨notAccept _ (fun _ same => by cases same), ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.bundle owner, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_bundle] at member
        exact (PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
          ⟨.bundle owner, trivial⟩ x result member).2
    | accept raw =>
        refine Or.inr ⟨⟨raw, rfl⟩, other, ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.accept raw, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_accept_other setup codec route checks t p created raw x other]
          at member
        exact (PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
          ⟨.accept raw, trivial⟩ _ result member).2
    | build session payload =>
        refine Or.inl ⟨notAccept _ (fun _ same => by cases same), ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.build session payload, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_build_real setup codec route checks t p created session payload x
          (fun _ _ marked => by rw [unmarked] at marked; cases marked)] at member
        exact (PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
          ⟨.build session payload, trivial⟩ x result member).2
    | finish owner raw =>
        refine Or.inl ⟨notAccept _ (fun _ same => by cases same), ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.finish owner raw, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t p created owner raw x
          (fun chosen => by rw [inactive] at chosen; cases chosen.1)] at member
        exact (PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
          ⟨.finish owner raw, trivial⟩ x result member).2
    | hmac key message =>
        refine Or.inl ⟨notAccept _ (fun _ same => by cases same), ?_⟩
        change result ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
          ⟨.hmac key message, trivial⟩).run x) at member
        rw [PqxdhDeploymentIdealEnvStep.idealSplit_hmac] at member
        exact (PqxdhDeploymentIdealKeymatch.realRegAt_support setup codec route checks created
          ⟨.hmac key message, trivial⟩ x result member).2
    | hash bytes =>
        exact Or.inl ⟨notAccept _ (fun _ same => by cases same),
          (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1⟩
    | serverSend keyId plaintext =>
        exact Or.inl ⟨notAccept _ (fun _ same => by cases same),
          (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1⟩
    | serverRaw raw =>
        exact Or.inl ⟨notAccept _ (fun _ same => by cases same),
          (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1⟩
    | beaconSend owner plaintext =>
        exact Or.inl ⟨notAccept _ (fun _ same => by cases same),
          (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1⟩
    | beaconRaw owner raw =>
        exact Or.inl ⟨notAccept _ (fun _ same => by cases same),
          (PqxdhDeploymentIdealKeymatch.onBase_support _ x result member).1⟩

/-- Every step of the flattened split game appends exactly one entry, the query with its reply, to the transcript. -/
theorem splitHandler_transcript (t : Target count) (p : Params KemSK count)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Query) (state : Ledger × XState KemSK SplitBk 2) :
    ∀ result ∈ support ((splitHandler setup codec route checks t p bounds created query).run state),
      result.2.1.transcript = state.1.transcript ++ [⟨query, result.1⟩] := by
  intro result member
  rw [splitHandler_run, support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at reachedMember
    obtain ⟨answer, _, rfl⟩ := reachedMember
    rfl
  · have value : reached.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds
        (.inr secrecy)).run state.1) := by
      apply OracleComp.support_simulateQ_run'_subset (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) _ state.2
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, reachedMember, rfl⟩
    exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      state.1 reached.1 value

/-- Every step of the flattened split game before the selected raw accept, other than the selected raw accept, stays before it. -/
theorem early_step (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) (early : Early t state) (other : ¬ SelectedQ t state query) :
    ∀ result ∈ support ((splitHandler setup codec route checks t p bounds created query).run state),
      Early t result.2 := by
  intro result member
  have transcriptEq := splitHandler_transcript setup codec route checks t p bounds created query state result member
  rw [splitHandler_run, support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  have backendFact : ((∀ raw reply, (⟨query, reached.1.1⟩ : Entry) ≠ ⟨.inl (.inr (.accept raw)), reply⟩) ∧
      reached.2.backend = state.2.backend) ∨
      ((∃ raw reply, (⟨query, reached.1.1⟩ : Entry) = ⟨.inl (.inr (.accept raw)), reply⟩) ∧
        state.2.backend.2.2.accepts ≠ t.accept ∧ reached.2.backend = PqxdhDeploymentIdealEnvStep.bump state.2.backend) := by
    rcases query with request | secrecy
    · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        support_map] at reachedMember
      obtain ⟨answer, answerMember, rfl⟩ := reachedMember
      rcases handler_backend setup codec route checks t p created request state.2 early.inactive early.unmarked other
        answer answerMember with ⟨notAccept, backend⟩ | ⟨⟨raw, rfl⟩, ne, backend⟩
      · refine Or.inl ⟨fun raw reply same => ?_, backend⟩
        have queries := congrArg Entry.query same
        exact notAccept raw (Sum.inl.inj queries)
      · exact Or.inr ⟨⟨raw, answer.1, rfl⟩, ne, backend⟩
    · refine Or.inl ⟨fun raw reply same => ?_, ?_⟩
      · have queries := congrArg Entry.query same
        cases queries
      · exact (PqxdhDeploymentIdealKeymatch.coinSend_keeps setup codec route _ _
          (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy state.1)
          state.2 reached reachedMember).1
  change Early t (reached.1.2, reached.2)
  change reached.1.2.transcript = state.1.transcript ++ [⟨query, reached.1.1⟩] at transcriptEq
  rcases backendFact with ⟨notAccept, backend⟩ | ⟨⟨raw, reply, same⟩, ne, backend⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change acceptCount reached.1.2.transcript = reached.2.backend.2.2.accepts
      rw [transcriptEq, PqxdhDeploymentIdealTrace.acceptCount_other _ _ notAccept, backend]
      exact early.count
    · change reached.2.backend.2.2.accepts ≤ t.accept
      rw [backend]; exact early.before
    · change reached.2.backend.2.2.active = false
      rw [backend]; exact early.inactive
    · change reached.2.backend.2.2.marks = none
      rw [backend]; exact early.unmarked
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change acceptCount reached.1.2.transcript = reached.2.backend.2.2.accepts
      rw [transcriptEq, same, PqxdhDeploymentIdealTrace.acceptCount_accept, backend, early.count]
      rfl
    · change reached.2.backend.2.2.accepts ≤ t.accept
      rw [backend]
      have below := early.before
      change state.2.backend.2.2.accepts + 1 ≤ t.accept
      omega
    · change reached.2.backend.2.2.active = false
      rw [backend]; exact early.inactive
    · change reached.2.backend.2.2.marks = none
      rw [backend]; exact early.unmarked

/-- The cut at ordinal `n` of a transcript with `n` raw accept attempts is unchanged by a further raw accept. -/
theorem cutAt_selected (n : ℕ) (transcript : List Entry) (count : acceptCount transcript = n) (raw : Pqxdh.Bytes)
    (reply : Option ℕ) :
    cutAt n (transcript ++ [⟨.inl (.inr (.accept raw)), reply⟩]) = cutAt n transcript := by
  induction transcript generalizing n with
  | nil =>
      change 0 = n at count
      subst count
      rfl
  | cons entry rest ih =>
      rw [PqxdhDeploymentIdealGuess.acceptCount_cons] at count
      rcases entry with ⟨(coin | command) | secrecy, reply'⟩
      · simp only [List.cons_append, PqxdhDeploymentIdealGuess.cutAt]
        rw [ih n count]
      · cases command with
        | accept raw' =>
            cases n with
            | zero => simp only at count; omega
            | succ n =>
                simp only [List.cons_append, PqxdhDeploymentIdealGuess.cutAt]
                rw [ih n (by simp only at count; omega)]
        | _ =>
            simp only [List.cons_append, PqxdhDeploymentIdealGuess.cutAt]
            rw [ih n count]
      · simp only [List.cons_append, PqxdhDeploymentIdealGuess.cutAt]
        rw [ih n count]

/-- The stop of the flattened split game: once the selected raw accept happened, the transcript guess. -/
def stopGuess (t : Target count) (state : Ledger × XState KemSK SplitBk 2) :
    Option (Option PqxdhKemIndCca.MlKem768Ciphertext) :=
  if t.accept < acceptCount state.1.transcript then some (guessCt codec t state.1.transcript) else none

/-- Every step of the flattened split game keeps a stopped state's guess. -/
theorem stopGuess_keeps (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) (value : Option PqxdhKemIndCca.MlKem768Ciphertext)
    (stopped : stopGuess codec t state = some value) :
    ∀ result ∈ support ((splitHandler setup codec route checks t p bounds created query).run state),
      stopGuess codec t result.2 = some value := by
  intro result member
  have transcriptEq := splitHandler_transcript setup codec route checks t p bounds created query state result member
  unfold stopGuess at stopped ⊢
  split at stopped
  · rename_i later
    have later' : t.accept < acceptCount result.2.1.transcript := by
      rw [transcriptEq]
      exact lt_of_lt_of_le later (PqxdhDeploymentIdealBeacon.acceptCount_prefix _ _)
    simp only [later', ↓reduceIte, Option.some.injEq]
    rw [transcriptEq, PqxdhDeploymentIdealGuess.guessCt_append codec t _ _ later]
    exact Option.some.inj stopped
  · cases stopped

/-- The selected raw accept stops the flattened split game, at every challenge, with the guess of the transcript before it. -/
theorem selected_stop (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) (early : Early t state) (selected : SelectedQ t state query) :
    ∀ result ∈ support ((splitHandler setup codec route checks t p bounds created query).run state),
      stopGuess codec t result.2 = some (guessCt codec t state.1.transcript) := by
  intro result member
  have transcriptEq := splitHandler_transcript setup codec route checks t p bounds created query state result member
  rcases query with (coin | command) | secrecy
  · exact absurd selected id
  · cases command with
    | accept raw =>
        have count : acceptCount state.1.transcript = t.accept := early.count.trans selected
        unfold stopGuess
        rw [transcriptEq, PqxdhDeploymentIdealTrace.acceptCount_accept, count]
        simp only [Nat.lt_succ_self, ↓reduceIte, Option.some.injEq]
        unfold guessCt PqxdhDeploymentIdealGuess.earlyFinish
        rw [cutAt_selected t.accept _ count raw]
    | _ => exact absurd selected id
  · exact absurd selected id

/-- The coupling step: from equal joint states before the selected raw accept, the flattened split game at a challenge and at another challenge take the same step and stay equal and before the selected raw accept, or both stop with the same guess at the selected raw accept. -/
theorem split_step (t : Target count) (p : Params KemSK count) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Query) (state₁ state₂ : Ledger × XState KemSK SplitBk 2)
    (related : state₁ = state₂ ∧ Early t state₁) :
    RelTriple ((splitHandler setup codec route checks t p bounds created query).run state₁)
      ((splitHandler setup codec route checks t (withChallenge p challenge) bounds created query).run state₂)
      (UntilStop (fun first second => first = second ∧ Early t first) (stopGuess codec t) (stopGuess codec t)) := by
  obtain ⟨rfl, early⟩ := related
  by_cases selected : SelectedQ t state₁ query
  · exact relTriple_post_mono (PqxdhServerAuthEntryFactor.relTriple_support _ _ _ _
      (selected_stop setup codec route checks t p bounds created query state₁ early selected)
      (selected_stop setup codec route checks t (withChallenge p challenge) bounds created query state₁ early selected))
      fun _ _ both => Or.inr ⟨_, both⟩
  · rw [← splitHandler_challenge setup codec route checks t p challenge bounds created query state₁ early selected]
    exact relTriple_refl_of_mem_support _ fun result member =>
      Or.inl ⟨rfl, rfl, early_step setup codec route checks t p bounds created query state₁ early selected result member⟩

/-- The initial joint state of the flattened split game is before the selected raw accept. -/
theorem early_initial (t : Target count) (created : PqxdhLiveServerConstruction.Created Unit) :
    Early t (Ledger.empty, PqxdhDeploymentBackend.xinitial (KemSK := KemSK) created
      (PqxdhDeploymentIdealSteps.splitInit created)) :=
  ⟨rfl, Nat.zero_le _, rfl, rfl⟩

/-- The law of the transcript guess of the flattened split game does not depend on the challenge: the two simulations are identical until the selected raw accept, which stops both with the guess of the same transcript, and the guess does not change after it (`PqxdhDeploymentIdealGuess.lawEq_until_stop`). -/
theorem split_guess_law {X : Type} (t : Target count) (p : Params KemSK count)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X) :
    LazyOracleDiscard.LawEq ((fun result => guessCt codec t result.2.1.transcript) <$>
        (simulateQ (splitHandler setup codec route checks t p bounds created) adversary).run
          (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)))
      ((fun result => guessCt codec t result.2.1.transcript) <$>
        (simulateQ (splitHandler setup codec route checks t (withChallenge p challenge) bounds created) adversary).run
          (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))) :=
  PqxdhDeploymentIdealGuess.lawEq_until_stop _ _ (fun first second => first = second ∧ Early t first)
    (stopGuess codec t) (stopGuess codec t)
    (fun query state value stopped => stopGuess_keeps setup codec route checks t p bounds created query state value
      stopped)
    (fun query state value stopped => stopGuess_keeps setup codec route checks t (withChallenge p challenge) bounds
      created query state value stopped)
    (fun query state₁ state₂ related => split_step setup codec route checks t p challenge bounds created query state₁
      state₂ related)
    adversary _ _ ⟨rfl, early_initial t created⟩ _ _ fun left right post => by
      rcases post with ⟨_, same, _⟩ | ⟨value, leftStop, rightStop⟩
      · rw [same]
      · unfold stopGuess at leftStop rightStop
        split at leftStop
        · split at rightStop
          · exact (Option.some.inj leftStop).trans (Option.some.inj rightStop).symm
          · cases rightStop
        · cases leftStop

end Flat


/-! ### The transcript guess of the final split game does not depend on the challenge -/

section Game
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The transcript guess of an outcome of the common deployment experiment. -/
def guessView {Out Bk : Type} (t : Target count) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    Out × Ledger × XState KemSK Bk 2)) : Option (Option PqxdhKemIndCca.MlKem768Ciphertext) :=
  outcome.map fun value => guessCt codec t value.2.2.1.transcript

/-- The transcript guess of the final split game is the Server construction followed by the transcript guess of the flattened split game. -/
theorem game_guess (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run' runtime =
      (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime >>=
        fun born => match born.1 with
        | none => pure none
        | some created => (fun result => some (guessCt codec t result.2.1.transcript)) <$>
            (simulateQ (splitHandler setup codec route checks t p bounds created)
              (PqxdhDeploymentInterface.asModeO mode adversary)).run
                (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)) := by
  simp only [PqxdhDeploymentBackend.gameWith, StateT.run'_eq, StateT.run, map_bind]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [map_pure]
    rfl
  · have flat := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
      (handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created))
      (ledgerImpl setup.source.crypto codec setup.serverKeyId bounds) (PqxdhDeploymentInterface.asModeO mode adversary)
      Ledger.empty (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))
    simp only [StateT.run] at flat
    simp only [PqxdhDeploymentSecrecy.wrap, StateT.run, Functor.map_map]
    rw [flat, Functor.map_map]
    rfl

/-- The law of the transcript guess of the final split game does not depend on the challenge. -/
theorem game_guess_law (t : Target count) (p : Params KemSK count) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (runtime : A) :
    LazyOracleDiscard.LawEq
      (guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run' runtime)
      (guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t (withChallenge p challenge)) ensureInit
          identityIndex bounds mode adversary).run' runtime) := by
  rw [game_guess, game_guess]
  refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LazyOracleDiscard.LawEq.refl _
  · have law := split_guess_law setup codec route checks t p challenge bounds created
      (PqxdhDeploymentInterface.asModeO mode adversary)
    have mapped := law.map some
    simpa only [Functor.map_map] using mapped

end Game


/-! ### A guess of the key pair, made before the encapsulation -/

section Guess
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open MeasureTheory

/-- A guess of the challenge ciphertext made from the key pair before the encapsulation to its public key hits it with probability at most `ctGuessPk`: replace each guess by the best guess for the public key (`PqxdhDeploymentIdealAnomaly.encapsHit_max`). The guess is a random variable of the whole key pair; the bound holds through the best guess of the public key. -/
theorem pairGuess_le (guess : PqxdhLiveKemReservation.Pair KemSK →
      ProbComp (Option (Option PqxdhKemIndCca.MlKem768Ciphertext))) :
    𝒟[simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair => guess pair >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some (some encapsulated.1)))] {true} ≤
      PqxdhDeploymentIdealTrace.ctGuessPk setup := by
  let : MeasurableSpace PqxdhKemIndCca.MlKem768Ciphertext := ⊤
  let : DiscreteMeasurableSpace PqxdhKemIndCca.MlKem768Ciphertext := ⟨fun _ => trivial⟩
  let : MeasurableSpace (Option (Option PqxdhKemIndCca.MlKem768Ciphertext)) := ⊤
  let : DiscreteMeasurableSpace (Option (Option PqxdhKemIndCca.MlKem768Ciphertext)) := ⟨fun _ => trivial⟩
  let : MeasurableSpace (PqxdhLiveKemReservation.Pair KemSK) := ⊤
  let : DiscreteMeasurableSpace (PqxdhLiveKemReservation.Pair KemSK) := ⟨fun _ => trivial⟩
  choose best bestMax using PqxdhDeploymentIdealAnomaly.encapsHit_max setup
  refine le_iSup_of_le best ?_
  simp only [simulateQ_bind, simulateQ_pure]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable),
    Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  refine lintegral_mono fun pair => ?_
  rw [evalDist_bind_of_discrete, Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  have never : ∀ guessed : Option (Option PqxdhKemIndCca.MlKem768Ciphertext), (∀ value, guessed ≠ some (some value)) →
      𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
        (pure (decide (guessed = some (some encapsulated.1))) : ProbComp Bool)] {true} = 0 := by
    intro guessed other
    have constant : (fun encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret =>
        (pure (decide (guessed = some (some encapsulated.1))) : ProbComp Bool)) = fun _ => pure false := by
      funext encapsulated
      simp only [other encapsulated.1, decide_false]
    rw [constant, OracleComp.evalDist_bind_const]
    simp
  have pointwise : ∀ guessed : Option (Option PqxdhKemIndCca.MlKem768Ciphertext),
      𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
        (pure (decide (guessed = some (some encapsulated.1))) : ProbComp Bool)] {true} ≤
        PqxdhDeploymentIdealAnomaly.encapsHit setup pair.1 (best pair.1) := by
    intro guessed
    rcases guessed with _ | _ | value
    · rw [never none (fun _ same => by cases same)]
      exact zero_le
    · rw [never (some none) (fun _ same => by cases same)]
      exact zero_le
    · refine le_trans (le_of_eq ?_) (bestMax pair.1 value)
      unfold PqxdhDeploymentIdealAnomaly.encapsHit
      congr 2
      refine bind_congr fun encapsulated => ?_
      simp only [Option.some.injEq, eq_comm]
  refine (lintegral_mono pointwise).trans ?_
  rw [lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

end Guess


/-! ### The bound on the final split game -/

section SplitBound
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhInitializerSecrecy (kemAmbientImpl)

/-- A fixed challenge ciphertext (all zero bytes), at which the guess of the final split game is drawn in the bound. -/
def zeroCt : PqxdhKemIndCca.MlKem768Ciphertext := List.Vector.replicate 1088 0

/-- On the challenger's draws followed by the final split game, the transcript guess is the challenge ciphertext with probability at most `ctGuessPk`: the guess has the same law at every challenge (`game_guess_law`), so the encapsulation can be drawn after it (`LazyOracleDiscard.lawEq_swap`), and a guess of the key pair made before the encapsulation hits it with probability at most `ctGuessPk` (`pairGuess_le`). -/
theorem split_guess_le (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A) :
    𝒟[PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
        (fun outcome => decide (guessView codec t outcome = some (some p.challenge))) <$>
          (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
            (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
              adversary).run' runtime] {true} ≤
      PqxdhDeploymentIdealTrace.ctGuessPk setup := by
  let guessOf : Params KemSK count → ProbComp (Option (Option PqxdhKemIndCca.MlKem768Ciphertext)) := fun p =>
    guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
        adversary).run' runtime
  have law : LazyOracleDiscard.LawEq
      (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
        (fun outcome => decide (guessView codec t outcome = some (some p.challenge))) <$>
          (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
            (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
              adversary).run' runtime)
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
          fun others => guessOf ⟨pair, others, zeroCt⟩) >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some (some encapsulated.1)))) := by
    unfold PqxdhDeploymentIdealParams.drawParams
    simp only [bind_assoc, pure_bind]
    refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun pair => ?_
    refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun others => ?_
    have pointwise : ∀ encapsulated : PqxdhKemIndCca.MlKem768Ciphertext × PqxdhKemIndCca.MlKemSharedSecret,
        LazyOracleDiscard.LawEq
          ((fun outcome => decide (guessView codec t outcome = some (some encapsulated.1))) <$>
            (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
              (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t ⟨pair, others, encapsulated.1⟩) ensureInit
                identityIndex bounds mode adversary).run' runtime)
          (guessOf ⟨pair, others, zeroCt⟩ >>= fun guessed =>
            pure (decide (guessed = some (some encapsulated.1)))) := by
      intro encapsulated
      have same := (game_guess_law setup codec route checks t ⟨pair, others, zeroCt⟩ encapsulated.1 ensureInit
        identityIndex bounds mode adversary runtime).symm.map (fun guessed => decide (guessed = some (some encapsulated.1)))
      simp only [Functor.map_map] at same
      refine same.trans (LazyOracleDiscard.LawEq.of_eq ?_)
      simp only [guessOf, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) pointwise).trans ?_
    exact LazyOracleDiscard.lawEq_swap _ _ _
  rw [law.evalDist_eq]
  exact pairGuess_le setup _

end SplitBound


/-! ### `anomaly_le` on the record world -/

section World
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealTrace (Anomaly)

/-- A Boolean observation that implies another on the support has at most its probability. -/
theorem evalDist_decide_mono {α : Type} (mx : ProbComp α) (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (implies : ∀ a ∈ support mx, P a → Q a) :
    𝒟[(fun a => decide (P a)) <$> mx] {true} ≤ 𝒟[(fun a => decide (Q a)) <$> mx] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact prEvent_mono_of_support _ _ _ fun a member held => by simpa using implies a member (by simpa using held)

open Classical in
/-- The transcript guess event on the record world with the ideal environment of a target: the transcript guess (`PqxdhDeploymentIdealGuess.guessCt`) is the challenge ciphertext of the drawn parameters with probability at most `ctGuessPk`. This public event of the transcript and the drawn parameters has the same probability on the challenger's draws followed by the final split game (`PqxdhDeploymentIdealEnv.c1_split`, whose projection keeps the drawn parameters), where it is at most `ctGuessPk` (`split_guess_le`). It takes no read-back premise; the anomaly bounds below reduce to it. -/
theorem guess_le_pk_sup (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ PqxdhDeploymentIdealTrace.ctGuessPk setup := by
  let hit : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × Ledger ×
      XState KemSK (Params KemSK count × SplitBk) 2) → Prop :=
    fun outcome => ∃ value, outcome = some value ∧
      guessCt codec t value.2.2.1.transcript = some value.2.2.2.backend.1.challenge
  refine (evalDist_decide_mono _ _ (fun result => hit (PqxdhDeploymentEnvironmentJoin.joined result))
    fun result _ ⟨value, found, guessed⟩ => ⟨(value.1, value.2.1.1, value.2.1.2,
      PqxdhDeploymentEnvironmentJoin.merge value.2.2 result.2), by
        simp only [PqxdhDeploymentEnvironmentJoin.joined, found, Option.map_some], guessed⟩).trans ?_
  have law := (PqxdhDeploymentIdealEnv.c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode
    adversary).map (fun outcome => decide (hit outcome))
  have joinedEq : (fun result => decide (hit (PqxdhDeploymentEnvironmentJoin.joined result))) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary =
      (fun outcome => decide (hit outcome)) <$> (PqxdhDeploymentEnvironmentJoin.joined <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
            mode adversary) := by
    rw [Functor.map_map]
  rw [joinedEq, ← law.evalDist_eq, map_bind]
  refine le_of_eq_of_le ?_ (split_guess_le setup codec route checks t ensureInit identityIndex bounds mode adversary
    runtime)
  congr 2
  refine bind_congr fun p => ?_
  rw [Functor.map_map]
  congr 1
  funext outcome
  rcases outcome with _ | value
  · simp [hit, guessView]
  · simp [hit, guessView, PqxdhDeploymentEnvironmentDraw.withX]

open Classical in
/-- `anomaly_le` with the public-key supremum (design-v2 section 7.2, item 6): under `Phase1ReadBack` and `Phase2ReadBack`, the record world with the ideal environment of a target has the Beacon-side anomaly with probability at most `ctGuessPk`. Route: the anomaly implies that the transcript guess is the challenge ciphertext (`PqxdhDeploymentIdealGuess.anomaly_guess`); this public event of the transcript and the drawn parameters has the same probability on the challenger's draws followed by the final split game (`PqxdhDeploymentIdealEnv.c1_split`), where it is at most `ctGuessPk` (`split_guess_le`; the transfer is `guess_le_pk_sup`). `ctGuessPk` is a supremum over all functions of the public key, an information-theoretic quantity; the form with a constructed guesser (`ctGuessBy`), which CE-12a's IND-CCA reduction consumes, is open. -/
theorem anomaly_le_pk_sup (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ PqxdhDeploymentIdealTrace.ctGuessPk setup :=
  (evalDist_decide_mono _ _ (fun result => ∃ value, result.1 = some value ∧
      guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)
    fun result member ⟨value, found, anomaly⟩ => ⟨value, found,
      PqxdhDeploymentIdealGuess.anomaly_guess setup codec route checks phase1 phase2 t ensureInit identityIndex runtime
        serverKid bounds mode adversary result member value found anomaly⟩).trans
    (guess_le_pk_sup setup codec route checks t ensureInit identityIndex runtime bounds mode adversary)

open Classical in
/-- `anomaly_le` (design-v2 section 7.2, item 6): under `Phase1ReadBack` and `Phase2ReadBack`, the record world with the ideal environment of a target has the Beacon-side anomaly with probability at most `ctGuess`, through `anomaly_le_pk_sup` and `PqxdhDeploymentIdealTrace.ctGuessPk_le`. -/
theorem anomaly_le (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ PqxdhDeploymentIdealTrace.ctGuess setup := (anomaly_le_pk_sup setup codec route checks phase1 phase2 t ensureInit identityIndex runtime serverKid bounds
    mode adversary).trans (PqxdhDeploymentIdealTrace.ctGuessPk_le setup)

open Classical in
/-- `anomaly_le_pk_sup` for the anomaly on a prefix: under `Phase1ReadBack` and `Phase2ReadBack`, on the record world with the ideal environment of a target, the event that owner `k` designates the target on some prefix `pre` of the final transcript through a finish made before the selected raw accept (`Anomaly … pre`, that is `BeaconLinked … pre ∧ FinishBefore t pre`: the exceptional alternative of `PqxdhDeploymentIdealBeacon.ideal_slots_prefix`, for consumers that designate at an intermediate time) has probability at most `ctGuessPk`. Designation is not monotone in the transcript, so this event is not contained in the anomaly of the final transcript, which is its case with an empty rest; it implies the same transcript guess event (`PqxdhDeploymentIdealGuess.anomaly_prefix_guess`), bounded by `guess_le_pk_sup`. -/
theorem anomaly_prefix_le_pk_sup (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧ ∃ pre rest, value.2.1.2.transcript = pre ++ rest ∧
        Anomaly setup.source.crypto codec serverKid t pre)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ PqxdhDeploymentIdealTrace.ctGuessPk setup :=
  (evalDist_decide_mono _ _ (fun result => ∃ value, result.1 = some value ∧
      guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)
    fun result member ⟨value, found, pre, rest, split, anomaly⟩ => ⟨value, found,
      PqxdhDeploymentIdealGuess.anomaly_prefix_guess setup codec route checks phase1 phase2 t ensureInit identityIndex
        runtime serverKid bounds mode adversary result member value found pre rest split anomaly⟩).trans
    (guess_le_pk_sup setup codec route checks t ensureInit identityIndex runtime bounds mode adversary)

open Classical in
/-- `anomaly_le` for the anomaly on a prefix: under `Phase1ReadBack` and `Phase2ReadBack`, the event of `anomaly_prefix_le_pk_sup` has probability at most `ctGuess`, through `PqxdhDeploymentIdealTrace.ctGuessPk_le`. -/
theorem anomaly_prefix_le (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧ ∃ pre rest, value.2.1.2.transcript = pre ++ rest ∧
        Anomaly setup.source.crypto codec serverKid t pre)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ PqxdhDeploymentIdealTrace.ctGuess setup :=
  (anomaly_prefix_le_pk_sup setup codec route checks phase1 phase2 t ensureInit identityIndex runtime serverKid bounds
    mode adversary).trans (PqxdhDeploymentIdealTrace.ctGuessPk_le setup)

end World

end BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.coinSend_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.coinSend_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.idealSplit_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.idealSplit_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.handler_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.handler_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.handler_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.handler_backend

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.splitHandler_transcript

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.early_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.early_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.cutAt_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.cutAt_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.stopGuess_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.stopGuess_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.selected_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.selected_stop

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.early_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.early_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_guess_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_guess_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.game_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.game_guess

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.game_guess_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.game_guess_law

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.pairGuess_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.pairGuess_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_guess_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.split_guess_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.evalDist_decide_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.evalDist_decide_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.guess_le_pk_sup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.guess_le_pk_sup

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_le_pk_sup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_le_pk_sup

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_prefix_le_pk_sup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_prefix_le_pk_sup

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_prefix_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyBound.anomaly_prefix_le
