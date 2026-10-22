-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets

/-! LQ-F upstream, unit A1: stages S0a and S0b of item 2 over the logged source (LQ-F upstream design-v2, section 4.3, module `…ItemFree`). The logged opaque branch `PqxdhDeploymentLaterServerOpaque.opaqueBranch` (theorem T6 for the logged source `PqxdhDeploymentLaterServerSource.Spec = RevealSchedule.Spec + LaterRead`) is restated by program equalities that charge no advantage: first without any write-only analysis observer (`opaqueBranchL_free`, the logged form of `PqxdhRegistrationJointKemObserverFree.opaqueBranch_free`), then with the marked Beacon finish (`opaqueBranchL_marked`, the logged form of `PqxdhRegistrationJointBeaconOpaqueFinish.opaqueBranch_marked`) and with the postchallenge router holding the public `placeholder` instead of the KEM candidate (`opaqueBranchL_freeRouter`, the logged form of `PqxdhRegistrationJointBeaconOpaqueFinishRouter.opaqueBranch_freeRouter`).

- Two layers. The logged command handler `PqxdhDeploymentLaterServerCommands.impl` keeps the owner registry and the ephemeral log above the native state. Each of its steps is the native backend `implL` (the exposed native backend of the source and the exposed logged accept `PqxdhDeploymentLaterServerCommands.accept`) run on the step of the logged source client `clientL` (`impl_clientL`), so every logged command run is the backend run on the client run (`run_clientL`, through the generic `run_layers`). `logClient` is the logged form of any source client: every source14 request other than the raw accept runs that client with the log kept, the raw accept sends the logged accept request `AcceptL` of unit D1 and appends the entry, and the Server read sends the identity-pool reveal of the Server's slot. `logClient_step` lifts a per-step equality of two source clients to their logged forms when the two handlers agree on the logged accept and on that reveal. Every stage below applies it to the existing per-request lemma of item 2 (`client_marked`, `client_unmarked`, and in `PqxdhDeploymentLaterServerItemShared` `client_grouped`), so no classical per-request client lemma is repeated; only the logged accept's facts are re-proved (for example `acceptL_neverRead` below and `acceptStepL_split` in `PqxdhDeploymentLaterServerItemShared`).
- Stage S0a. The logged accept never reads the observers (`acceptL_neverRead`: the proof of `accept_neverRead` on the logged collector), hence neither does the backend (`implL_neverRead`). The resumption, the postchallenge step and the branch follow as in the classical proof (`resume_freeL`, `post_freeL`, `opaqueBranchL_free`); the decision reads only the stop status and the source's Boolean result.
- Stage S0b. Neither the logged accept nor the Server read sends the selected decapsulation of the challenge (`accept_freeL`: `accept_free` transported along `accept_fst`, since forgetting the logged scalar is a map; the read is a pool reveal), so the marking is absorbed exactly as in the classical proof (`client_markedL`, `resume_markedL`, `post_markedL`, `client_unmarkedL`, `markedResumeL_unmarked`, `markedPostL_free`).

The resumption definitions keep the log (type `(R × Local) × NativeState`), as the logged skeleton `PqxdhDeploymentLaterServerItemTargets.skelResumeL` of unit D1 does; the postchallenge steps forget it (`dropLog`), because the result type of the KEM game is the classical one. After these stages the candidate is an argument only of the Server's private resumption interpreter and of the private Beacon root interpreter, and the 32-byte suffix of the Extract-table cache keys that both write; `PqxdhDeploymentLaterServerItemShared` moves those reads below the interpreter stack. No assumption, contract or premise is added. LQ-F claims confidentiality only: nothing here cites T5, theorem A2 or T8, and no definition here or in the two later modules of unit A1 references a DH-keyed component (only the types `MlKem768PublicKey`, `PqxdhJointGapDh.ScalarBytes` and the field `Phase1KeyTuple.pqKey`). -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemObserverFree (eraseImpl NeverRead run_erase eraseOptionImpl eraseJoint
  eraseObservers_idem eraseOutcome eraseResult decision_erase router_layer evaluate_map lift_native_erase
  tail_oblivious impl_neverRead resume_neverRead post_neverRead)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerCommands (Local)
open PqxdhDeploymentLaterServerItemTargets (AcceptL)

/-! ### Two stateful layers -/

section Generic

variable {ιE ιM ιI L S α : Type} {E : OracleSpec ιE} {M : OracleSpec ιM} {I : OracleSpec ιI}

/-- A two-layer handler whose every step is the lower handler run on the upper client's step interprets every program as the lower handler run on the upper client's run. -/
theorem run_layers (client : QueryImpl E (StateT L (OracleComp M)))
    (backend : QueryImpl M (StateT S (OracleComp I))) (handler : QueryImpl E (StateT L (StateT S (OracleComp I))))
    (step : ∀ query held, (handler query).run held = simulateQ backend ((client query).run held))
    (work : OracleComp E α) (held : L) :
    (simulateQ handler work).run held = simulateQ backend ((simulateQ client work).run held) := by
  induction work using OracleComp.inductionOn generalizing held with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, step]
      exact bind_congr fun result => ih result.1 result.2

end Generic

/-! ### The logged source client and its native backend -/

section Client

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The source client's interface with the logged accept request. -/
abbrev SpecL (KemSK Response : Type) := PqxdhRegistrationJointServiceSchedule.Spec KemSK Response + AcceptL

/-- The logged form of a source client `client` on an interface `spec'`, with the owner registry and the log as its state: every source14 request other than the raw accept runs `client` with the log kept, the raw accept sends the logged accept request and appends the entry, and the Server read sends the identity-pool reveal of the Server's slot through `pool` and returns it with the log. -/
noncomputable def logClient {ι' : Type} {spec' : OracleSpec ι'}
    (client : QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp spec')))
    (pool : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp spec')) (identityIndex : Nat) :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK) (StateT Local (OracleComp (spec' + AcceptL)))
  | .inl (.inl (.inr (.accept raw))) => fun held =>
      (fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((spec' + AcceptL).query (.inr raw) : OracleComp (spec' + AcceptL) _)
  | .inl query => fun held =>
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((spec' + AcceptL).query (.inl q) : OracleComp (spec' + AcceptL) _))
          ((client query).run held.1)
  | .inr _ => fun held =>
      (fun seed => ((seed, held.2), held)) <$>
        simulateQ (fun q => ((spec' + AcceptL).query (.inl q) : OracleComp (spec' + AcceptL) _))
          (pool (.inl (.inr (.reveal identityIndex))))

/-- Two logged clients have the same interpretation of every step under two handlers that agree on the logged accept, when the underlying source clients have the same interpretation of every step and the two pool reveals of the Server's slot have the same interpretation. -/
theorem logClient_step {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {m : Type → Type} [Monad m]
    [LawfulMonad m]
    (client₁ : QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp spec₁)))
    (client₂ : QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK)
      (StateT (List EncodedEntry) (OracleComp spec₂)))
    (pool₁ : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp spec₁))
    (pool₂ : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OracleComp spec₂))
    (impl₁ : QueryImpl (spec₁ + AcceptL) m) (impl₂ : QueryImpl (spec₂ + AcceptL) m) (identityIndex : Nat)
    (step : ∀ query owners, simulateQ (fun q => impl₁ (.inl q)) ((client₁ query).run owners) =
      simulateQ (fun q => impl₂ (.inl q)) ((client₂ query).run owners))
    (read : simulateQ (fun q => impl₁ (.inl q)) (pool₁ (.inl (.inr (.reveal identityIndex)))) =
      simulateQ (fun q => impl₂ (.inl q)) (pool₂ (.inl (.inr (.reveal identityIndex)))))
    (accept : ∀ raw, impl₁ (.inr raw) = impl₂ (.inr raw))
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    simulateQ impl₁ ((logClient client₁ pool₁ identityIndex query).run held) =
      simulateQ impl₂ ((logClient client₂ pool₂ identityIndex query).run held) := by
  have lifted : ∀ {ι' β : Type} {spec' : OracleSpec ι'} (impl : QueryImpl (spec' + AcceptL) m)
      (work : OracleComp spec' β),
      simulateQ impl (simulateQ (fun q => ((spec' + AcceptL).query (.inl q) : OracleComp (spec' + AcceptL) _)) work) =
        simulateQ (fun q => impl (.inl q)) work := by
    intro _ _ _ impl work
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext request
    simp only [QueryImpl.apply_compose, simulateQ_spec_query]
  have step' : ∀ query owners, simulateQ (fun q => impl₁ (.inl q)) (client₁ query owners) =
      simulateQ (fun q => impl₂ (.inl q)) (client₂ query owners) := step
  rcases query with ((coin | request) | read') | later
  · simp only [logClient, StateT.run, simulateQ_map, lifted, step']
  · cases request
    case accept raw =>
      simp only [logClient, StateT.run, simulateQ_map, simulateQ_spec_query]
      exact congrArg _ (accept raw)
    all_goals simp only [logClient, StateT.run, simulateQ_map, lifted, step']
  · simp only [logClient, StateT.run, simulateQ_map, lifted, step']
  · simp only [logClient, StateT.run, simulateQ_map]
    exact congrArg _ ((lifted impl₁ _).trans (read.trans (lifted impl₂ _).symm))

/-- Lift a source-client request to the logged interface. -/
def liftL : QueryImpl (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) (OracleComp (SpecL KemSK Response)) :=
  fun query => (SpecL KemSK Response).query (.inl query)

/-- The logged source client: the logged form of the source client of `PqxdhRegistrationJointRevealSchedule`. -/
noncomputable def clientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (identityIndex : Nat) :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK) (StateT Local (OracleComp (SpecL KemSK Response))) :=
  logClient (PqxdhRegistrationJointRevealSchedule.client setup codec)
    (PqxdhRegistrationJointServiceSchedule.poolLift (Response := Response)) identityIndex

/-- The native backend of the logged source client: the exposed native backend of the source, and the exposed logged accept on the logged accept request. -/
noncomputable def implL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    QueryImpl (SpecL KemSK Response) (PqxdhRegistrationJointKemEncapsulation.Client KemSK)
  | .inl query => PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity query
  | .inr raw => PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw

/-- Each step of the logged command handler is the native backend run on the logged source client's step. -/
theorem impl_clientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (held : Local) :
    (PqxdhDeploymentLaterServerCommands.impl setup codec checks identityIndex publicIdentity query).run held =
      simulateQ (implL setup codec checks identityIndex publicIdentity)
        ((clientL (Response := Response) setup codec identityIndex query).run held) := by
  have lifted : ∀ {β : Type} (work : OracleComp (PqxdhRegistrationJointServiceSchedule.Spec KemSK Response) β),
      simulateQ (implL setup codec checks identityIndex publicIdentity)
          (simulateQ (fun q => ((SpecL KemSK Response).query (.inl q) : OracleComp (SpecL KemSK Response) _)) work) =
        simulateQ (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity)
          work := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext request
    simp only [QueryImpl.apply_compose, simulateQ_spec_query, implL, QueryImpl.add_apply_inl]
  rcases query with ((coin | request) | read) | later
  · simp only [PqxdhDeploymentLaterServerCommands.impl, clientL, logClient, StateT.run, simulateQ_map, lifted]
  · cases request
    case accept raw =>
      simp only [PqxdhDeploymentLaterServerCommands.impl, clientL, logClient, StateT.run, simulateQ_map,
        simulateQ_spec_query]
      rfl
    all_goals simp only [PqxdhDeploymentLaterServerCommands.impl, clientL, logClient, StateT.run, simulateQ_map, lifted]
  · simp only [PqxdhDeploymentLaterServerCommands.impl, clientL, logClient, StateT.run, simulateQ_map, lifted]
  · apply StateT.ext
    intro state
    simp only [PqxdhDeploymentLaterServerCommands.impl, clientL, logClient, StateT.run, simulateQ_map]
    rfl

/-- The logged command run is the native backend run on the logged source client's run. -/
theorem run_clientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) {Result : Type}
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Result) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work owners log state =
      (simulateQ (implL setup codec checks identityIndex publicIdentity)
        ((simulateQ (clientL (Response := Response) setup codec identityIndex) work).run (owners, log))).run state :=
  congrArg (fun program => StateT.run program state)
    (run_layers _ _ _ (impl_clientL setup codec checks identityIndex publicIdentity) work (owners, log))

end Client

/-! ### Stage S0a over the logged source: the observer-free branch -/

section Free

open PqxdhDeploymentLaterServerOpaque (OpaqueContext toContext sourcePreOpaque opaquePost opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The exposed logged raw accept never reads the analysis observers. -/
theorem acceptL_neverRead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    Prod.map id eraseObservers <$>
        (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run state =
      Prod.map id eraseObservers <$>
        (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run
          (eraseObservers state) := by
  have consumed : (eraseObservers state).2.server.consumed = state.2.server.consumed := rfl
  rw [PqxdhDeploymentLaterServerCommands.accept_ordered, PqxdhDeploymentLaterServerCommands.accept_ordered, consumed]
  simp only [map_bind, map_pure]
  refine bind_congr fun collected => ?_
  have erased := congrArg (fun work => (fun answer : Option Nat × NativeState KemSK =>
      ((answer.1, collected.1.2), answer.2)) <$> work)
    ((lift_native_erase _ state).trans ((congrArg _ (congrArg _ (tail_oblivious setup publicIdentity state.2
      (collected.1.1, collected.2) state))).trans (lift_native_erase _ (eraseObservers state)).symm))
  simp only [Functor.map_map] at erased
  simp only [bind_pure_comp]
  exact erased

/-- The native backend of the logged source client never reads the analysis observers. -/
theorem implL_neverRead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) :
    NeverRead eraseObservers (implL (Response := Response) setup codec checks identityIndex publicIdentity) := by
  rintro (query | raw) state
  · exact impl_neverRead setup codec checks identityIndex publicIdentity query state
  · exact acceptL_neverRead setup codec checks identityIndex publicIdentity raw state

/-- Forget the log of a logged outcome. -/
def dropLog (result : (R × Local) × NativeState KemSK) : Outcome KemSK R :=
  ((result.1.1, result.1.2.1), result.2)

/-- The observer-free logged resumption: the opaque resumption and the rest of the tagged logged program under the logged source client, with both native interpreters erased. The log is kept. -/
noncomputable def freeResumeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) ((R × Local) × NativeState KemSK) := do
  let answer ← (simulateQ
      (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run (eraseObservers native)
  hide setup ((simulateQ (eraseImpl eraseObservers (implL setup codec checks identityIndex publicIdentity))
    ((simulateQ (clientL (Response := Response) setup codec identityIndex)
      (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
        (owners, log ++ [some ephemeral.secret]))).run answer.2)

/-- The logged opaque resumption with its native observers erased is the observer-free logged resumption with the log forgotten. -/
theorem resume_freeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    eraseOutcome <$> PqxdhDeploymentLaterServerCut.opaqueResume setup codec checks identityIndex publicIdentity observe
        raw value ephemeral consumed native owners log next ciphertext candidate =
      dropLog <$> freeResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed
        native owners log next ciphertext candidate := by
  have commandsFree : ∀ answer : Option Nat × NativeState KemSK,
      eraseOutcome <$> hide setup (PqxdhDeploymentLaterServerCommands.commands setup codec checks identityIndex
        publicIdentity (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1) owners
          (log ++ [some ephemeral.secret]) answer.2) =
      dropLog <$> hide setup ((simulateQ
          (eraseImpl eraseObservers (implL setup codec checks identityIndex publicIdentity))
        ((simulateQ (clientL (Response := Response) setup codec identityIndex)
          (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
            (owners, log ++ [some ephemeral.secret]))).run (eraseObservers answer.2)) := by
    intro answer
    rw [← run_erase eraseObservers eraseObservers_idem _
      (implL_neverRead setup codec checks identityIndex publicIdentity)]
    simp only [hide, ← simulateQ_map, PqxdhDeploymentLaterServerCommands.commands, run_clientL, Functor.map_map]
    rfl
  simp only [PqxdhDeploymentLaterServerCut.opaqueResume, freeResumeL, map_bind, commandsFree]
  rw [← run_erase eraseObservers eraseObservers_idem _ (resume_neverRead setup native.2.sessions candidate),
    bind_map_left]
  rfl

/-- The observer-free logged postchallenge step: `LaterServerOpaque.opaquePost` with the erased joint router and the observer-free logged resumption (log forgotten), started from the erased router state. -/
noncomputable def freePostL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext candidate))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (dropLog <$> freeResumeL setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next
            transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The logged opaque postchallenge step with every observer erased is the observer-free logged postchallenge step. -/
theorem post_freeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    eraseResult <$> opaquePost setup codec checks decision count selected transcript candidate =
      freePostL setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => simp [opaquePost, freePostL, eraseResult]
  | ready created others cut state runtime =>
    cases cut with
    | none => simp [opaquePost, freePostL, eraseResult]
    | some cut =>
      cases cut with
      | complete outcome => simp [opaquePost, freePostL, eraseResult]
      | pending raw value ephemeral consumed native owners log next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [opaquePost, freePostL, active, ↓reduceIte, map_bind, map_pure]
          rw [← resume_freeL, simulateQ_map,
            ← router_layer _ (post_neverRead setup.joint setup.kem selected.val _ ciphertext candidate),
            bind_map_left]
          rfl
        · simp [opaquePost, freePostL, active, eraseResult]

/-- The observer-free logged opaque branch: `LaterServerOpaque.opaqueBranch` with the observer-free logged postchallenge step. The key generation, prefix, challenger encapsulation, uniform draw, CCA evaluation and decision are unchanged. -/
noncomputable def freeBranchL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (freePostL setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S0a over the logged source. The logged opaque branch (theorem T6 for the logged source) equals the observer-free logged branch, as programs and for both values of the branch bit: the family history, the native ghost, the KEM pool/router transcript and the identity-pool transcript of the postchallenge phase are written but never read (the logged accept and the Server read included), and the decision reads only the stop status and the source's Boolean result. This charges no advantage. -/
theorem opaqueBranchL_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeBranchL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real := by
  unfold opaqueBranch freeBranchL
  refine bind_congr fun chosen => bind_congr fun context => bind_congr fun encapsulated =>
    bind_congr fun uniform => ?_
  rw [← post_freeL, evaluate_map, Functor.map_map]
  congr 1
  funext result
  exact (decision_erase result).symm

end Free

/-! ### Stage S0b over the logged source: the marked Beacon finish -/

section Marked

open PqxdhRegistrationJointBeaconOpaqueFinish (MarkedSpec markedClient markedImpl markedPoolLift markEnc markHandler
  markPool_actual markEnc_hide mark_run layered router_absorbs client_marked)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The marked interface with the logged accept request. -/
abbrev MarkedSpecL (KemSK Response : Type) := MarkedSpec KemSK Response + AcceptL

/-- The marked logged client: the logged form of the marked source client. -/
noncomputable def markedClientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK) (StateT Local (OracleComp (MarkedSpecL KemSK Response))) :=
  logClient (markedClient setup codec selected challenge) (markedPoolLift (Response := Response)) identityIndex

/-- The native backend of the marked logged client: the marked backend, and the exposed logged accept. -/
noncomputable def markedImplL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) :
    QueryImpl (MarkedSpecL KemSK Response) (PqxdhRegistrationJointKemEncapsulation.Client KemSK)
  | .inl query => markedImpl setup codec checks identityIndex publicIdentity candidate query
  | .inr raw => PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw

/-- Every step of the logged source client and of the marked logged client has the same marked interpretation: source14 requests by `PqxdhRegistrationJointBeaconOpaqueFinish.client_marked`, and the logged accept and the Server read are the same requests on both sides. -/
theorem client_markedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    simulateQ (markHandler selected challenge candidate
        (eraseImpl eraseObservers (implL setup codec checks identityIndex publicIdentity)))
        ((clientL (Response := Response) setup codec identityIndex query).run held) =
      simulateQ (markHandler selected challenge candidate
        (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate)))
        ((markedClientL setup codec selected challenge identityIndex query).run held) :=
  logClient_step (PqxdhRegistrationJointRevealSchedule.client setup codec) (markedClient setup codec selected challenge)
    (PqxdhRegistrationJointServiceSchedule.poolLift (Response := Response)) (markedPoolLift (Response := Response))
    (markHandler selected challenge candidate
      (eraseImpl eraseObservers (implL setup codec checks identityIndex publicIdentity)))
    (markHandler selected challenge candidate
      (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate)))
    identityIndex
    (fun query owners => client_marked setup codec checks identityIndex publicIdentity selected challenge candidate
      query owners)
    (by simp only [PqxdhRegistrationJointServiceSchedule.poolLift, markedPoolLift, simulateQ_spec_query]; rfl)
    (fun _ => rfl) query held

/-- The marked logged resumption: the observer-free logged resumption with the marked logged client and the marked native backend, whose private root interpreter alone holds `candidate`. The log is kept. -/
noncomputable def markedResumeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) ((R × Local) × NativeState KemSK) := do
  let answer ← (simulateQ
      (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run (eraseObservers native)
  hide setup ((simulateQ (eraseImpl eraseObservers
      (markedImplL setup codec checks identityIndex publicIdentity candidate))
    ((simulateQ (markedClientL setup codec selected ciphertext identityIndex)
      (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
        (owners, log ++ [some ephemeral.secret]))).run answer.2)

/-- After marking, the observer-free logged resumption and the marked logged resumption are the same program. -/
theorem resume_markedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    simulateQ (markEnc selected ciphertext candidate)
        (freeResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
          log next ciphertext candidate) =
      simulateQ (markEnc selected ciphertext candidate)
        (markedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
          owners log next selected ciphertext candidate) := by
  unfold freeResumeL markedResumeL
  simp only [simulateQ_bind, markEnc_hide]
  refine bind_congr fun answer => ?_
  congr 1
  rw [mark_run, mark_run]
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_markedL setup codec checks identityIndex publicIdentity selected ciphertext candidate) _
      (owners, log ++ [some ephemeral.secret]))

/-- The marked logged postchallenge step: the observer-free logged postchallenge step with the marked logged resumption. -/
noncomputable def markedPostL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext candidate))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (dropLog <$> markedResumeL setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next selected.val
            transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The observer-free logged postchallenge step equals the marked logged postchallenge step. -/
theorem post_markedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    freePostL setup codec checks decision count selected transcript candidate =
      markedPostL setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners log next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [freePostL, markedPostL, active, ↓reduceIte]
          have absorb : ∀ (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)
              (Outcome KemSK Bool)),
              simulateQ (eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate))
                (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work) =
              simulateQ (eraseOptionImpl eraseJoint (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
                (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate))
                (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
                  (simulateQ (markEnc selected.val ciphertext candidate) work)) := by
            intro work
            conv_lhs => rw [← router_absorbs setup.kem setup.joint selected.val
              (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext candidate]
            rw [QueryImpl.simulateQ_compose, markPool_actual]
          rw [absorb]
          conv_rhs => rw [absorb]
          simp only [simulateQ_map, resume_markedL]
        · simp only [freePostL, markedPostL, active, ↓reduceIte]

/-- The marked logged opaque branch: the observer-free logged branch with the marked logged postchallenge step. -/
noncomputable def markedBranchL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (markedPostL setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S0b over the logged source, first part: the logged opaque branch equals the marked logged branch, as programs and for both values of the branch bit. -/
theorem opaqueBranchL_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      markedBranchL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index real := by
  rw [opaqueBranchL_free]
  unfold freeBranchL markedBranchL
  simp only [post_markedL]

end Marked

/-! ### Stage S0b over the logged source: the router holds a public placeholder -/

section Router

open PqxdhRegistrationJointBeaconOpaqueFinish (markedClient markedImpl markedPoolLift markEnc markHandler
  markPool_actual markEnc_hide mark_run layered router_moves)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (IsTarget IsTargetEnc onLeft mark_free markedBy_other
  client_unmarked placeholder)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The exposed logged raw accept requests no selected decapsulation of the challenge: `PqxdhRegistrationJointBeaconOpaqueFinishRouter.accept_free` transported along `PqxdhDeploymentLaterServerCommands.accept_fst`, since forgetting the logged scalar is a map. -/
theorem accept_freeL (selected : Nat) (challenge : MlKem768Ciphertext) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run
      state).IsQueryBoundP (IsTargetEnc selected challenge) 0 := by
  have free := PqxdhRegistrationJointBeaconOpaqueFinishRouter.accept_free selected challenge setup codec checks
    identityIndex publicIdentity raw state
  rw [← PqxdhDeploymentLaterServerCommands.accept_fst, isQueryBoundP_map_iff] at free
  exact free

/-- Every step of the marked logged client has the same interpretation whether or not the backend marks the selected decapsulation of the challenge: source14 requests by `PqxdhRegistrationJointBeaconOpaqueFinishRouter.client_unmarked`, the logged accept by `accept_freeL`, and the Server read is not that decapsulation. -/
theorem client_unmarkedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (selected : Nat) (challenge : MlKem768Ciphertext)
    (candidate marker : MlKemSharedSecret) (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain)
    (held : Local) :
    simulateQ (markHandler selected challenge marker
        (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate)))
        ((markedClientL (Response := Response) setup codec selected challenge identityIndex query).run held) =
      simulateQ (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate))
        ((markedClientL (Response := Response) setup codec selected challenge identityIndex query).run held) :=
  logClient_step (markedClient setup codec selected challenge) (markedClient setup codec selected challenge)
    (markedPoolLift (Response := Response)) (markedPoolLift (Response := Response))
    (markHandler selected challenge marker
      (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate)))
    (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate))
    identityIndex
    (fun query owners => client_unmarked setup codec checks identityIndex publicIdentity selected challenge candidate
      marker query owners)
    (by
      simp only [markedPoolLift, simulateQ_spec_query]
      exact markedBy_other setup codec checks identityIndex publicIdentity selected challenge candidate marker
        (.inl (.inl (.inl (.inl (.inr (.reveal identityIndex)))))) (by simp [onLeft, IsTarget]))
    (fun raw => by
      apply StateT.ext
      intro state
      change simulateQ (markEnc selected challenge marker) (Prod.map id eraseObservers <$>
        (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run
          (eraseObservers state)) = _
      refine mark_free selected challenge marker _ ?_
      rw [isQueryBoundP_map_iff]
      exact accept_freeL selected challenge setup codec checks identityIndex publicIdentity raw _)
    query held

/-- The marked logged resumption is unchanged by marking the selected decapsulation of the challenge with any value. -/
theorem markedResumeL_unmarked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate marker : MlKemSharedSecret) :
    simulateQ (markEnc selected ciphertext marker)
        (markedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
          owners log next selected ciphertext candidate) =
      markedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        log next selected ciphertext candidate := by
  unfold markedResumeL
  rw [simulateQ_bind, mark_free selected ciphertext marker _
    (PqxdhRegistrationJointBeaconOpaqueFinishRouter.resume_free selected ciphertext setup codec checks identityIndex
      publicIdentity raw value ephemeral consumed native ciphertext candidate)]
  refine bind_congr fun answer => ?_
  rw [markEnc_hide]
  congr 1
  rw [mark_run]
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_unmarkedL setup codec checks identityIndex publicIdentity selected ciphertext candidate
      marker) _ (owners, log ++ [some ephemeral.secret]))

/-- The router-free logged postchallenge step: the marked logged postchallenge step with the router holding `placeholder`. The candidate is an argument only of the Server's private resumption interpreter and of the private Beacon root interpreter. -/
noncomputable def freeRouterPostL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext placeholder))
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (dropLog <$> markedResumeL setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next selected.val
            transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The marked logged postchallenge step equals the router-free logged postchallenge step. -/
theorem markedPostL_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    markedPostL setup codec checks decision count selected transcript candidate =
      freeRouterPostL setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => rfl
  | ready created others cut state runtime =>
    cases cut with
    | none => rfl
    | some cut =>
      cases cut with
      | complete outcome => rfl
      | pending raw value ephemeral consumed native owners log next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [markedPostL, freeRouterPostL, active, ↓reduceIte]
          conv_lhs => rw [← router_moves setup.kem setup.joint selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected publicKey others) ciphertext placeholder candidate]
          rw [QueryImpl.simulateQ_compose, markPool_actual, simulateQ_map, markedResumeL_unmarked]
        · simp only [markedPostL, freeRouterPostL, active, ↓reduceIte]

/-- The router-free logged opaque branch: the marked logged branch with the router-free logged postchallenge step. -/
noncomputable def freeRouterBranchL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (freeRouterPostL setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S0b over the logged source, completed. The logged opaque branch (theorem T6 for the logged source) equals the router-free logged branch, as programs and for both values of the branch bit: every Beacon finish carries an opaque decapsulation handle and sends its root request privately, the postchallenge router holds the fixed public `placeholder` instead of the candidate, and the candidate is an argument only of the Server's private resumption interpreter and of the private Beacon root interpreter. Neither the logged accept nor the Server read sends the selected decapsulation of the challenge. -/
theorem opaqueBranchL_freeRouter (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeRouterBranchL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
        selected index real := by
  rw [opaqueBranchL_marked]
  unfold markedBranchL freeRouterBranchL
  simp only [markedPostL_free]

end Router

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.run_layers' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.run_layers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.logClient_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.logClient_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.impl_clientL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.impl_clientL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.run_clientL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.run_clientL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.acceptL_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.acceptL_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.implL_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.implL_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.resume_freeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.resume_freeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.post_freeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.post_freeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.client_markedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.client_markedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.resume_markedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.resume_markedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.post_markedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.post_markedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.accept_freeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.accept_freeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.client_unmarkedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.client_unmarkedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.markedResumeL_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.markedResumeL_unmarked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.markedPostL_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.markedPostL_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_freeRouter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree.opaqueBranchL_freeRouter
