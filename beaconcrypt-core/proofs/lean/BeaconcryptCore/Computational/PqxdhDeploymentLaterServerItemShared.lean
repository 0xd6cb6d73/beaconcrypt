-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFree

/-! LQ-F upstream, unit A1: stage S1b of item 2 over the logged source (LQ-F upstream design-v2, section 4.3, module `…ItemShared`). The main theorem `opaqueBranchL_shared` states the logged opaque branch with the KEM-ideal bit as G1's shared world on the frozen definitions of unit D1 (`PqxdhDeploymentLaterServerItemTargets`):

```text
opaqueBranch … false = PqxdhExtractRomHiddenSuffix.sharedGame (sharedStartL …) (sharedClientL …)
```

`sharedStartL` runs the challenger's key generation, the logged stopped-source prefix up to the selected raw accept and the challenger's encapsulation, and returns the table cache at the cut with a candidate-free context. `sharedClientL` is the logged skeleton's postchallenge phase `postSkelL` with the native services, compiled to G1's interface; it has no candidate argument. So the candidate is G1's secret: it is the 32-byte suffix of every hidden read (the Server's private resumption root and every grouped Beacon finish whose decapsulation handle is the challenge marker) and occurs nowhere else. Everything the logged program reveals, including the Server read and the log, is computed by that candidate-free client from oracle answers. This equality is the Lean form of the T7 condition for LQ-F (LQ-F upstream design-v2, section 5, point 2).

Proof. `opaqueBranchL_grouped`: the router-free logged branch of `PqxdhDeploymentLaterServerItemFree` with every Beacon finish grouped, from `PqxdhRegistrationJointKemPostSkeleton.client_grouped` through `logClient_step` (`client_groupedL`; `groupedClientL_log` identifies unit D1's `groupedClientL` with the logged form of the grouped client), and with the encapsulation-hiding wrapper dropped (`resume_groupedL`). The native layer splits (`groupedImplL_split`): every classical request by `groupedImpl_split`, and the logged accept by `acceptStepL_split`, the proof of `split_accept` on the logged collector, in which the logged scalar is fixed before the encapsulation and passes through. `groupedResumeL_split` and `post_sharedL` move the table below the encapsulator, the router and the CCA evaluation exactly as `groupedResume_split` and `post_shared` do; the decision reads only the source's Boolean result, so the log kept by the resumption is forgotten there. These are program equalities; they charge no advantage and add no assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhSecretInputKdf (HmacOracle RootOutput)
open PqxdhRegistrationJointKemObserverFree (eraseImpl run_eraseOption eraseOptionImpl eraseJoint eraseJoint_idem
  evaluate_map post_neverRead)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
open PqxdhRegistrationJointBeaconOpaqueFinish (layered)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder)
open PqxdhRegistrationJointKemPostSkeleton (GSpec groupedClient groupedImpl groupedPoolLift client_grouped SplitC join
  opRoot coinsEnc tableAt split_run resumeImpl resumeImpl_split groupedImpl_split nativeServices liftT acceptTail
  encLift tableAt_encLift liftT_split split_acceptTail lift_native_run compileHidden shared_compile push_stateless
  push_option actual_coins router_coins evalLayer evalLayer_coins evaluate_layer clean SkelState)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerCommands (Local)
open PqxdhDeploymentLaterServerItemTargets (AcceptL GSpecL acceptStepL skelImplL groupedClientL skelResumeL postSkelL
  cacheOfL sharedStartL sharedClientL)
open PqxdhDeploymentLaterServerItemFree (logClient logClient_step markedClientL markedImplL markedResumeL dropLog
  freeRouterPostL freeRouterBranchL opaqueBranchL_freeRouter)

/-! ### The grouped logged client -/

section Client

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The logged grouped client of unit D1 is the logged form of the grouped source client. -/
theorem groupedClientL_log (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) :
    groupedClientL (Response := Response) setup codec selected challenge identityIndex =
      logClient (groupedClient setup codec selected challenge) (groupedPoolLift (Response := Response))
        identityIndex := by
  funext query
  rcases query with ((coin | request) | read) | later
  · rfl
  · cases request <;> rfl
  · rfl
  · rfl

/-- The native backend of the logged grouped client: the grouped native backend, and the exposed logged accept. -/
noncomputable def groupedImplL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) :
    QueryImpl (GSpecL KemSK Response) (PqxdhRegistrationJointKemEncapsulation.Client KemSK) :=
  groupedImpl setup codec checks identityIndex publicIdentity candidate +
    (fun raw => PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw :
      QueryImpl AcceptL (PqxdhRegistrationJointKemEncapsulation.Client KemSK))

/-- Every step of the marked logged client and of the logged grouped client has the same erased interpretation: source14 requests by `PqxdhRegistrationJointKemPostSkeleton.client_grouped`, and the logged accept and the Server read are the same requests on both sides. -/
theorem client_groupedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (selected : Nat)
    (challenge : MlKem768Ciphertext) (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (held : Local) :
    simulateQ (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate))
        ((markedClientL (Response := Response) setup codec selected challenge identityIndex query).run held) =
      simulateQ (eraseImpl eraseObservers (groupedImplL setup codec checks identityIndex publicIdentity candidate))
        ((groupedClientL (Response := Response) setup codec selected challenge identityIndex query).run held) := by
  rw [groupedClientL_log]
  exact logClient_step (PqxdhRegistrationJointBeaconOpaqueFinish.markedClient setup codec selected challenge)
    (groupedClient setup codec selected challenge)
    (PqxdhRegistrationJointBeaconOpaqueFinish.markedPoolLift (Response := Response))
    (groupedPoolLift (Response := Response))
    (eraseImpl eraseObservers (markedImplL setup codec checks identityIndex publicIdentity candidate))
    (eraseImpl eraseObservers (groupedImplL setup codec checks identityIndex publicIdentity candidate))
    identityIndex
    (fun query owners => client_grouped setup codec checks identityIndex publicIdentity candidate selected challenge
      query owners)
    (by simp only [PqxdhRegistrationJointBeaconOpaqueFinish.markedPoolLift, groupedPoolLift, simulateQ_spec_query]; rfl)
    (fun _ => rfl) query held

end Client

/-! ### The grouped logged branch -/

section Grouped

open PqxdhDeploymentLaterServerOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The grouped logged resumption: the Server's private resumption, then the rest of the tagged logged program under the logged grouped client and the grouped native backend, without the encapsulation-hiding wrapper. The log is kept. -/
noncomputable def groupedResumeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
  (simulateQ (eraseImpl eraseObservers (groupedImplL setup codec checks identityIndex publicIdentity candidate))
    ((simulateQ (groupedClientL setup codec selected ciphertext identityIndex)
      (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
        (owners, log ++ [some ephemeral.secret]))).run answer.2

/-- Under the actual encapsulator, the marked logged resumption equals the grouped logged resumption. -/
theorem resume_groupedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (markedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
          owners log next selected ciphertext candidate) =
      simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        (groupedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native
          owners log next selected ciphertext candidate) := by
  unfold markedResumeL groupedResumeL
  simp only [simulateQ_bind]
  refine bind_congr fun answer => ?_
  rw [hide, PqxdhRegistrationJointKemEncapsulation.forward_actual]
  congr 1
  exact congrArg (fun work => StateT.run work answer.2)
    (layered _ _ _ _ (client_groupedL setup codec checks identityIndex publicIdentity candidate selected ciphertext)
      _ (owners, log ++ [some ephemeral.secret]))

/-- The grouped logged postchallenge step: the router-free logged postchallenge step with the grouped logged resumption. -/
noncomputable def groupedPostL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
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
          (dropLog <$> groupedResumeL setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next selected.val
            transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The router-free logged postchallenge step equals the grouped logged postchallenge step. -/
theorem post_groupedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    freeRouterPostL setup codec checks decision count selected transcript candidate =
      groupedPostL setup codec checks decision count selected transcript candidate := by
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
        · simp only [freeRouterPostL, groupedPostL, active, ↓reduceIte, simulateQ_map, resume_groupedL]
        · simp only [freeRouterPostL, groupedPostL, active, ↓reduceIte]

/-- The grouped logged branch: the router-free logged branch with the grouped logged postchallenge step. -/
noncomputable def groupedBranchL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (groupedPostL setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S1b over the logged source, first part. The logged opaque branch equals the grouped logged branch, as programs and for both values of the branch bit: every Beacon finish reaches the native layer as one request for its private root and the continuation after it, and the encapsulation-hiding wrapper of the resumed logged client is dropped. -/
theorem opaqueBranchL_grouped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      groupedBranchL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index real := by
  rw [opaqueBranchL_freeRouter]
  unfold freeRouterBranchL groupedBranchL
  simp only [post_groupedL]

end Grouped

/-! ### The native layer of the logged skeleton -/

section Split

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The exposed logged raw accept splits into the logged skeleton's accept step with the shared table below it. -/
theorem acceptStepL_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret) (raw : Pqxdh.Bytes) :
    SplitC setup.hmac candidate
      (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw)
      (acceptStepL setup codec checks identityIndex publicIdentity raw) := by
  intro cache state
  have stepS : (PqxdhDeploymentLaterServerCommands.accept setup codec checks identityIndex publicIdentity raw).run
      (join cache state) =
      (PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run state.1.server.consumed >>=
        fun collected => (fun answer => ((answer.1, collected.1.2), answer.2)) <$>
          (PqxdhRegistrationJointKemEncapsulation.lift (PqxdhRegistrationJointOpenBackend.native
            (PqxdhRegistrationJointServerAccept.tail setup publicIdentity (clean state.1)
              (collected.1.1, collected.2)))).run (join cache state) := by
    rw [PqxdhDeploymentLaterServerCommands.accept_ordered]
    simp only [bind_pure_comp]
    rfl
  have stepT : (acceptStepL (V := RootOutput) setup codec checks identityIndex publicIdentity raw).run state =
      simulateQ (encLift (V := RootOutput))
          ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run
            state.1.server.consumed) >>= fun collected =>
        (fun answer => ((answer.1, collected.1.2), answer.2)) <$>
          (liftT (acceptTail setup publicIdentity (clean state.1) (collected.1.1, collected.2))).run state := by
    simp only [acceptStepL, StateT.run_bind, bind_pure_comp, StateT.run_map]
    simp only [StateT.run, bind_map_left, pure_bind]
  rw [stepS, stepT, simulateQ_bind, StateT.run_bind, tableAt_encLift, bind_map_left, map_bind, map_bind]
  refine bind_congr fun collected => ?_
  have tail := congrArg (fun work => (fun answer : Option Nat × NativeState KemSK =>
      ((answer.1, collected.1.2), answer.2)) <$> work)
    (liftT_split (split_acceptTail setup candidate publicIdentity (clean state.1) (collected.1.1, collected.2))
      cache state)
  simp only [Functor.map_map] at tail
  simp only [Functor.map_map, simulateQ_map, StateT.run_map]
  exact tail

/-- Every step of the grouped logged native backend splits into the logged skeleton with the native services. -/
theorem groupedImplL_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (candidate : MlKemSharedSecret)
    (query : (GSpecL KemSK Response).Domain) :
    SplitC setup.hmac candidate (groupedImplL setup codec checks identityIndex publicIdentity candidate query)
      (skelImplL setup codec checks identityIndex publicIdentity (nativeServices setup codec checks) query) := by
  rcases query with query | raw
  · exact groupedImpl_split setup codec checks identityIndex publicIdentity candidate query
  · exact acceptStepL_split setup codec checks identityIndex publicIdentity candidate raw

end Split

/-! ### The resumed logged client and the branch as G1's shared world -/

section Shared

open PqxdhDeploymentLaterServerOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)
open PqxdhExtractRomHiddenSuffix (sharedImpl sharedGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The grouped logged resumption is the logged skeleton's resumption with the native services, with the shared table below it at the candidate and the native state represented by the table cache and the skeleton state. -/
theorem groupedResumeL_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    groupedResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        log next selected ciphertext candidate =
      (fun result : ((R × Local) × SkelState KemSK RootOutput) × HmacOracle.QueryCache =>
          (result.1.1, join result.2 result.1.2)) <$>
        (simulateQ (tableAt coinsEnc (opRoot setup.hmac candidate))
          (skelResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native.2
            owners log next selected ciphertext (nativeServices setup codec checks))).run native.1.cache := by
  unfold groupedResumeL skelResumeL
  have start : eraseObservers native = join native.1.cache ((native.2, none) : SkelState KemSK RootOutput) := rfl
  rw [start, split_run
    (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (resumeImpl setup.hmac native.2.sessions (nativeServices setup codec checks))
    (tableAt coinsEnc (opRoot setup.hmac candidate)) join
    (fun query cache state => resumeImpl_split setup codec checks native.2.sessions candidate query cache state),
    simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
  refine bind_congr fun result => ?_
  exact split_run (eraseImpl eraseObservers (groupedImplL setup codec checks identityIndex publicIdentity candidate))
    (skelImplL setup codec checks identityIndex publicIdentity (nativeServices setup codec checks))
    (tableAt coinsEnc (opRoot setup.hmac candidate)) join
    (fun query cache state => groupedImplL_split setup codec checks identityIndex publicIdentity candidate query cache
      state)
    _ result.2 result.1.2

/-- The grouped logged postchallenge step at a candidate, with the CCA evaluation and the decision, is G1's shared world at that candidate on the logged skeleton's postchallenge phase, started from the table cache at the cut. -/
theorem post_sharedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) (context : OpaqueContext Reader KemSK A X count) (candidate : MlKemSharedSecret) :
    PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
        (groupedPostL setup codec checks decision count selected ⟨chosen.1, challenge, context⟩ candidate) =
      (simulateQ (sharedImpl candidate) (simulateQ (compileHidden setup.hmac)
        (postSkelL setup codec checks decision count selected (nativeServices setup codec checks) chosen challenge
          context))).run' (cacheOfL context) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  all_goals try (simp only [groupedPostL, postSkelL, PqxdhDynamicKemPost.evaluate, simulateQ_pure, map_pure,
    StateT.run'_eq, StateT.run_pure]; rfl)
  · by_cases active : value.keys.pqKey = chosen.1
    · have router := run_eraseOption eraseJoint eraseJoint_idem
        (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder)
        (post_neverRead setup.joint setup.kem selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (dropLog <$> groupedResumeL setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners log next
            selected.val challenge candidate))
        (eraseJoint state)
      rw [eraseJoint_idem] at router
      simp only [groupedPostL, postSkelL, active, ↓reduceIte, cacheOfL]
      rw [bind_pure_comp, evaluate_map, Functor.map_map, evaluate_layer, ← router, groupedResumeL_split,
        Functor.map_map, simulateQ_map (impl := PqxdhRegistrationJointKemEncapsulation.actual setup),
        push_stateless (PqxdhRegistrationJointKemEncapsulation.actual setup) coinsEnc PqxdhLiveKemBirth.coins
          (opRoot setup.hmac candidate) (fun work => actual_coins setup work),
        simulateQ_map (impl := PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder),
        OptionT.run_map, StateT.run_map,
        ← push_option _ PqxdhLiveKemBirth.coins PqxdhPrivateKemSource.ccaCoins (opRoot setup.hmac candidate)
          (fun work current => router_coins setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder work current),
        StateT.run'_eq, shared_compile,
        simulateQ_map (impl := tableAt (fun work => work) (opRoot setup.hmac candidate)), StateT.run_map,
        ← push_stateless (evalLayer setup chosen.2 challenge) PqxdhPrivateKemSource.ccaCoins (fun work => work)
          (opRoot setup.hmac candidate) (fun work => evalLayer_coins setup chosen.2 challenge work)]
      simp only [simulateQ_map, Functor.map_map]
      congr 1
      funext result
      rcases result with ⟨⟨_ | outcome, after⟩, cache⟩ <;> rfl
    · simp only [groupedPostL, postSkelL, active, ↓reduceIte, PqxdhDynamicKemPost.evaluate, simulateQ_pure, map_pure,
        StateT.run'_eq, StateT.run_pure]
      rfl

/-- The grouped logged branch with the KEM-ideal bit is G1's shared world. -/
theorem groupedBranchL_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    groupedBranchL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index false =
      sharedGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index)
        (sharedClientL setup codec checks decision count selected) := by
  unfold groupedBranchL sharedGame sharedStartL
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun chosen => bind_congr fun context => bind_congr fun encapsulated =>
    bind_congr fun uniform => ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact post_sharedL setup codec checks decision count selected chosen encapsulated.1 context uniform

/-- Stage S1b over the logged source. The logged opaque branch with the KEM-ideal bit is G1's shared world: the logged prefix produces the table cache at the cut and a candidate-free context, the candidate is G1's secret drawn after the prefix, and the postchallenge phase is the logged services skeleton with the native services as a client of G1's hidden and direct table reads. The client `sharedClientL` has no candidate argument (the Lean form of the T7 condition). This is a program equality; it charges no advantage and adds no assumption. -/
theorem opaqueBranchL_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false =
      sharedGame (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index)
        (sharedClientL setup codec checks decision count selected) :=
  (opaqueBranchL_grouped setup codec checks ensureInit supplied decision work runtime count selected index false).trans
    (groupedBranchL_shared setup codec checks ensureInit supplied decision work runtime count selected index)

end Shared

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedClientL_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedClientL_log

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.client_groupedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.client_groupedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.resume_groupedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.resume_groupedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.post_groupedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.post_groupedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.opaqueBranchL_grouped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.opaqueBranchL_grouped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.acceptStepL_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.acceptStepL_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedImplL_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedImplL_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedResumeL_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedResumeL_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.post_sharedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.post_sharedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedBranchL_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.groupedBranchL_shared

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.opaqueBranchL_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemShared.opaqueBranchL_shared
