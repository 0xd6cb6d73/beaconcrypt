-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerTransfer

/-! LQ-F upstream, unit D1: the frozen targets of item 2 over the logged source (U-L1). Item 2's classical stages S1b-S8 are stated for programs of source14 (`PqxdhRegistrationJointRevealSchedule.Spec`); the compiled LQ-F program `PqxdhDeploymentLaterServerCompile.compileServer` is a program of the logged source `PqxdhDeploymentLaterServerSource.Spec = RevealSchedule.Spec + LaterRead`, whose raw accepts append the generated ephemeral scalar to a log and whose Server read returns the Server's identity seed with the log. No source14 request returns either value, so item 2 is lifted rather than reduced (LQ-F upstream design-v2, decisions D1 and D9; not CE-11b's design-v2). This module fixes, before any of the lift's theorems exist, the definitions those theorems will be stated with, so that the later units build against frozen names. Its theorems are projections, unfoldings, the evaluation of the guessing term and the implication between its two targets; it proves no security bound.

- The logged grouped interface adds one request to item 2's grouped interface: `GSpecL = GSpec + AcceptL`, the logged accept, which takes the raw bytes and returns the session and the logged scalar. `acceptStepL` is the skeleton's accept `PqxdhRegistrationJointKemPostSkeleton.acceptStep` with the LQ-F logged collector (`PqxdhDeploymentLaterServerCommands.ordered`); forgetting the scalar gives the classical step back (`acceptStepL_fst`). `skelImplL` is the classical skeleton `skelImpl` on `.inl` and `acceptStepL` on the new request. `groupedClientL` keeps the owner registry and the log as its state, exactly as `PqxdhDeploymentLaterServerCommands.impl` does: every source14 request other than the raw accept runs the classical grouped client with the log kept (`groupedClientL_inl`), the raw accept sends the logged accept and appends the entry (`groupedClientL_accept`), and the Server read sends the ordinary identity-pool reveal of the Server's slot, the request `LaterServerCommands.impl` issues, and returns it with the log (`groupedClientL_read`).
- The post-challenge phase: `skelResumeL` is the classical `skelResume` with the logged rest of the opaque cut (`PqxdhDeploymentLaterServerCut.opaqueResume`: the tagged logged program from the log at the cut extended by the selected accept's explicit ephemeral). `postSkelL` is the classical `postSkel` on a logged opaque context (`PqxdhDeploymentLaterServerOpaque.OpaqueContext`); it has no candidate argument. `sharedStartL` is the classical `sharedStart` with the logged opaque prephase `LaterServerOpaque.sourcePreOpaque` and the cache of the logged cut (`cacheOfL`). `sharedClientL`, `rootClientL` and `entryClientL` are the classical `sharedClient`, `rootClient` and `entryClient` with `sharedStartL` and `postSkelL`, and `entryDL` is the classical `entryD` on `entryClientL`.
- The hybrid of stage S7, generic in the client: `hybridOf` and `entryDkOf` are the classical `PqxdhRegistrationJointKemSecondEntry.hybrid` and `entryDk` with the factored root client abstracted (`hybrid_hybridOf`, `entryDk_entryDkOf`, both `rfl`); `entryDkL` is `entryDkOf` at `entryClientL`.
- The targets: `laterSlotGame` is the classical `slotGame` (item 2's two-slot world through the first-touch allocator on the persistent lazy table) with `entryClientL`; `slotLossL` is the classical `PqxdhRegistrationJointKemKeyTransfer.allIdealLoss` (the right side of `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`) with `rootClientL` and `entryDkL`; `rootBillL` is the classical coin bill `PqxdhRegistrationJointKemRootCosts.rootBill` (LQ-F design-v2 D8: the logged prechallenge bills have the classical closed form, the Server read weighs 0, and the post-run coins, HMAC and BLAKE2b enter through the budget). At the transported caps of the compiled LQ-F program the first term of `slotLossL` is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (`later_guess_term`, `slotLossL_transported`): the post-run HMAC queries are charged in the same guessing term, with coefficient one.
- The target statements, as `Prop`-valued definitions for the later units to prove: `OpaqueBranchSlotsTwoTargetL` (the logged counterpart of `opaqueBranch_slots_two`, for every logged-source program within a logged source budget, under `SourceFullCorrect`) and `LaterSlotsTwoTarget` (its instance at the compiled LQ-F program of a budget-respecting `A₁` and a post-budget-respecting `A₂`, at the transported caps). The generic target implies the instance (`laterSlotsTwo_of_generic`, through `compile_server_certified`).

Decorrelation caveat (route R1, sharpened for LQ-F): the post-run adversary knows every revealed Beacon secret, the Server seed and every generated ephemeral, hence both hidden entries' 128-byte DH coordinates exactly; each hidden entry is the R1 table at `padFF32 ‖ m ‖ u` with only the shared 32-byte ML-KEM output `u` unknown. The unpredictability of the two entries given `m` and their mutual independence rest on R1 alone. Classically `m` also contains honest-honest DH values the adversary cannot compute; item 2 never uses them, but in LQ-F no such second line of defence exists. The premises of the targets (R1, the HMAC-SHA-512 PRF game, the Extract game on `uniform32`, `SourceFullCorrect`, the logged source budget) are those of the classical T7. LQ-F claims confidentiality only: no target here cites T5, theorem A2 or T8, and no definition here references a DH-keyed component (only the types `MlKem768PublicKey`, `PqxdhJointGapDh.ScalarBytes` and the field `Phase1KeyTuple.pqKey`). -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (HmacOracle RootOutput hmacPrfRealGame hmacPrfRandomGame)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhFullSecretInputKdf (SourceFullCorrect)
open PqxdhCorrelatedExpandHybrid (indexedReduction)
open PqxdhRegistrationJointKemObserverFree (eraseJoint)
open PqxdhRegistrationJointKemPostSkeleton (GSpec SClient SkelSpec SkelState Services TSpec Enc encLift liftT
  acceptTail clean groupedClient skelImpl acceptStep groupedPoolLift resumeImpl evalLayer skelDecide nativeServices
  compileHidden fwd fwdOption)
open PqxdhRegistrationJointKemEntryFactor (Output EntrySpec internalizeV factoredServices firstTable)
open PqxdhRegistrationJointKemSecondEntry (indexedImpl sampler pin slotImpl tableService emptyAlloc keyScheduleBound)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder)
open PqxdhRegistrationJointRevealCosts (SourceKind)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext sourcePreOpaque)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec Handle)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhDeploymentLaterServerCompileBudget (laterTransported)

/-! ### The logged grouped interface and the logged skeleton -/

section Skeleton
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The logged accept request of the grouped interface: raw bytes in, the session and the logged scalar out. -/
abbrev AcceptL : OracleSpec Pqxdh.Bytes := fun _ => Option Nat × Option PqxdhJointGapDh.ScalarBytes

/-- The logged grouped interface: item 2's grouped interface and the logged accept. -/
abbrev GSpecL (KemSK Response : Type) := GSpec KemSK Response + AcceptL

/-- The logged accept on the skeleton's native layer: `acceptStep` with the LQ-F logged collector. It returns the session of the accept and the logged scalar. -/
noncomputable def acceptStepL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    SClient KemSK V (Option Nat × Option PqxdhJointGapDh.ScalarBytes) := do
  let before ← (fun state => pure (clean state.1, state) : SClient KemSK V (GameState KemSK))
  let collected ← (fun state => (fun result => (result, state)) <$> simulateQ (encLift (V := V))
      ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run
        state.1.server.consumed) : SClient KemSK V _)
  let reply ← liftT (acceptTail setup publicIdentity before (collected.1.1, collected.2))
  pure (reply, collected.1.2)

/-- The logged skeleton: the classical skeleton on the classical requests, the logged accept on the new one. -/
noncomputable def skelImplL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) :
    QueryImpl (GSpecL KemSK Response) (SClient KemSK V)
  | .inl query => skelImpl setup codec checks identityIndex publicIdentity services query
  | .inr raw => acceptStepL setup codec checks identityIndex publicIdentity raw

/-- The logged grouped client, with the owner registry and the log as its state: source14 requests as the classical grouped client (log kept), the raw accept as the logged accept request (entry appended), and the Server read as the identity-pool reveal request of the Server's slot together with the log. -/
noncomputable def groupedClientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (StateT (List EncodedEntry × Log) (OracleComp (GSpecL KemSK Response)))
  | .inl (.inl (.inr (.accept raw))) => fun held =>
      (fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _)
  | .inl query => fun held =>
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          ((groupedClient setup codec selected challenge query).run held.1)
  | .inr _ => fun held =>
      (fun seed => ((seed, held.2), held)) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          (groupedPoolLift (Response := Response) (.inl (.inr (.reveal identityIndex))))

/-- Forgetting the logged scalar gives the classical skeleton accept: the logged collector forgets to the classical source prefix (`PqxdhDeploymentLaterServerCommands.ordered_fst` with `PqxdhRegistrationJointKemSourceSuffix.ordered_source`). -/
theorem acceptStepL_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : SkelState KemSK V) :
    (fun result => (result.1.1, result.2)) <$>
        (acceptStepL (V := V) setup codec checks identityIndex publicIdentity raw).run state =
      (acceptStep (V := V) setup codec checks identityIndex publicIdentity raw).run state := by
  have inner : simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix (Reader := Reader) identityIndex raw) =
        PqxdhRegistrationJointKemSourceSuffix.ordered setup codec checks identityIndex raw := by
    simp only [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
    rw [← PqxdhRegistrationJointKemSourceSuffix.handler, PqxdhRegistrationJointKemSourceSuffix.ordered_source]
  have outer := PqxdhDeploymentLaterServerCommands.ordered_fst setup codec checks identityIndex raw
    state.1.server.consumed
  simp only [acceptStepL, acceptStep, StateT.run_bind, inner]
  simp only [StateT.run] at outer ⊢
  simp only [pure_bind]
  rw [← outer, simulateQ_map]
  simp only [map_bind, bind_map_left, Functor.map_map]
  refine bind_congr fun a => ?_
  refine (bind_congr fun b => ?_).trans (bind_pure _)
  rfl

/-- The logged skeleton on a classical request is the classical skeleton. -/
theorem skelImplL_inl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (query : (GSpec KemSK Response).Domain) :
    skelImplL setup codec checks identityIndex publicIdentity services (.inl query) =
      skelImpl setup codec checks identityIndex publicIdentity services query := rfl

/-- The logged skeleton on the logged accept is the logged accept step. -/
theorem skelImplL_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (raw : Pqxdh.Bytes) :
    skelImplL setup codec checks identityIndex publicIdentity services (.inr raw) =
      acceptStepL setup codec checks identityIndex publicIdentity raw := rfl

/-- The logged grouped client on a source14 request other than the raw accept is the classical grouped client, with the log kept. -/
theorem groupedClientL_inl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (held : List EncodedEntry × Log) :
    groupedClientL (Response := Response) setup codec selected challenge identityIndex (.inl query) held =
      (fun result => (result.1, (result.2, held.2))) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          ((groupedClient setup codec selected challenge query).run held.1) := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case accept raw => exact absurd rfl (other raw)
    all_goals rfl
  · rfl

/-- The logged grouped client on the raw accept sends the logged accept and appends the logged entry. -/
theorem groupedClientL_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) (raw : Pqxdh.Bytes) (held : List EncodedEntry × Log) :
    groupedClientL (Response := Response) setup codec selected challenge identityIndex (.inl (.inl (.inr (.accept raw))))
        held =
      (fun answer => (answer.1, (held.1, held.2 ++ [answer.2]))) <$>
        ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _) := rfl

/-- The logged grouped client on the Server read sends the identity-pool reveal of the Server's slot, returns its answer with the log and keeps its state. -/
theorem groupedClientL_read (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (identityIndex : Nat) (held : List EncodedEntry × Log) :
    groupedClientL (Response := Response) setup codec selected challenge identityIndex (.inr ()) held =
      (fun seed => ((seed, held.2), held)) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          (groupedPoolLift (Response := Response) (.inl (.inr (.reveal identityIndex)))) := rfl

end Skeleton

/-! ### The post-challenge phase over the logged opaque cut -/

section Post
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The resumed client of the logged skeleton: the Server's private resumption (unchanged), then the rest of the tagged logged program under the logged grouped client from the owners and the log at the cut extended by the selected accept's explicit ephemeral, on the native layer of the logged skeleton. -/
noncomputable def skelResumeL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (services : Services V Response) :
    OracleComp (Enc KemSK + TSpec V) ((R × (List EncodedEntry × Log)) × SkelState KemSK V) := do
  let answer ← (simulateQ (resumeImpl setup.hmac game.sessions services)
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge game consumed)).run (game, none)
  (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
    ((simulateQ (groupedClientL setup codec selected ciphertext identityIndex)
      (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
        (owners, log ++ [some ephemeral.secret]))).run answer.2

/-- The post-challenge phase of the logged skeleton as a client of the coins and the table oracles (`postSkel` on a logged opaque context): the resumed logged client under the actual encapsulator, the post-challenge router holding `placeholder` and the CCA evaluation, each forwarding the table oracles, followed by the decision. It is given the challenger's key pair, the challenge ciphertext and the prechallenge context; it has no candidate argument. -/
noncomputable def postSkelL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) : OracleComp (SkelSpec V) Bool :=
  match context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners log next)) state _ =>
    if value.keys.pqKey = chosen.1 then
      skelDecide (KemSK := KemSK) <$> simulateQ (fwd (T := TSpec V) (evalLayer setup chosen.2 challenge))
        (((simulateQ (fwdOption (T := TSpec V) (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder))
          (simulateQ (fwd (T := TSpec V) (PqxdhRegistrationJointKemEncapsulation.actual setup))
            (skelResumeL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
              (decideTag decision) raw value ephemeral consumed native.2 owners log next selected.val challenge
              services))).run).run (eraseJoint state))
    else pure false
  | _ => pure false

/-- The cache of the shared table held by the native state of an active logged prechallenge context. -/
def cacheOfL {count : Nat} : OpaqueContext Reader KemSK A X count → HmacOracle.QueryCache
  | .ready _ _ (some (.pending _ _ _ _ native _ _ _)) _ _ => native.1.cache
  | _ => ∅

/-- G1's prefix for the logged KEM-ideal branch: the challenger's key generation, the logged stopped-source prefix up to the selected raw accept and the challenger's encapsulation, returning the table cache at the cut and the candidate-free context. -/
noncomputable def sharedStartL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    ProbComp (HmacOracle.QueryCache ×
      ((MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)) := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  pure (cacheOfL context, (chosen, context, encapsulated.1))

/-- G1's client for the logged KEM-ideal branch: the logged skeleton's post-challenge phase with the native services, on G1's interface. -/
noncomputable def sharedClientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext) :
    OracleComp PqxdhExtractRomHiddenSuffix.HiddenSpec Bool :=
  simulateQ (compileHidden setup.hmac) (postSkelL setup codec checks decision count selected
    (nativeServices setup codec checks) context.1 context.2.2 context.2.1)

/-- The root client of the logged KEM-ideal branch (stage S2 over the logged source): `sharedStartL` and `postSkelL` with the native services, with the public table at the cut held inside. It has no candidate argument. -/
noncomputable def rootClientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) : OracleComp PqxdhCorrelatedExpand.RootSpec Bool :=
  PqxdhRegistrationJointKemRootExpand.internalize (sharedStartL (Reader := Reader) setup codec checks ensureInit
      supplied decision work runtime count selected index)
    (fun context => postSkelL setup codec checks decision count selected (nativeServices setup codec checks) context.1
      context.2.2 context.2.1)

/-- The factored root client of the logged KEM-ideal branch (stage S3b over the logged source): `postSkelL` with the factored services; its value requests return 108-byte outputs. It has no candidate argument. -/
noncomputable def entryClientL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) : OracleComp (EntrySpec Output) Bool :=
  internalizeV (sharedStartL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
      selected index)
    (fun context => postSkelL setup codec checks decision count selected (factoredServices setup codec checks)
      context.1 context.2.2 context.2.1)

/-- The key-schedule distinguisher of entry 0 of the logged branch (`entryD` on `entryClientL`). -/
noncomputable def entryDL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) : PqxdhServerAuthKeySchedule.Distinguisher :=
  fun value => (simulateQ (firstTable value (PqxdhServerAuthKeySchedule.fromRoot setup.source <$> ($ᵗ RootOutput)))
    (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' (∅, none)

end Post

/-! ### The hybrid of stage S7, generic in the client -/

section Hybrid

/-- The `k`-th hybrid of stage S7 for any value-valued client: the first `k` fresh hidden coordinates get 108 uniform bytes, every later one the key-schedule output of a fresh uniform root. -/
noncomputable def hybridOf (source : FixedHkdfSha512NoSaltSource) (client : OracleComp (EntrySpec Output) Bool)
    (k : ℕ) : ProbComp Bool :=
  (simulateQ (indexedImpl (sampler source k)) client).run'
    ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0)

/-- The key-schedule distinguisher of the `k`-th fresh hidden entry of any value-valued client: its `k`-th hybrid with that entry answered by the given 108 bytes. -/
noncomputable def entryDkOf (source : FixedHkdfSha512NoSaltSource) (client : OracleComp (EntrySpec Output) Bool)
    (k : ℕ) : PqxdhServerAuthKeySchedule.Distinguisher :=
  fun value => (simulateQ (indexedImpl (pin k value (sampler source k))) client).run'
    ((∅ : (PqxdhCorrelatedExtractFamily.Message →ₒ Output).QueryCache), 0)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The classical hybrid is `hybridOf` at the classical factored root client. -/
theorem hybrid_hybridOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (k : ℕ) :
    PqxdhRegistrationJointKemSecondEntry.hybrid (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index k =
      hybridOf setup.source (PqxdhRegistrationJointKemEntryFactor.entryClient (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index) k := rfl

/-- The classical key-schedule distinguisher of the `k`-th entry is `entryDkOf` at the classical factored root client. -/
theorem entryDk_entryDkOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (k : ℕ) :
    PqxdhRegistrationJointKemSecondEntry.entryDk (Reader := Reader) setup codec checks ensureInit supplied decision work
        runtime count selected index k =
      entryDkOf setup.source (PqxdhRegistrationJointKemEntryFactor.entryClient (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index) k := rfl

/-- The key-schedule distinguisher of the `k`-th fresh hidden entry of the logged branch. -/
noncomputable def entryDkL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (k : ℕ) : PqxdhServerAuthKeySchedule.Distinguisher :=
  entryDkOf setup.source (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime
    count selected index) k

end Hybrid

/-! ### The targets of U-L1 -/

section Targets
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The logged two-slot world: `PqxdhRegistrationJointKemSecondEntry.slotGame` with the logged factored root client, through the first-touch slot allocator in front of the persistent lazy table on `n` slots. -/
noncomputable def laterSlotGame (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (n : ℕ) : ProbComp Bool :=
  (simulateQ (slotImpl (D := PqxdhCorrelatedExtractFamily.Message) (tableService (n := n)))
    (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
      index)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- The loss of U-L1 at a logged source budget: the logged form of `PqxdhRegistrationJointKemKeyTransfer.allIdealLoss` (term by term, with `rootClientL` and `entryDkL` for `rootClient` and `entryDk`), which is the right side of `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`; that is the guessing term of G1 at the accept, finish and HMAC caps, the two HMAC-SHA-512 PRF advantages of the indexed reductions of `rootClientL`, and the four key-schedule advantages of each of the two entry distinguishers `entryDkL k`. Decorrelation caveat (route R1): in LQ-F the post-run adversary knows both hidden entries' 128-byte DH coordinates exactly, and their unpredictability and mutual independence rest on R1 alone (module docstring). -/
noncomputable def slotLossL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : SourceKind → ℕ) : ℝ :=
  ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
    ∑ slot ∈ Finset.range 2,
      (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
        ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
        (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
          ensureInit supplied decision work runtime count selected index) slot)) +
    ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
      (entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index k)

/-- The coin bill of the logged root client (LQ-F design-v2 D8): the classical `PqxdhRegistrationJointKemRootCosts.rootBill`, the logged prechallenge bills having the classical closed form, the Server read weighing 0, and the post-run coins, HMAC and BLAKE2b entering through the logged source budget (at the compiled LQ-F program, `laterTransported`). -/
def rootBillL (caps : PqxdhServerAuthSourceCosts.KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes) (count : Nat)
    (budget : SourceKind → ℕ) : ℕ :=
  PqxdhRegistrationJointKemRootCosts.rootBill caps qInit supplied count budget

/-- `rootBillL` is the classical root bill. -/
theorem rootBillL_eq (caps : PqxdhServerAuthSourceCosts.KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes)
    (count : Nat) (budget : SourceKind → ℕ) :
    rootBillL caps qInit supplied count budget =
      PqxdhRegistrationJointKemRootCosts.rootBill caps qInit supplied count budget := rfl

/-- The guessing term of item 2 at the transported LQ-F caps: the accept, finish and HMAC caps of the compiled LQ-F program add up to `qAccept + qFinish + (qHmac + qHmac₂)`; the post-run HMAC budget enters with coefficient one. -/
theorem later_guess_term (bounds : FreshBounds) (budget : Budget) (post : PostBudget) :
    laterTransported bounds budget post (.inl 3) + laterTransported bounds budget post (.inl 5) +
        laterTransported bounds budget post (.inl 6) =
      budget.accept + budget.finish + (budget.hmac + post.hmac) := by
  simp [laterTransported]

/-- `slotLossL` at the transported caps of the compiled LQ-F program: its first term is `(qAccept + qFinish + qHmac + qHmac₂)/2^256`. -/
theorem slotLossL_transported (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (bounds : FreshBounds) (budget : Budget) (post : PostBudget) :
    slotLossL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (laterTransported bounds budget post) =
      ((budget.accept + budget.finish + (budget.hmac + post.hmac) : ℕ) : ℝ) / 2 ^ 256 +
        ∑ slot ∈ Finset.range 2,
          (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
            ensureInit supplied decision work runtime count selected index) slot)).boolDistAdvantage
            (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL (Reader := Reader) setup codec checks
              ensureInit supplied decision work runtime count selected index) slot)) +
        ∑ k ∈ Finset.range 2, keyScheduleBound setup.source setup.hmac
          (entryDkL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
            index k) := by
  rw [slotLossL, later_guess_term]

/-- Target of U-L1, generic form (LQ-F design-v2 unit A2, `PqxdhDeploymentLaterServerItemKeys.opaqueBranchL_slots_two`): the logged counterpart of `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`. For every logged-source program within a logged source budget (caps per source14 kind through `LaterServerReserve.laterKind`; the Server read has no kind and needs no cap) and under `SourceFullCorrect`, the logged opaque KEM-ideal branch and the logged two-slot world differ by at most `slotLossL`. Decorrelation caveat (route R1): see `slotLossL`. -/
def OpaqueBranchSlotsTwoTargetL : Prop :=
  ∀ {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (budget : SourceKind → ℕ),
    (∀ kind, work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some kind) (budget kind)) →
    SourceFullCorrect setup.source setup.hmac →
    (PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision
        work runtime count selected index false).boolDistAdvantage
      (laterSlotGame (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
        index 2) ≤
      slotLossL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        budget

/-- Target of U-L1 at the compiled LQ-F program (LQ-F design-v2 unit A2, `PqxdhDeploymentLaterServerItemKeys.later_slots_two`): for a run-phase adversary within its budget and a post-run adversary within its post budget on every input, the logged opaque KEM-ideal branch of the per-target decision `LaterServerTransfer.decision` (the branch that remains after `kem_transfer_server`) and the logged two-slot world differ by at most `slotLossL` at the transported caps, whose first term is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (`slotLossL_transported`). Decorrelation caveat (route R1): see `slotLossL`. LQ-F claims confidentiality only. -/
def LaterSlotsTwoTarget : Prop :=
  ∀ {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks),
    SourceFullCorrect setup.source setup.hmac →
    ∀ (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
      (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget),
    budget.Respects first →
    ∀ (post : PostBudget), (∀ output reveal, post.Respects (second output reveal)) →
    ∀ (event : PqxdhDeploymentKemTransfer.Observed Out → Bool)
      (claim : PqxdhDeploymentKemTransfer.Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
      (runtime : A),
    (PqxdhDeploymentLaterServerOpaque.opaqueBranch (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val false).boolDistAdvantage
      (laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2) ≤
      slotLossL (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val (laterTransported bounds budget post)

/-- The generic target of U-L1 gives its instance at the compiled LQ-F program: the compiled program meets the logged source budget `laterTransported` (`PqxdhDeploymentLaterServerCompileBudget.compile_server_certified`). -/
theorem laterSlotsTwo_of_generic (generic : OpaqueBranchSlotsTwoTargetL) : LaterSlotsTwoTarget :=
  fun setup codec route checks correct ensureInit bounds mode first second budget respects post postRespects event
      claim g runtime =>
    generic setup codec checks ensureInit none
      (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime budget.create
      (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val (laterTransported bounds budget post)
      (PqxdhDeploymentLaterServerCompileBudget.compile_server_certified setup codec route bounds mode first second
        budget respects post postRespects) correct

end Targets

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.acceptStepL_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.acceptStepL_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.skelImplL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.skelImplL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.skelImplL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.skelImplL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.groupedClientL_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.hybrid_hybridOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.hybrid_hybridOf

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.entryDk_entryDkOf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.entryDk_entryDkOf

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.rootBillL_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.rootBillL_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.later_guess_term' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.later_guess_term

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.slotLossL_transported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.slotLossL_transported

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.laterSlotsTwo_of_generic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets.laterSlotsTwo_of_generic
