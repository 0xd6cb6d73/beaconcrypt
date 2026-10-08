import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonNative

/-!
# The KEM-ideal branch as G1's shared world (item 2, stage S1b)

This module completes stage S1b of the item 2 plan. The main theorem `opaqueBranch_shared` states that the opaque raw-ordinal branch of theorem T6 with the KEM-ideal bit (H0 of the plan; equal to H0b by stages S0a and S0b) is G1's shared world:

```text
opaqueBranch … false = PqxdhExtractRomHiddenSuffix.sharedGame (sharedStart …) (sharedClient …)
```

- `sharedStart` is the prechallenge phase: the challenger's key generation, the stopped-source prefix up to the selected raw accept (`PqxdhRegistrationJointKemRawOpaque.sourcePreOpaque`) and the challenger's encapsulation. It returns the cache of the shared zero-key 192-byte Extract table held by the native state at the cut (`cacheOf`) and the context: the challenger's key pair, the prechallenge context and the challenge ciphertext. It returns no candidate; the candidate is G1's secret, which `sharedGame` draws after `sharedStart`, exactly where the opaque branch draws its uniform candidate.
- The client `sharedClient` is the post-challenge phase of the services skeleton (`postSkel` of `PqxdhRegistrationJointKemPostSkeletonServices`) with the native services, compiled to G1's interface by `compileHidden`: coins stay coins, a direct read stays a direct read, and a hidden read at coordinates `m` becomes G1's hidden read at `m` followed by real Expand (`PqxdhSecretInputKdf.expandRoot`) of the block. The client has no candidate argument.

So in this form the candidate is G1's secret: it is the 32-byte suffix of every hidden read, which `sharedImpl` answers from the one shared table at `familyInput m secret`, and it occurs nowhere else. Every other read of that table, including the adversary's public HMAC on the zero-key 192-byte slice, other Server and Beacon roots and the cache keys written before the cut, is a direct read or a prefix cache key of the same table. Stage S1c applies G1 (`PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`) to move the hidden entries into a coordinate-keyed table.

Proof. `opaqueBranch_grouped` gives the grouped branch. Its native layer splits (`groupedImpl_split`, `resumeImpl_split`, through `split_run`): the native state with the table cache is the skeleton state with the table below it at the candidate (`opRoot`). The table then moves below the actual encapsulator (`push_stateless`), below the post-challenge router (`push_option`, after `run_eraseOption` removes its erased observers) and below the CCA evaluation (`push_stateless`); the decision reads none of the states. At the bottom, `opRoot` with uniform coins is G1's `sharedImpl` composed with `compileHidden` (`shared_compile`). These are program equalities; they charge no advantage, and no assumption is added.

`resume_lift_backend` is the backend-generic form of `PqxdhRegistrationJointKemOpaqueResume.resume_lift` that the plan asks for: the Server's resumption under any prefix interpreter and any interpreter of its private tail, whose root request is no longer tied to the restricted Extract-ROM interpreter with the candidate.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree PqxdhRegistrationJointBeaconOpaqueFinish
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)
open PqxdhServerAuthNative (NativeGame NativeState eraseObservers)

/-! ### The backend-generic resumption -/

section Resume

open PqxdhRegistrationJointKemOpaqueResume (prefixLift tailLift)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The backend-generic restatement of `PqxdhRegistrationJointKemOpaqueResume.resume_lift`: under any prefix interpreter and any interpreter of the private tail (whose root request may be answered by any backend), the Server's resumption is the compiled suffix under the prefix interpreter followed by the tail under the tail interpreter. -/
theorem resume_lift_backend (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes)
    (preImpl : QueryImpl (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) m)
    (tailImpl : QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) m) :
    simulateQ (preImpl + tailImpl)
        (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw verified
          ephemeral ciphertext token state consumed) =
      (do
        let collected ← simulateQ preImpl
          ((PqxdhRegistrationJointKemOpaqueSuffix.compiled setup codec checks identityIndex raw verified ephemeral
            ciphertext token).run consumed)
        simulateQ tailImpl (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity state collected)) := by
  have prefixPart : ∀ {α : Type} (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α),
      simulateQ (preImpl + tailImpl) (simulateQ (prefixLift (Reader := Reader)) work) = simulateQ preImpl work := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.apply_compose, prefixLift, simulateQ_spec_query, QueryImpl.add_apply_inl]
  have tailPart : ∀ {α : Type} (work : OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) α),
      simulateQ (preImpl + tailImpl) (simulateQ (tailLift (KemSK := KemSK)) work) = simulateQ tailImpl work := by
    intro _ work
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.apply_compose, tailLift, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp only [PqxdhRegistrationJointKemOpaqueResume.resume, simulateQ_bind, prefixPart, tailPart]

/-- The skeleton's resumption interpreter is an instance: its prefix interpreter forwards, its tail interpreter is the skeleton's private native tail. -/
theorem resumeImpl_backend (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) {V : Type}
    (services : Services V Response) :
    resumeImpl (Reader := Reader) (KemSK := KemSK) hmac index services =
      (show QueryImpl (Enc KemSK) (StateT (SkelState KemSK V) (OracleComp (Enc KemSK + TSpec V))) from
        fun query => StateT.mk fun state => (fun reply => (reply, state)) <$> encLift (V := V) query) +
      (show QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK)
          (StateT (SkelState KemSK V) (OracleComp (Enc KemSK + TSpec V))) from
        fun query => liftT (resumeTail hmac index services query)) := by
  funext query
  rcases query with query | query <;> rfl

end Resume

/-! ### The bottom of the stack -/

section Bottom

open PqxdhExtractRomHiddenSuffix (HiddenSpec sharedImpl)

/-- G1's interface for the skeleton with root-valued hidden reads: coins and direct reads are forwarded, a hidden read at `m` is G1's hidden read at `m` followed by real Expand. -/
noncomputable def compileHidden (hmac : PqxdhSecretInputKdf.HmacSha512) :
    QueryImpl (SkelSpec RootOutput) (OracleComp HiddenSpec) :=
  (fun query => (HiddenSpec.query (.inl query) : OracleComp HiddenSpec _) : QueryImpl unifSpec (OracleComp HiddenSpec)) +
  ((fun point => PqxdhSecretInputKdf.expandRoot hmac <$> (HiddenSpec.query (.inr (.inl point)) : OracleComp HiddenSpec _) :
      QueryImpl (ValueOracle RootOutput) (OracleComp HiddenSpec)) +
    (fun point => (HiddenSpec.query (.inr (.inr point)) : OracleComp HiddenSpec _) :
      QueryImpl PqxdhExtractRomHiddenSuffix.TableOracle (OracleComp HiddenSpec)))

/-- G1's shared world at the candidate, after `compileHidden`, is the table operation `opRoot` with uniform coins. -/
theorem shared_compile {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : MlKemSharedSecret)
    (work : OracleComp (SkelSpec RootOutput) α) (cache : HmacOracle.QueryCache) :
    (simulateQ (sharedImpl candidate) (simulateQ (compileHidden hmac) work)).run cache =
      (simulateQ (tableAt (fun work => work) (opRoot hmac candidate)) work).run cache := by
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext query
  rcases query with coin | (point | point)
  · simp only [QueryImpl.apply_compose, compileHidden, QueryImpl.add_apply_inl, simulateQ_spec_query]
    rfl
  · apply StateT.ext
    intro current
    simp only [QueryImpl.apply_compose, compileHidden, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      simulateQ_map, simulateQ_spec_query, StateT.run_map]
    rfl
  · simp only [QueryImpl.apply_compose, compileHidden, QueryImpl.add_apply_inr, simulateQ_spec_query]
    rfl

end Bottom

/-! ### Coins through the interpreter stack -/

section Coins

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

theorem actual_coins (setup : Setup baseSpec KemSK) {α : Type} (work : ProbComp α) :
    simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) (coinsEnc work) = PqxdhLiveKemBirth.coins work := by
  rw [coinsEnc, ← QueryImpl.simulateQ_compose]
  rfl

theorem router_coins (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (challenge : MlKem768Ciphertext)
    (candidate : MlKemSharedSecret) {α : Type} (work : ProbComp α) (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate)
        (PqxdhLiveKemBirth.coins work)).run).run state =
      (fun reply => (some reply, state)) <$> PqxdhPrivateKemSource.ccaCoins work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhLiveKemBirth.coins, PqxdhPrivateKemSource.ccaCoins, simulateQ_bind, simulateQ_spec_query,
        OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind] at ih ⊢
      simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run,
        bind_map_left]
      exact bind_congr fun reply => ih reply

theorem evalLayer_coins (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext)
    {α : Type} (work : ProbComp α) :
    simulateQ (evalLayer setup secret challenge) (PqxdhPrivateKemSource.ccaCoins work) = work := by
  have lifted : PqxdhPrivateKemSource.ccaCoins (baseSpec := baseSpec) work =
      PqxdhPrivateKemSource.ccaAmbient (OracleComp.liftComp work (unifSpec + baseSpec)) := by
    rw [PqxdhPrivateKemSource.ccaAmbient, OracleComp.liftComp_def, ← QueryImpl.simulateQ_compose]
    rfl
  rw [lifted]
  refine (QueryImpl.simulateQ_compose (kemAmbientImpl setup.baseImpl)
    (setup.kem.IND_CCA_postChallengeImpl secret challenge) _).trans ?_
  change PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem secret challenge _ = _
  rw [PqxdhDynamicKemPost.ambient, simulateQ_kemAmbient_liftProbComp]

end Coins

/-! ### The resumed client -/

section Split

open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointAcceptKemCut (tagged)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X R : Type}

/-- The grouped resumption is the skeleton's resumption with the native services, with the shared table below it at the candidate and the native state represented by the table cache and the skeleton state. -/
theorem groupedResume_split (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    groupedResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        next selected ciphertext candidate =
      (fun result : ((R × List EncodedEntry) × SkelState KemSK RootOutput) × HmacOracle.QueryCache =>
          (result.1.1, join result.2 result.1.2)) <$>
        (simulateQ (tableAt coinsEnc (opRoot setup.hmac candidate))
          (skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native.2 owners
            next selected ciphertext (nativeServices setup codec checks))).run native.1.cache := by
  unfold groupedResume skelResume
  have start : eraseObservers native = join native.1.cache ((native.2, none) : SkelState KemSK RootOutput) := rfl
  rw [start, split_run (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (resumeImpl setup.hmac native.2.sessions (nativeServices setup codec checks))
    (tableAt coinsEnc (opRoot setup.hmac candidate)) join
    (fun query cache state => resumeImpl_split setup codec checks native.2.sessions candidate query cache state),
    simulateQ_bind, StateT.run_bind, bind_map_left, map_bind]
  refine bind_congr fun result => ?_
  exact split_run (eraseImpl eraseObservers (groupedImpl setup codec checks identityIndex publicIdentity candidate))
    (skelImpl setup codec checks identityIndex publicIdentity (nativeServices setup codec checks))
    (tableAt coinsEnc (opRoot setup.hmac candidate)) join
    (fun query cache state => groupedImpl_split setup codec checks identityIndex publicIdentity candidate query cache state)
    _ result.2 result.1.2

end Split

/-! ### The post-challenge phase and the branch -/

section Post

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext toContext sourcePreOpaque opaqueBranch)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder)
open PqxdhExtractRomHiddenSuffix (sharedImpl sharedGame)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The cache of the shared table held by the native state of an active prechallenge context. -/
def cacheOf {count : Nat} : OpaqueContext Reader KemSK A X count → HmacOracle.QueryCache
  | .ready _ _ (some (.pending _ _ _ _ native _ _)) _ _ => native.1.cache
  | _ => ∅

theorem evaluate_layer (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext) {α : Type}
    (client : OracleComp (MlKemCCAOracleSpec baseSpec) α) :
    PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem secret challenge client =
      simulateQ (evalLayer setup secret challenge) client :=
  (QueryImpl.simulateQ_compose (kemAmbientImpl setup.baseImpl)
    (setup.kem.IND_CCA_postChallengeImpl secret challenge) client).symm

/-- The post-challenge step of the grouped branch at a candidate, with the CCA evaluation and the decision, is G1's shared world at that candidate on the skeleton's post-challenge phase, started from the table cache at the cut. -/
theorem post_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) (context : OpaqueContext Reader KemSK A X count) (candidate : MlKemSharedSecret) :
    PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
        (groupedPost setup codec checks decision count selected ⟨chosen.1, challenge, context⟩ candidate) =
      (simulateQ (sharedImpl candidate) (simulateQ (compileHidden setup.hmac)
        (postSkel setup codec checks decision count selected (nativeServices setup codec checks) chosen challenge
          context))).run' (cacheOf context) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  all_goals try (simp only [groupedPost, postSkel, PqxdhDynamicKemPost.evaluate, simulateQ_pure, map_pure,
    StateT.run'_eq, StateT.run_pure]; rfl)
  · by_cases active : value.keys.pqKey = chosen.1
    · have router := run_eraseOption eraseJoint eraseJoint_idem
        (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder)
        (post_neverRead setup.joint setup.kem selected.val
          (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          (groupedResume setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
            (decideTag decision) raw value ephemeral consumed native owners next selected.val challenge candidate))
        (eraseJoint state)
      rw [eraseJoint_idem] at router
      simp only [groupedPost, postSkel, active, ↓reduceIte, cacheOf]
      rw [bind_pure_comp, evaluate_map, Functor.map_map, evaluate_layer, ← router, groupedResume_split,
        simulateQ_map (impl := PqxdhRegistrationJointKemEncapsulation.actual setup),
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
    · simp only [groupedPost, postSkel, active, ↓reduceIte, PqxdhDynamicKemPost.evaluate, simulateQ_pure, map_pure,
        StateT.run'_eq, StateT.run_pure]
      rfl

/-- G1's prefix for the KEM-ideal branch: the challenger's key generation, the stopped-source prefix up to the selected raw accept and the challenger's encapsulation. It returns the table cache at the cut and the context of the post-challenge phase: the challenger's key pair, the prechallenge context and the challenge ciphertext. -/
noncomputable def sharedStart (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    ProbComp (HmacOracle.QueryCache ×
      ((MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)) := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  pure (cacheOf context, (chosen, context, encapsulated.1))

/-- G1's client for the KEM-ideal branch: the skeleton's post-challenge phase with the native services, on G1's interface. -/
noncomputable def sharedClient (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (context : (MlKem768PublicKey × KemSK) × OpaqueContext Reader KemSK A X count × MlKem768Ciphertext) :
    OracleComp PqxdhExtractRomHiddenSuffix.HiddenSpec Bool :=
  simulateQ (compileHidden setup.hmac) (postSkel setup codec checks decision count selected
    (nativeServices setup codec checks) context.1 context.2.2 context.2.1)

/-- The grouped branch with the KEM-ideal bit is G1's shared world. -/
theorem groupedBranch_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    groupedBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false =
      sharedGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index)
        (sharedClient setup codec checks decision count selected) := by
  unfold groupedBranch sharedGame sharedStart
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun chosen => bind_congr fun context => bind_congr fun encapsulated =>
    bind_congr fun uniform => ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact post_shared setup codec checks decision count selected chosen encapsulated.1 context uniform

/-- Stage S1b. The opaque raw-ordinal branch of theorem T6 with the KEM-ideal bit is G1's shared world: the prefix produces the table cache at the cut and a candidate-free context, the candidate is G1's secret drawn after the prefix, and the post-challenge phase is the services skeleton with the native services as a client of G1's hidden and direct table reads. This is a program equality; it charges no advantage and adds no assumption. -/
theorem opaqueBranch_shared (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        false =
      sharedGame (sharedStart (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
          selected index)
        (sharedClient setup codec checks decision count selected) :=
  (opaqueBranch_grouped setup codec checks ensureInit supplied decision work runtime count selected index false).trans
    (groupedBranch_shared setup codec checks ensureInit supplied decision work runtime count selected index)

end Post

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resume_lift_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resume_lift_backend

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resumeImpl_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.resumeImpl_backend

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.shared_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.shared_compile

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.actual_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.actual_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.router_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.router_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.evalLayer_coins' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.evalLayer_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedResume_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedResume_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.evaluate_layer' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.evaluate_layer

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.post_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.post_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedBranch_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.groupedBranch_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared
