import BeaconcryptCore.Computational.PqxdhFirstRecordStopBound
import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical
import BeaconcryptCore.Computational.VCVioForwardProgramLogic
/-!
# Target-free bound on the first-record stop term

`PqxdhFirstRecordStopBound.sourceStopGame` is the source-only restricted repetition game of the first record of Beacon `b`: after the selected first Server builder, the history-extended original source post runs, and the event is that two ordered sealing positions use the selected sending chain while that chain is still undisclosed. `source_stop_bound` bounds it, for every post whose continuations are bounded by a post query budget, by `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`, where `qSend`, `qRaw` and `qFinish` are the budgets for sends, raw receives and attempted finishes. `stop_bound` transfers the bound to `PqxdhFirstBeaconRecordIntegrity.stopGame` through `PqxdhFirstRecordStopBound.stopGame_le`; `forgery_stop_bound` and `canonical_stop_bound` instantiate it for the forgery proxy and the canonical proxy with the certificate's post budget. `first_beacon_record_integrity_stop` substitutes the canonical instance into `PqxdhFirstBeaconRecordCanonical.first_beacon_record_integrity_canonical`, so the first Beacon record integrity bound consists of the target and completed-branch losses, the CTX loss, `2^-256` twice and the explicit statistical term above. It has exactly the premises of the canonical theorem; this module adds none.

The selected chain. For a Beacon owner the selected sending chain is `target`, the second 32 bytes of the uniform 64-byte initializer block (`beacon_root`); the first 32 bytes are `other`. In the 64-byte response `other ++ target`, the second half `target` is both the Beacon send chain and the Server receive chain (`marked_kernel`, `server_kernel`).

Tagged interpreter. A tagged kernel (`TKernel`) has chain slots that are either `known` bytes or the `hidden` selected chain; `mapKernel target` reads the hidden slot as `target`. The target-free services `taggedLabels` answer a private derivation on the hidden slot with the programmed reply and on a known chain with its prior table value, and append the known chain's bytes to a log; openings, sealings and the public services (public HKDF included) are the actual ones, which do not read the private table (`open_table`, `seal_table`). `labels_near` couples the concrete services with them until the selected value is logged, because a concrete derivation on a known chain differs from the target-free one only at the selected address. The tagged world `world` runs records under these services, reveals on tagged roles (a hidden chain is revealed as a fixed chain, so a concrete reveal of the selected chain is the concrete bad event), source-local selectors, and attempted finishes (`taggedFinishOp`), which install the hidden-send kernel on the selected message and otherwise the actual initializer reply. `post_coupled` couples the whole adaptive post up to the concrete bad event (the selected chain is disclosed) or the tagged bad event (the selected value is logged, `Exposed`), and `post_triple` concludes with the invariant `GoodState` (a wrapper around `Good`): Server peers and Beacons other than the first have known send chains, only the first Beacon can be marked, the hidden chain occurs at most once among the seal chains, the first Beacon and a pending marked finish, and every known seal chain is logged. Under it two ordered seals at the selected chain force a logged selected value (`repeated_impossible`).

Builder and start. `taggedBuild` is the selected first Server builder over tagged kernels, coupled with the concrete builder by `build_coupled`; it does not use the initializer callback (`build_initial`). `build_good` gives the invariant at the start of the post from `StartFront`, which holds for the all-known image of the prepared front because only slot zero can hold a generated KEM handle (`PqxdhFirstRecordStopBound.front_only`, `start_front`). A marked preparation holds a generated KEM handle (`existing_markable`, from `lifted_unchallenged` and `lifted_unmarked`). The actual initializer callback with response `other ++ target` returns the hidden-send kernel on the selected message (`initial_marked`) and agrees with the target-free callback `initialFree`, whose selected half is zero, on every other request (`initial_unmarked`). `stop_tagged` combines these: the source stop run is at most the probability that `target` is in the final log of the target-free run `taggedRun`, whose arguments are the opposite half, the prepared context, the nonce, the next chain and the key, but not `target`.

Sampling and budget. `RawCtxSelectedInitialSecond.second_observed` splits the initializer block into two independent uniform halves; `delayed_bound` draws `target` after the target-free run (`PqxdhSecretInputKdf.evalSPMF_sample_comm`) and applies `RawCtxSelectedInputCandidates.uniform_candidates` to the final log. The log grows by at most one entry per private derivation request (`label_growth`); a symbolic send makes at most one request and a raw receive at most fifty-one (`RawCtxChainSend.program_kdf_bound`, `RawCtxChainReceiveBounds.receive_bound`, `RawCtxGenericFamilyBudgets.family_step`), an attempted finish runs one raw receive, and the builder one send. `weighted_growth` accumulates these weights along the post under its per-kind query budget (`run_log`).

Messages are byte strings that each side knows how to decode; the record writer and the frame decoder are abstract functions of the environment, and no property of a concrete serialization library is used.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged
open PqxdhFirstRecordStopBound (Retains OnlyFirst ExistingKem)
open PqxdhGeneratedBeaconState (KemHandle)

section NoClone

/-- A state-monad bind applied to a state runs the first computation from that state. -/
theorem bind_apply {σ α β : Type} {m : Type → Type} [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = x s >>= fun p => f p.1 p.2 := rfl

/-- A state-monad return applied to a state returns the value with that state. -/
theorem pure_apply {σ α : Type} {m : Type → Type} [Monad m] (a : α) (s : σ) : (pure a : StateT σ m α) s = pure (a, s) := rfl

/-- A Beacon phase after an operation is the phase before it, or an established or aborted phase. -/
def Settled {D K Kernel : Type} (before after : RawCtxBeaconLifecycle.Phase D K Kernel) : Prop :=
  after = before ∨ (∃ control ad kernel, after = .established control ad kernel) ∨ ∃ control, after = .aborted control

/-- Every phase is settled with respect to itself. -/
theorem settled_refl {D K Kernel : Type} (phase : RawCtxBeaconLifecycle.Phase D K Kernel) : Settled phase phase :=
  Or.inl rfl

/-- A settled phase without a generated KEM handle before has none after. -/
theorem settled_retains {D K Kernel : Type} (before after : RawCtxBeaconLifecycle.Phase D (KemHandle K) Kernel)
    (settled : Settled before after) (valid : Retains before) : Retains after := by
  rcases settled with rfl | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
  · exact valid
  · trivial
  · trivial

/-- A settled phase is an initialization-sent phase only if it is the phase before. -/
theorem settled_initSent {D K Kernel : Type} (before after : RawCtxBeaconLifecycle.Phase D K Kernel)
    (settled : Settled before after) (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (sent : after = .initSent control prekey oneTime kem) : before = after := by
  rcases settled with rfl | ⟨_, _, _, rfl⟩ | ⟨_, rfl⟩
  · rfl
  · cases sent
  · cases sent

/-- Settled phases compose. -/
theorem settled_trans {D K Kernel : Type} (first second third : RawCtxBeaconLifecycle.Phase D K Kernel)
    (left : Settled first second) (right : Settled second third) : Settled first third := by
  rcases right with rfl | established | aborted
  · exact left
  · exact Or.inr (Or.inl established)
  · exact Or.inr (Or.inr aborted)

/-- The generic Beacon record frontend keeps the phase or re-establishes it, for every call interpreter. -/
theorem beacon_settled {Kernel I D K σ : Type} (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (shared : σ)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxGenericRoleStorage.BeaconState Kernel I D K) × σ)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode query).run state).run shared)) :
    Settled state.beacon.phase result.1.2.beacon.phase := by
  cases phase : state.beacon.phase with
  | established control ad kernel =>
    rw [RawCtxGenericBeacon.established calls decode query state control ad kernel phase] at supported
    simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact Or.inr (Or.inl ⟨control, ad, _, rfl⟩)
  | fresh _ _ _ | freshWithCoins _ _ _ _ | initSent _ _ _ _ | aborted _ =>
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase] at supported
    subst supported
    cases query <;> exact Or.inl phase

/-- Every generic family record step keeps every Beacon phase or re-establishes it. -/
theorem frontend_settled {Kernel M P I D K σ : Type} {S B : Nat} (calls : RawCtxChainOwner.Calls Kernel (StateT σ ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT σ ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (roles : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B)
    (shared : σ) (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) × σ)
    (supported : result ∈ support (((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run roles).run shared))
    (position : Fin B) : Settled (roles.2 position).beacon.phase (result.1.2.2 position).beacon.phase := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  all_goals simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_apply, pure_apply,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  all_goals obtain ⟨inner, innerSupported, rfl⟩ := supported
  · exact settled_refl _
  · by_cases same : position = index
    · subst position
      simpa only [Function.update_self] using beacon_settled calls decode request (roles.2 index) shared inner innerSupported
    · simpa only [Function.update_of_ne same] using settled_refl (roles.2 position).beacon.phase
  · exact settled_refl _

/-- A finish attempt always ends established or aborted. -/
theorem finish_phase {Kernel I D K : Type} (control : pqxdh.BeaconInitSent)
    (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (staged : Option (PqxdhInitialGenericBeacon.Staged Kernel)) :
    (∃ c a k, (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase = .established c a k) ∨
      ∃ c, (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase = .aborted c := by
  unfold PqxdhInitialGenericBeacon.finish
  rcases staged with _ | staged
  · exact Or.inr ⟨_, rfl⟩
  · simp only
    split_ifs
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, _, _, rfl⟩

/-- A finish attempt settles the phase and never leaves it in the initialization-sent phase. -/
theorem finish_settled {Kernel I D K : Type} (control : pqxdh.BeaconInitSent)
    (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (staged : Option (PqxdhInitialGenericBeacon.Staged Kernel)) :
    Settled state.beacon.phase (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase ∧
      ∀ c p o k, (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase ≠ .initSent c p o k := by
  rcases finish_phase control state staged with ⟨c, a, k, equal⟩ | ⟨c, equal⟩
  · exact ⟨Or.inr (Or.inl ⟨c, a, k, equal⟩), fun _ _ _ _ => by rw [equal]; exact fun h => by cases h⟩
  · exact ⟨Or.inr (Or.inr ⟨c, equal⟩), fun _ _ _ _ => by rw [equal]; exact fun h => by cases h⟩

end NoClone

section Owner
open PqxdhNativeSharedPrefix PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)

/-- An attempted Beacon finish under the source interpreter settles the phase; from the initialization-sent phase it never stays there. -/
theorem owner_settled (raw : Pqxdh.Bytes) (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C))
    (result : PqxdhSelectedInitialOwnerCompiler.Reply I D K × RawCtxSharedPrimitive.SharedState (Local A N C))
    (supported : result ∈ support ((simulateQ (PqxdhSelectedInitialOwnerCompiler.source (extra := extra) (X := X) (Response := Response)
      pre application initial selector aux fixed writer prior parent key target nonce next read)
      (PqxdhSelectedInitialOwnerCompiler.owner raw before)).run state)) :
    Settled before.beacon.phase result.1.2.beacon.phase ∧
      ∀ control prekey oneTime kem, before.beacon.phase = .initSent control prekey oneTime kem →
        ∀ c p o k, result.1.2.beacon.phase ≠ .initSent c p o k := by
  unfold PqxdhSelectedInitialOwnerCompiler.owner at supported
  cases phase : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [phase] at supported
    suffices both : Settled before.beacon.phase result.1.2.beacon.phase ∧
        ∀ c p o k, result.1.2.beacon.phase ≠ .initSent c p o k from
      ⟨phase ▸ both.1, fun _ _ _ _ _ => both.2⟩
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    rcases prepared with ⟨_ | pending, middle⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact finish_settled control before none
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨kernel, _, supported⟩ := supported
      rcases kernel with ⟨_ | kernel, middle⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact finish_settled control before none
      · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨_, _, supported⟩ := supported
        simp only [PqxdhSelectedInitialOwnerCompiler.source, StateT.run_map, support_map,
          Set.mem_image] at supported
        obtain ⟨inner, _, rfl⟩ := supported
        exact finish_settled control before _
  | fresh _ _ _ | freshWithCoins _ _ _ _ | established _ _ _ | aborted _ =>
    simp only [phase, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    refine ⟨phase ▸ settled_refl _, fun _ _ _ _ impossible => ?_⟩
    cases impossible

variable {M P : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)

/-- Every operation of the original source post (records, reveals, selectors and attempted finishes) settles every Beacon phase. -/
theorem post_settled (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (state : PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B)
    (result : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query ×
      PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B)
    (supported : result ∈ support ((PqxdhSelectedPostCompiler.original pre application initial selector aux fixed writer prior parent
      key target nonce next sender route read query).run state))
    (position : Fin B) :
    Settled (state.1.roles.1.2 position).beacon.phase (result.2.1.roles.1.2 position).beacon.phase := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [PqxdhSelectedPostCompiler.original, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    cases request with
    | inl request =>
      simp only [RawCtxSelectedFamilyNonceCoupling.original, RawCtxSelectedMessageStopping.stopping, OptionT.run_mk,
        support_map, Set.mem_image] at innerSupported
      obtain ⟨record, recordSupported, rfl⟩ := innerSupported
      simp only [RawCtxSelectedMessageStopping.sourceRecord, QueryImpl.flattenStateT, StateT.run_mk, support_map,
        Set.mem_image] at recordSupported
      obtain ⟨front, frontSupported, rfl⟩ := recordSupported
      exact frontend_settled _ _ sender route read request state.1.roles.1 state.2 front frontSupported position
    | inr request =>
      simp only [RawCtxSelectedFamilyNonceCoupling.original, RawCtxSelectedMessageStopping.stopping, OptionT.run_mk,
        support_pure, Set.mem_singleton_iff] at innerSupported
      subst innerSupported
      exact settled_refl _
  · simp only [PqxdhSelectedPostCompiler.original, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact settled_refl _
  · simp only [PqxdhSelectedPostCompiler.original, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    by_cases same : position = index
    · subst position
      simpa only [PqxdhSelectedPostCompiler.install, Function.update_self] using
        (owner_settled pre application initial selector aux fixed writer prior parent key target nonce next read raw
          (state.1.roles.1.2 index) state.2 inner innerSupported).1
    · simpa only [PqxdhSelectedPostCompiler.install, Function.update_of_ne same] using settled_refl _

/-- The history-extended source post settles every Beacon phase over a whole adaptive run. -/
theorem observed_settled {Result : Type}
    (client : OracleComp (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (state : PqxdhFirstRecordNonceStop.History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B)
    (result : Result × (PqxdhFirstRecordNonceStop.History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B))
    (supported : result ∈ support ((simulateQ (PqxdhFirstRecordNonceStop.sourceObserved pre application initial selector aux fixed writer
      prior parent key target nonce next sender route read) client).run state))
    (position : Fin B) :
    Settled (state.2.1.roles.1.2 position).beacon.phase (result.2.2.1.roles.1.2 position).beacon.phase := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact settled_refl _
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, stepSupported, rest⟩ := supported
    simp only [PqxdhFirstRecordNonceStop.sourceObserved, StateT.run, support_map, Set.mem_image] at stepSupported
    obtain ⟨inner, innerSupported, rfl⟩ := stepSupported
    exact settled_trans _ _ _ (post_settled pre application initial selector aux fixed writer prior parent key target nonce next read
      sender route query state.2 inner innerSupported position) (ih inner.1 _ rest)

/-- The history-extended source post keeps every Beacon slot other than slot zero free of generated KEM handles over a whole adaptive run. -/
theorem observed_only {Result : Type} {Kem : Type}
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D (KemHandle Kem) X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (client : OracleComp (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S (B + 1))) Result)
    (state : PqxdhFirstRecordNonceStop.History S (B + 1) × PqxdhSelectedPostCompiler.SourceState M P I D (KemHandle Kem) A N C S (B + 1))
    (valid : OnlyFirst (fun position => (state.2.1.roles.1.2 position).beacon.phase))
    (result : Result × (PqxdhFirstRecordNonceStop.History S (B + 1) ×
      PqxdhSelectedPostCompiler.SourceState M P I D (KemHandle Kem) A N C S (B + 1)))
    (supported : result ∈ support ((simulateQ (PqxdhFirstRecordNonceStop.sourceObserved pre application initial selector aux fixed writer
      prior parent key target nonce next sender route read) client).run state)) :
    OnlyFirst (fun position => (result.2.2.1.roles.1.2 position).beacon.phase) := fun position nonzero =>
  settled_retains _ _ (observed_settled pre application initial selector aux fixed writer prior parent key target nonce next read
    sender route client state result supported position) (valid position nonzero)

/-- Over a whole adaptive run of the history-extended source post, a Beacon ends in the initialization-sent phase only if it started in that same phase. -/
theorem observed_initSent {Result : Type}
    (client : OracleComp (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (state : PqxdhFirstRecordNonceStop.History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B)
    (result : Result × (PqxdhFirstRecordNonceStop.History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B))
    (supported : result ∈ support ((simulateQ (PqxdhFirstRecordNonceStop.sourceObserved pre application initial selector aux fixed writer
      prior parent key target nonce next sender route read) client).run state))
    (position : Fin B) (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (sent : (result.2.2.1.roles.1.2 position).beacon.phase = .initSent control prekey oneTime kem) :
    (state.2.1.roles.1.2 position).beacon.phase = .initSent control prekey oneTime kem :=
  (settled_initSent _ _ (observed_settled pre application initial selector aux fixed writer prior parent key target nonce next read
    sender route client state result supported position) control prekey oneTime kem sent).trans sent

end Owner

section Unmarked
open PqxdhNativeSharedPrefix PqxdhBeaconPhase2Shared PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhSecretInputKdf PqxdhPhase1AcceptanceOracle
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhKemIndCca
open PqxdhGeneratedBeaconState (IdentityHandle)

/-- Simulating into another oracle computation never adds outputs. -/
theorem support_simulation {κ μ Result : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (OracleComp target)) (work : OracleComp source Result) :
    support (simulateQ impl work) ⊆ support work := by
  have kept := support_simulateQ_run'_subset (impl.liftTarget (StateT Unit (OracleComp target))) work ()
  simpa [simulateQ_liftTarget, StateT.run'_eq, liftM_run_StateT] using kept

/-- The result of a stateful simulation is an output of the simulated computation. -/
theorem support_state_simulation {κ μ Result Aux : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (StateT Aux (OracleComp target))) (work : OracleComp source Result)
    (state : Aux) (result : Result × Aux) (supported : result ∈ support ((simulateQ impl work).run state)) :
    result.1 ∈ support work := by
  apply support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ supported

variable {ι κ A I D K X Response KemSK : Type} {baseSpec : OracleSpec ι} {extra : OracleSpec κ}

/-- The preparation interface of an attempted finish as seen through the source-local callback lift. -/
noncomputable def liftedPreparation {σ C : Type} (pre : QueryImpl (Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A σ C) ProbComp))
    (application : Response → LocalCallback A σ C (Option Pqxdh.Bytes))
    (initial : Secrets PqxdhPhase2DecapsulationRouting.Shared → LocalCallback A σ C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A σ C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A σ C) ProbComp)) :
    QueryImpl (Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (RawCtxSharedPrimitive.SharedState (Local A σ C)) ProbComp) :=
  fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal pre application initial selector aux (.inl query)

/-- A preparation interface never answers a decapsulation at an existing KEM handle with the challenge marker. -/
def NeverChallenge {σ : Type} (pre : QueryImpl (Spec I D (KemHandle K) X Response PqxdhPhase2DecapsulationRouting.Shared)
    (StateT σ ProbComp)) : Prop :=
  ∀ value prior state (reply : Option PqxdhPhase2DecapsulationRouting.Shared × σ),
    reply ∈ support ((pre (.decapsulate value (.existing prior))).run state) → reply.1 ≠ some .challenge

/-- The source-local lift of the actual prepared preparation callback never answers a decapsulation at an existing KEM handle with the challenge marker. -/
theorem lifted_unchallenged (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (application : Response → LocalCallback A (BareState count) RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A (BareState count) RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A (BareState count) RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
      (StateT (ExternalState A (BareState count) RootOracle.QueryCache) ProbComp)) :
    NeverChallenge (liftedPreparation
      (PqxdhPreparedPrefixCallbacks.preparation (I := I) (D := D) (X := X) (Response := Response)
        attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
      application initial selector aux) := by
  intro value prior state result supported
  simp only [liftedPreparation, PqxdhSelectedInitialOwnerCompiler.sourceExternal, PqxdhSelectedStateInterpreter.evaluate,
    PqxdhSelectedCallbackCompiler.callback, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  have first := support_state_simulation _ _ _ _ innerSupported
  simp only [localCall, support_map, Set.mem_image] at first
  obtain ⟨core, coreSupported, equal⟩ := first
  have second := support_simulation _ _ coreSupported
  have reply := PqxdhFirstRecordStopBound.existing_unchallenged attachedVerify primitives count fixed localImpl baseImpl kem
    secret challenge value prior _ core second
  simpa only [PqxdhSelectedStateInterpreter.pair, ← equal] using reply

/-- No successful preparation of an attempted finish at a Beacon holding an existing KEM handle, under a preparation interface that never answers the challenge marker at existing handles (such as `lifted_unchallenged`), carries the selected-message installation marker. -/
theorem lifted_unmarked {σ : Type} (pre : QueryImpl (Spec I D (KemHandle K) X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT σ ProbComp)) (never : NeverChallenge pre) (fixed : FixedHkdfSha512NoSaltSource)
    (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (control : pqxdh.BeaconInitSent)
    (identity : I) (prekey oneTime : D) (prior : K) (raw : Pqxdh.Bytes) (state : σ)
    (result : Option (Prepared Response PqxdhPhase2DecapsulationRouting.Shared) × σ)
    (supported : result ∈ support ((simulateQ pre (prepare control identity prekey oneTime (.existing prior) raw)).run state))
    (prepared : Prepared Response PqxdhPhase2DecapsulationRouting.Shared) (found : result.1 = some prepared) :
    PqxdhInitialSelectedOrigin.mark fixed selectedMessage prepared.root = false :=
  PqxdhFirstRecordStopBound.prepare_unmarked pre fixed selectedMessage control identity prekey oneTime (.existing prior) raw
    (fun value current reply reached => never value prior current reply reached) state result supported prepared found

/-- On an unmarked request the retained initializer callback does not depend on the selected previous root or selected response. -/
theorem initial_unmarked {A N : Type} (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (previousRoot otherRoot : RootOutput) (response otherResponse : PqxdhInitialRootLabelService.Response)
    (secrets : Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (unmarked : PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false) :
    initialLocal (A := A) (N := N) fixed selectedMessage previousRoot response secrets =
      initialLocal fixed selectedMessage otherRoot otherResponse secrets := by
  unfold initialLocal
  funext state
  simp only [PqxdhInitialSelectedOrigin.mark] at unmarked
  cases request : PqxdhInitialRootLabelBridge.request fixed secrets with
  | known root => rfl
  | family message =>
    rw [request] at unmarked
    have different : message ≠ selectedMessage := by
      simpa [PqxdhInitialSelectedOrigin.selectedRequest] using unmarked
    simp only [PqxdhInitialRootAudit.retained, different, ite_false]

end Unmarked


section Coupling
open OracleComp.ProgramLogic.Relational
variable {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ α : Type}

/-- Two support properties of never-failing computations combine through the product coupling. -/
theorem product_coupling {β γ : Type} {first : ProbComp β} {second : ProbComp γ} {P : β → Prop} {Q : γ → Prop}
    (left : ∀ value ∈ support first, P value) (right : ∀ value ∈ support second, Q value) :
    RelTriple first second (fun value other => P value ∧ Q other) :=
  relTriple_prod left right

/-- From a state in an absorbing set, every final state of a stateful simulation stays in that set. -/
theorem run_absorbing {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (absorbing : ∀ query state, bad state → ∀ result ∈ support ((impl query).run state), bad result.2)
    (work : OracleComp spec α) (state : σ) (start : bad state) :
    ∀ result ∈ support ((simulateQ impl work).run state), bad result.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    intro result supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact start
  | query_bind query continuation ih =>
    intro result supported
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, stepSupported, rest⟩ := supported
    exact ih step.1 step.2 (absorbing query state start step stepSupported) result rest

/-- The postcondition of the up-to-bad coupling: a bad left state, a bad right state, or equal outputs with related states. -/
def UpTo {β : Type} (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (left : β × σ₁) (right : β × σ₂) : Prop :=
  bad₁ left.2 ∨ bad₂ right.2 ∨ (left.1 = right.1 ∧ related left.2 right.2)

/-- A run from a bad left state is coupled with any right computation under the up-to-bad postcondition. -/
theorem absorbed_left {β : Type} (impl₁ : QueryImpl spec (StateT σ₁ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (absorbing₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (work : OracleComp spec β) (first : σ₁) (bad : bad₁ first) (other : ProbComp (β × σ₂)) :
    RelTriple ((simulateQ impl₁ work).run first) other (UpTo related bad₁ bad₂) :=
  relTriple_post_mono (product_coupling (Q := fun _ => True)
    (run_absorbing impl₁ bad₁ absorbing₁ work first bad) (fun _ _ => trivial)) fun _ _ held => Or.inl held.1

/-- Any left computation is coupled with a run from a bad right state under the up-to-bad postcondition. -/
theorem absorbed_right {β : Type} (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (absorbing₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (work : OracleComp spec β) (second : σ₂) (bad : bad₂ second) (other : ProbComp (β × σ₁)) :
    RelTriple other ((simulateQ impl₂ work).run second) (UpTo related bad₁ bad₂) :=
  relTriple_post_mono (product_coupling (P := fun _ => True) (fun _ _ => trivial)
    (run_absorbing impl₂ bad₂ absorbing₂ work second bad)) fun _ _ held => Or.inr (Or.inl held.2)

/-- Up-to-bad coupling of two stateful simulations over different state spaces: if both bad sets are absorbing and every operation from related good states can be coupled with equal outputs and related states unless one side becomes bad, the whole adaptive runs are coupled the same way. -/
theorem coupled_run (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (absorbing₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (absorbing₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query first second, related first second → ¬ bad₁ first → ¬ bad₂ second →
      RelTriple ((impl₁ query).run first) ((impl₂ query).run second) (UpTo related bad₁ bad₂))
    (work : OracleComp spec α) (first : σ₁) (second : σ₂)
    (start : bad₁ first ∨ bad₂ second ∨ related first second) :
    RelTriple ((simulateQ impl₁ work).run first) ((simulateQ impl₂ work).run second) (UpTo related bad₁ bad₂) := by
  induction work using OracleComp.inductionOn generalizing first second with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rcases start with bad | bad | same
    · exact Or.inl bad
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr ⟨rfl, same⟩)
  | query_bind query continuation ih =>
    by_cases firstBad : bad₁ first
    · exact absorbed_left impl₁ related bad₁ bad₂ absorbing₁ _ first firstBad _
    by_cases secondBad : bad₂ second
    · exact absorbed_right impl₂ related bad₁ bad₂ absorbing₂ _ second secondBad _
    have same : related first second := by
      rcases start with bad | bad | same
      · exact absurd bad firstBad
      · exact absurd bad secondBad
      · exact same
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    refine relTriple_bind (step query first second same firstBad secondBad) fun reply₁ reply₂ held => ?_
    rcases held with bad | bad | ⟨equal, same⟩
    · exact absorbed_left impl₁ related bad₁ bad₂ absorbing₁ _ reply₁.2 bad _
    · exact absorbed_right impl₂ related bad₁ bad₂ absorbing₂ _ reply₂.2 bad _
    · rw [equal]
      exact ih reply₂.1 reply₁.2 reply₂.2 (Or.inr (Or.inr same))

/-- An event of the left run that excludes the left bad set and is impossible on related good pairs is at most the right bad probability. -/
theorem coupled_bound (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (related : σ₁ → σ₂ → Prop) (bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop)
    (absorbing₁ : ∀ query state, bad₁ state → ∀ result ∈ support ((impl₁ query).run state), bad₁ result.2)
    (absorbing₂ : ∀ query state, bad₂ state → ∀ result ∈ support ((impl₂ query).run state), bad₂ result.2)
    (step : ∀ query first second, related first second → ¬ bad₁ first → ¬ bad₂ second →
      RelTriple ((impl₁ query).run first) ((impl₂ query).run second) (UpTo related bad₁ bad₂))
    (work : OracleComp spec α) (first : σ₁) (second : σ₂) (start : related first second)
    (event : α × σ₁ → Prop) (excluded : ∀ result, event result → ¬ bad₁ result.2)
    (impossible : ∀ left right, related left right → ¬ bad₂ right → ∀ value, event (value, left) → False) :
    Pr[event | (simulateQ impl₁ work).run first] ≤ Pr[fun result => bad₂ result.2 | (simulateQ impl₂ work).run second] := by
  refine probEvent_le_of_relTriple (coupled_run impl₁ impl₂ related bad₁ bad₂ absorbing₁ absorbing₂ step work first second
    (Or.inr (Or.inr start))) fun left right held holds => ?_
  rcases held with bad | bad | ⟨equal, same⟩
  · exact absurd bad (excluded left holds)
  · exact bad
  · by_contra good
    exact impossible left.2 right.2 same good left.1 holds

end Coupling

section Labels
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation

/-- A tagged chain slot: the selected chain is `hidden`, every other chain is `known` with its bytes. -/
abbrev Chain := RawCtxSelectedChain.Slot
/-- The selected-message material slot of the stopped source. -/
abbrev Material := RawCtxSelectedMessageKey.Slot
/-- A ratchet kernel whose chains are tagged slots. -/
abbrev TKernel := RefinedRatchet Chain Chain Material
/-- The log of known chain inputs of private derivations, as 32-byte values. -/
abbrev Log := List RootOutput

/-- The chain bytes of a tagged slot, with the hidden slot read as the selected chain. -/
def reveal (target : RootOutput) : Chain → RatchetChain :=
  RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)

/-- The stopped-source kernel represented by a tagged kernel. -/
def mapKernel (target : RootOutput) : TKernel → RawCtxSelectedMessageReveals.Kernel :=
  mapChains (reveal target) (reveal target)

/-- The concrete private derivation of the stopped source on the bytes of a tagged slot, with the returned chain known. -/
noncomputable def concreteStep (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (slot : Chain) :
    Chain × Material :=
  let reply := RawCtxSelectedMessageKdf.step prior target nonce next (RawCtxChainSend.nativeRequest (reveal target slot))
  (.known reply.1, reply.2)

/-- The target-free private derivation: the hidden slot gets the programmed reply, a known chain its prior value. -/
noncomputable def taggedStep (prior : Prior) (nonce : NonceOutput) (next : RootOutput) : Chain → Chain × Material
  | .hidden => (.known (RawCtxFreshChainCut.concreteChain next), .hidden nonce)
  | .known chain =>
    let reply := RawCtxSelectedMessageKdf.known (prior (RawCtxSelectedPendingCut.requestAddress chain))
    (.known reply.1, reply.2)

/-- The logged value of a derivation input: the bytes of a known chain, nothing for the hidden slot. -/
def logged : Chain → Log
  | .hidden => []
  | .known chain => [RawCtxSelectedQueryTrace.rootVector chain]

/-- Away from a logged selected value, the concrete derivation is the target-free one; on the hidden slot they always agree. -/
theorem step_tagged (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (slot : Chain)
    (fresh : target ∉ logged slot) :
    concreteStep prior target nonce next slot = taggedStep prior nonce next slot := by
  cases slot with
  | hidden =>
    simp only [concreteStep, taggedStep, reveal, RawCtxSelectedChain.interpret, RawCtxSelectedMessageKdf.step]
    have same : RawCtxKdfRequestTable.address (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain target)) =
        RawCtxSelectedParentPrivatePatch.targetAddress target := rfl
    simp only [same, ite_true]
  | known chain =>
    have different : RawCtxSelectedPendingCut.requestAddress chain ≠ RawCtxSelectedParentPrivatePatch.targetAddress target := by
      intro same
      exact fresh (by simp only [logged, List.mem_singleton]; exact (RawCtxSelectedParentPrivatePatch.address_eq target chain).mp same)
    simp only [concreteStep, taggedStep, reveal, RawCtxSelectedChain.interpret, RawCtxSelectedMessageKdf.step]
    simp only [RawCtxSelectedPendingCut.requestAddress] at different
    simp only [different, ite_false]
    rfl

end Labels

section Services
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation
open RawCtxInterpretedOpening RawCtxMaterialInterpretation
variable {A : Type}

/-- The opening service of the functional source family does not read the private table. -/
theorem open_table (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (first second : Prior)
    (input : RawCtxWholeOwner.OpenInput) :
    (RawCtxFunctionalFamily.native (A := A) source writer first ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) =
      (RawCtxFunctionalFamily.native source writer second ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input) := by
  change simulateQ (RawCtxFunctionalFamily.native source writer first) (simulateQ RawCtxMixedOwner.receiveLift
      (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input))) =
    simulateQ (RawCtxFunctionalFamily.native source writer second) (simulateQ RawCtxMixedOwner.receiveLift
      (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input)))
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with query | query <;> rfl

/-- The sealing service of the functional source family does not read the private table. -/
theorem seal_table (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (first second : Prior)
    (input : RawCtxSourceSend.SealInput) :
    (RawCtxFunctionalFamily.native (A := A) source writer first ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) =
      (RawCtxFunctionalFamily.native source writer second ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input) := by
  change simulateQ (RawCtxFunctionalFamily.native source writer first) (simulateQ RawCtxMixedOwner.sendLift
      (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input))) =
    simulateQ (RawCtxFunctionalFamily.native source writer second) (simulateQ RawCtxMixedOwner.sendLift
      (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input)))
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with query | query | query <;> rfl

/-- The functional opening reads only the opening arguments, never the private table. -/
theorem opening_arguments (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (first second : Prior)
    (pending other : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (same : RawCtxWholeOwner.arguments pending = RawCtxWholeOwner.arguments other) :
    RawCtxFunctionalFamily.opening (A := A) source writer first pending = RawCtxFunctionalFamily.opening source writer second other := by
  simp only [RawCtxFunctionalFamily.opening, QueryImpl.compose, RawCtxWholeOwner.adapter, same]
  split
  · rfl
  · simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
    rw [open_table source writer first second]

/-- The functional sealing reads only the sealing arguments, never the private table. -/
theorem sealing_arguments (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (first second : Prior)
    (pending other : SendSeal RawCtxSourceSend.SealContext)
    (same : RawCtxSourceSend.arguments pending = RawCtxSourceSend.arguments other) :
    RawCtxFunctionalFamily.sealing (A := A) source writer first pending = RawCtxFunctionalFamily.sealing source writer second other := by
  simp only [RawCtxFunctionalFamily.sealing, QueryImpl.compose, RawCtxSourceSend.adapter]
  rw [same]
  simp only [simulateQ_bind, simulateQ_pure, simulateQ_spec_query]
  rw [seal_table source writer first second]

/-- Material interpretation and chain interpretation of a pending opening commute. -/
theorem opening_maps {Send Receive SendValue ReceiveValue Material Value Context : Type}
    (send : Send → SendValue) (receive : Receive → ReceiveValue) (interpret : Material → Value)
    (pending : Opening Send Receive Material Context) :
    mapOpening interpret (mapOpeningChains send receive pending) = mapOpeningChains send receive (mapOpening interpret pending) := by
  obtain ⟨entry, context, prepared⟩ := pending
  cases prepared <;> rfl

end Services

section Records
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation
open RawCtxInterpretedOpening RawCtxMaterialInterpretation RawCtxSelectedMessageDriver
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The chain-handle receive interface over tagged kernels. -/
abbrev ReceiveSpec := RawCtxChainReceive.ReceiveSpec Chain Chain Material RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted
/-- The chain-handle send interface over tagged kernels. -/
abbrev SendSpec := RawCtxChainSend.SendSpec Chain Chain Material RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted
/-- Every private and public primitive interface used by one record operation over tagged kernels. -/
abbrev LabelSpec := ReceiveSpec + (SendSpec + RawCtxServerServices.PublicSpec)

/-- Fills chain fields that opening and sealing never read. -/
def blank : Chain → RatchetChain := fun _ => RawCtxSelectedChain.unusedChain

/-- The stopped-source receive interface pulled back to tagged kernels: derivations use the concrete selected step on the slot bytes, openings the actual source opening. -/
noncomputable def concreteReceive (target : RootOutput) :
    QueryImpl ReceiveSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl slot => pure (concreteStep prior target nonce next slot)
  | .inr pending => receiveServices source writer prior none key target nonce next
      (.inr (mapOpeningChains (reveal target) (reveal target) pending))

/-- The stopped-source send interface pulled back to tagged kernels. -/
noncomputable def concreteSend (target : RootOutput) :
    QueryImpl SendSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl slot => pure (concreteStep prior target nonce next slot)
  | .inr pending => sendServices source writer prior none key target nonce next
      (.inr (RawCtxChainSend.nativeSeal (reveal target) (reveal target) pending))

/-- The public services of the stopped source. -/
noncomputable def publicServices (target : RootOutput) :
    QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp) :=
  RawCtxFunctionalFamily.backend source writer (privateTable prior none target (RawCtxSelectedMessageKdf.response key nonce next)) ∘ₛ
    RawCtxServerServices.publicLift

/-- All stopped-source primitive services of one record operation over tagged kernels. -/
noncomputable def concreteLabels (target : RootOutput) :
    QueryImpl LabelSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
  | .inl query => concreteReceive source writer prior key nonce next target query
  | .inr (.inl query) => concreteSend source writer prior key nonce next target query
  | .inr (.inr query) => publicServices source writer prior key nonce next target query

/-- The target-free opening: unread chain fields are blank and the private table is the prior table. -/
noncomputable def taggedOpening (pending : Opening Chain Chain Material RawCtxWholeOwner.OpenContext) :=
  RawCtxFunctionalFamily.opening (A := A) source writer prior
    (toNative (mapOpening (RawCtxSelectedMessageKey.interpret key) (mapOpeningChains blank blank pending)))

/-- The target-free sealing: unread chain fields are blank and the private table is the prior table. -/
noncomputable def taggedSealing (pending : RawCtxChainSend.Seal Chain Chain Material RawCtxSourceSend.SealContext) :=
  RawCtxFunctionalFamily.sealing (A := A) source writer prior
    (RawCtxInterpretedSend.nativeSeal (RawCtxInterpretedSend.mapSeal (RawCtxSelectedMessageKey.interpret key)
      (RawCtxChainSend.nativeSeal blank blank pending)))

/-- Run a shared-state service beside an unchanged log. -/
def keepLog {β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β) :
    StateT (RawCtxSharedPrimitive.SharedState A × Log) ProbComp β := fun state =>
  (fun reply => (reply.1, (reply.2, state.2))) <$> work.run state.1

/-- The target-free primitive services: the hidden slot gets the programmed reply, known chains their prior values and are logged. -/
noncomputable def taggedLabels : QueryImpl LabelSpec (StateT (RawCtxSharedPrimitive.SharedState A × Log) ProbComp)
  | .inl (.inl slot) => fun state => pure (taggedStep prior nonce next slot, (state.1, state.2 ++ logged slot))
  | .inl (.inr pending) => keepLog (taggedOpening source writer prior key pending)
  | .inr (.inl (.inl slot)) => fun state => pure (taggedStep prior nonce next slot, (state.1, state.2 ++ logged slot))
  | .inr (.inl (.inr pending)) => keepLog (taggedSealing source writer prior key pending)
  | .inr (.inr query) => keepLog ((RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift) query)

/-- The concrete opening of a tagged pending opening is the target-free opening. -/
theorem opening_tagged (target : RootOutput) (pending : Opening Chain Chain Material RawCtxWholeOwner.OpenContext) :
    concreteReceive (A := A) source writer prior key nonce next target (.inr pending) =
      taggedOpening source writer prior key pending := by
  apply opening_arguments
  rw [opening_maps, opening_maps]
  exact RawCtxChainOpeningArguments.arguments_chains _ _ _ _ _

/-- The concrete sealing of a tagged pending seal is the target-free sealing. -/
theorem sealing_tagged (target : RootOutput) (pending : RawCtxChainSend.Seal Chain Chain Material RawCtxSourceSend.SealContext) :
    concreteSend (A := A) source writer prior key nonce next target (.inr pending) =
      taggedSealing source writer prior key pending := by
  apply sealing_arguments
  rfl

/-- The concrete public services are the target-free public services. -/
theorem public_tagged (target : RootOutput) (query : RawCtxServerServices.PublicSpec.Domain) :
    publicServices (A := A) source writer prior key nonce next target query =
      (RawCtxFunctionalFamily.backend source writer prior ∘ₛ RawCtxServerServices.publicLift) query := by
  rcases query with query | query | query <;> rfl

end Records

section LabelCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The label-level relation: equal shared states. -/
def SameShared (first : RawCtxSharedPrimitive.SharedState A) (second : RawCtxSharedPrimitive.SharedState A × Log) : Prop :=
  first = second.1

/-- The label-level bad event: the selected value is in the log. -/
def Logged (target : RootOutput) (second : RawCtxSharedPrimitive.SharedState A × Log) : Prop := target ∈ second.2

/-- A shared-state service is coupled with itself run beside the log. -/
theorem keep_coupled {β : Type} (target : RootOutput) (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β)
    (state : RawCtxSharedPrimitive.SharedState A) (log : Log) :
    RelTriple (work.run state) ((keepLog work).run (state, log)) (UpTo SameShared (fun _ => False) (Logged target)) := by
  have mapped : RelTriple (id <$> work.run state) ((fun reply => (reply.1, (reply.2, log))) <$> work.run state)
      (UpTo SameShared (fun _ => False) (Logged target)) :=
    relTriple_map (relTriple_refl_of_mem_support _ fun _ _ => Or.inr (Or.inr ⟨rfl, rfl⟩))
  simp only [id_map] at mapped
  exact mapped

/-- One derivation: the concrete and target-free replies agree unless the selected value is logged. -/
theorem step_coupled (target : RootOutput) (slot : Chain) (state : RawCtxSharedPrimitive.SharedState A) (log : Log) :
    RelTriple (pure (concreteStep prior target nonce next slot, state) : ProbComp _)
      (pure (taggedStep prior nonce next slot, (state, log ++ logged slot)) : ProbComp _)
      (UpTo SameShared (fun _ => False) (Logged target)) := by
  apply relTriple_pure_pure
  by_cases fresh : target ∈ logged slot
  · exact Or.inr (Or.inl (List.mem_append_right log fresh))
  · exact Or.inr (Or.inr ⟨step_tagged prior target nonce next slot fresh, rfl⟩)

/-- One label query of the concrete and target-free services is coupled up to a logged selected value. -/
theorem label_step (target : RootOutput) (query : LabelSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A) (log : Log) :
    RelTriple ((concreteLabels source writer prior key nonce next target query).run state)
      ((taggedLabels source writer prior key nonce next query).run (state, log))
      (UpTo SameShared (fun _ => False) (Logged target)) := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  · exact step_coupled prior nonce next target slot state log
  · change RelTriple ((concreteReceive source writer prior key nonce next target (.inr pending)).run state) _ _
    rw [opening_tagged]
    exact keep_coupled target _ state log
  · exact step_coupled prior nonce next target slot state log
  · change RelTriple ((concreteSend source writer prior key nonce next target (.inr pending)).run state) _ _
    rw [sealing_tagged]
    exact keep_coupled target _ state log
  · change RelTriple ((publicServices source writer prior key nonce next target query).run state) _ _
    rw [public_tagged]
    exact keep_coupled target _ state log

/-- The target-free services never remove a logged value. -/
theorem labels_absorbing (target : RootOutput) (query : LabelSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A × Log)
    (bad : Logged target state)
    (result : LabelSpec.Range query × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support ((taggedLabels source writer prior key nonce next query).run state)) :
    Logged target result.2 := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  all_goals first
    | (simp only [taggedLabels, StateT.run, support_pure, Set.mem_singleton_iff] at supported
       subst supported
       exact List.mem_append_left _ bad)
    | (simp only [taggedLabels, keepLog, StateT.run, support_map, Set.mem_image] at supported
       obtain ⟨_, _, rfl⟩ := supported
       exact bad)

/-- Every program over the record primitive interface runs identically under the concrete and the target-free services, until the selected value is logged. -/
theorem labels_coupled {β : Type} (target : RootOutput) (work : OracleComp LabelSpec β)
    (state : RawCtxSharedPrimitive.SharedState A) (log : Log) :
    RelTriple ((simulateQ (concreteLabels source writer prior key nonce next target) work).run state)
      ((simulateQ (taggedLabels source writer prior key nonce next) work).run (state, log))
      (UpTo SameShared (fun _ => False) (Logged target)) :=
  coupled_run _ _ SameShared (fun _ => False) (Logged target) (fun _ _ impossible => impossible.elim)
    (labels_absorbing source writer prior key nonce next target)
    (fun query first second same _ _ => by
      obtain ⟨state, log⟩ := second
      change first = state at same
      subst same
      exact label_step source writer prior key nonce next target query first log)
    work state (state, log) (Or.inr (Or.inr rfl))

end LabelCoupling

section Frontend
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation
open RawCtxSelectedMessageDriver RawCtxGenericRoleFamily
variable {A M P I D K : Type} {S B : Nat} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- Receive handle queries as record primitive queries. -/
def receiveInject : QueryImpl ReceiveSpec (OracleComp LabelSpec) := fun query => LabelSpec.query (.inl query)
/-- Send handle queries as record primitive queries. -/
def sendInject : QueryImpl SendSpec (OracleComp LabelSpec) := fun query => LabelSpec.query (.inr (.inl query))
/-- Public queries as record primitive queries. -/
def publicInject : QueryImpl RawCtxServerServices.PublicSpec (OracleComp LabelSpec) :=
  fun query => LabelSpec.query (.inr (.inr query))

/-- The chain-handle receive and send programs over tagged kernels, as record primitive programs. -/
noncomputable def symbolicCalls : RawCtxChainOwner.Calls TKernel (OracleComp LabelSpec) :=
  ⟨fun kernel sequence context => simulateQ receiveInject (RawCtxChainReceive.execute kernel sequence context),
    fun kernel context => simulateQ sendInject (RawCtxChainSend.execute kernel context)⟩

/-- One role or public operation over tagged roles as a record primitive program. -/
noncomputable def symbolicStep (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : Roles TKernel M P I D K S B) :
    OracleComp LabelSpec ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles TKernel M P I D K S B) :=
  (RawCtxGenericFamilyFrontend.impl symbolicCalls publicInject sender route decode query).run roles

/-- The concrete services on injected receive queries are the concrete receive services. -/
theorem labels_receive {β : Type} (target : RootOutput) (work : OracleComp ReceiveSpec β) :
    simulateQ (concreteLabels (A := A) source writer prior key nonce next target) (simulateQ receiveInject work) =
      simulateQ (concreteReceive source writer prior key nonce next target) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, receiveInject, simulateQ_spec_query]
  rfl

/-- The concrete services on injected send queries are the concrete send services. -/
theorem labels_send {β : Type} (target : RootOutput) (work : OracleComp SendSpec β) :
    simulateQ (concreteLabels (A := A) source writer prior key nonce next target) (simulateQ sendInject work) =
      simulateQ (concreteSend source writer prior key nonce next target) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.compose, sendInject, simulateQ_spec_query]
  rfl

/-- The concrete services on injected public queries are the public services. -/
theorem labels_public (target : RootOutput) :
    (fun query => simulateQ (concreteLabels (A := A) source writer prior key nonce next target) (publicInject query)) =
      publicServices source writer prior key nonce next target := by
  funext query
  simp only [publicInject, simulateQ_spec_query]
  rfl

/-- The stopped-source receive on the represented kernel is the concrete chain-handle receive on the tagged kernel. -/
theorem receive_map (target : RootOutput) (kernel : TKernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (RawCtxSelectedMessageFamily.calls (receiveServices (A := A) source writer prior none key target nonce next)
      (sendServices source writer prior none key target nonce next) none target nonce next).receive
        (mapKernel target kernel) sequence context =
      Prod.map (mapKernel target) id <$>
        simulateQ (concreteReceive source writer prior key nonce next target) (RawCtxChainReceive.execute kernel sequence context) := by
  change simulateQ (receiveServices source writer prior none key target nonce next)
    (simulateQ (receiveCompiler none target nonce next) (RawCtxInterpretedReceive.receive (mapKernel target kernel) sequence context)) = _
  rw [← QueryImpl.simulateQ_compose]
  refine RawCtxChainReceive.execute_native (reveal target) (reveal target) _ _ (fun slot => ?_) (fun pending => ?_) kernel sequence context
  · simp only [QueryImpl.compose, receiveCompiler, ← QueryImpl.simulateQ_compose]
    change simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
      (derive none target nonce next _) = _
    rw [derive_evaluated]
    rfl
  · exact simulateQ_spec_query (receiveServices source writer prior none key target nonce next) _

/-- The stopped-source send on the represented kernel is the concrete chain-handle send on the tagged kernel. -/
theorem send_map (target : RootOutput) (kernel : TKernel) (context : RawCtxSourceSend.SealContext) :
    (RawCtxSelectedMessageFamily.calls (receiveServices (A := A) source writer prior none key target nonce next)
      (sendServices source writer prior none key target nonce next) none target nonce next).send
        (mapKernel target kernel) context =
      Prod.map (mapKernel target) id <$>
        simulateQ (concreteSend source writer prior key nonce next target) (RawCtxChainSend.execute kernel context) := by
  change simulateQ (sendServices source writer prior none key target nonce next)
    (simulateQ (sendCompiler none target nonce next) (RawCtxInterpretedSend.send (mapKernel target kernel) context)) = _
  rw [← QueryImpl.simulateQ_compose]
  refine RawCtxChainSend.execute_native (reveal target) (reveal target) _ _ (fun slot => ?_) (fun pending => ?_) kernel context
  · simp only [QueryImpl.compose, sendCompiler, ← QueryImpl.simulateQ_compose]
    change simulateQ (fun address => (pure (prior address) : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp FullOutput))
      (derive none target nonce next _) = _
    rw [derive_evaluated]
    rfl
  · exact simulateQ_spec_query (sendServices source writer prior none key target nonce next) _

/-- Every stopped-source role or public operation on represented tagged roles is the concrete interpretation of the symbolic tagged step. -/
theorem record_symbolic (target : RootOutput) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : Roles TKernel M P I D K S B) :
    (RawCtxGenericFamilyFrontend.impl (RawCtxSelectedMessageFamily.calls (receiveServices (A := A) source writer prior none key target nonce next)
      (sendServices source writer prior none key target nonce next) none target nonce next)
      (publicServices source writer prior key nonce next target) sender route decode query).run (mapRoles (mapKernel target) roles) =
      Prod.map id (mapRoles (mapKernel target)) <$>
        simulateQ (concreteLabels source writer prior key nonce next target) (symbolicStep sender route decode query roles) := by
  rw [symbolicStep, RawCtxGenericFamilyInterpretation.step_interpretation, labels_public]
  refine RawCtxGenericFamilyFrontend.step_map (mapKernel target) _ _ _ (fun kernel sequence context => ?_)
    (fun kernel context => ?_) sender route decode query roles
  · change _ = Prod.map (mapKernel target) id <$> simulateQ (concreteLabels source writer prior key nonce next target)
      (simulateQ receiveInject (RawCtxChainReceive.execute kernel sequence context))
    rw [labels_receive, receive_map]
  · change _ = Prod.map (mapKernel target) id <$> simulateQ (concreteLabels source writer prior key nonce next target)
      (simulateQ sendInject (RawCtxChainSend.execute kernel context))
    rw [labels_send, send_map]

end Frontend

section Keeps
open PqxdhJointKdfGame RawCtxSelectedParentTable
variable {ι : Type} {spec : OracleSpec ι} {A β : Type}

/-- A shared-state computation keeps the auxiliary component and otherwise behaves as the same computation over a unit auxiliary component. -/
def Keeps (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β)
    (unit : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp β) : Prop :=
  ∀ auxiliary cache, work.run (auxiliary, cache) = (fun result => (result.1, (auxiliary, result.2.2))) <$> unit.run ((), cache)

/-- Keeping the auxiliary component is preserved by simulation. -/
theorem simulate_keeps (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (unitImpl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (keeps : ∀ query, Keeps (impl query) (unitImpl query)) (work : OracleComp spec β) :
    Keeps (simulateQ impl work) (simulateQ unitImpl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => intro auxiliary cache; simp
  | query_bind query continuation ih =>
    intro auxiliary cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, keeps query auxiliary cache, bind_map_left, map_bind]
    refine bind_congr fun result => ?_
    rw [ih result.1 auxiliary result.2.2]

/-- Keeping the auxiliary component is preserved by composition with a lifting. -/
theorem compose_keeps {κ : Type} {source : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (unitImpl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (keeps : ∀ query, Keeps (impl query) (unitImpl query)) (lift : QueryImpl source (OracleComp spec)) (query : source.Domain) :
    Keeps ((impl ∘ₛ lift) query) ((unitImpl ∘ₛ lift) query) :=
  simulate_keeps impl unitImpl keeps (lift query)

/-- The shared primitive services keep the auxiliary component. -/
theorem native_keeps (c : Pqxdh.Crypto) (fixed : FixedHkdfSha512NoSaltSource) (query : RawCtxSourceOpen.NativeSpec.Domain) :
    Keeps (RawCtxSharedPrimitive.nativeImpl (Auxiliary := A) c (RawCtxSourceHkdf.kdfImpl fixed) query)
      (RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl fixed) query) := by
  intro auxiliary cache
  rcases query with request | (bytes | input)
  · simp only [StateT.run]
    simp [RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl]
  · simp only [RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, StateT.run, map_bind, map_pure]
  · simp only [StateT.run]
    simp only [RawCtxSharedPrimitive.nativeImpl]
    simp only [StateT.run]
    simp [RawCtxSharedPrimitive.openingImpl]

/-- The protocol backend keeps the auxiliary component. -/
theorem backend_keeps (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxServerServices.BackendSpec.Domain) :
    Keeps (RawCtxProtocolBackend.backend (Auxiliary := A) fixed writer query) (RawCtxProtocolBackend.backend fixed writer query) := by
  intro auxiliary cache
  rcases query with coin | (request | view)
  · simp only [RawCtxProtocolBackend.backend, StateT.run]
    simp [RawCtxServerServices.backendImpl]
  · exact compose_keeps _ _ (native_keeps fixed.crypto fixed) _ request auxiliary cache
  · simp only [RawCtxProtocolBackend.backend, StateT.run]
    simp [RawCtxServerServices.backendImpl]

/-- The functional source family keeps the auxiliary component. -/
theorem family_keeps (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (table : Prior)
    (query : RawCtxServerServices.BackendSpec.Domain) :
    Keeps (RawCtxFunctionalFamily.backend (A := A) fixed writer table query)
      (RawCtxFunctionalFamily.backend (A := Unit) fixed writer table query) := by
  refine compose_keeps _ _ (fun request => ?_) _ query
  rcases request with request | request
  · exact backend_keeps fixed writer request
  · intro auxiliary cache
    simp [RawCtxRetainedTable.viewImpl]

end Keeps

section LabelKeeps
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxSelectedMessageDriver
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- A pure shared-state reply keeps the auxiliary component. -/
theorem pure_keeps {β : Type} (value : β) :
    Keeps (A := A) (pure value : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β) (pure value) := by
  intro auxiliary cache
  simp

/-- The native functional family keeps the auxiliary component. -/
theorem native_family_keeps (table : Prior) (query : RawCtxMixedOwner.NativeSpec.Domain) :
    Keeps (RawCtxFunctionalFamily.native (A := A) source writer table query)
      (RawCtxFunctionalFamily.native (A := Unit) source writer table query) :=
  compose_keeps _ _ (family_keeps source writer table) _ query

/-- The concrete record services keep the auxiliary component. -/
theorem labels_keeps (target : RootOutput) (query : LabelSpec.Domain) :
    Keeps (concreteLabels (A := A) source writer prior key nonce next target query)
      (concreteLabels (A := Unit) source writer prior key nonce next target query) := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  · exact pure_keeps _
  · exact compose_keeps _ _ (compose_keeps _ _ (native_family_keeps source writer _) _) _ _
  · exact pure_keeps _
  · exact compose_keeps _ _ (compose_keeps _ _ (native_family_keeps source writer _) _) _ _
  · exact compose_keeps _ _ (family_keeps source writer _) _ _

/-- Every record primitive program keeps the auxiliary component under the concrete services. -/
theorem program_keeps {β : Type} (target : RootOutput) (work : OracleComp LabelSpec β) :
    Keeps (simulateQ (concreteLabels (A := A) source writer prior key nonce next target) work)
      (simulateQ (concreteLabels (A := Unit) source writer prior key nonce next target) work) :=
  simulate_keeps _ _ (labels_keeps source writer prior key nonce next target) work

end LabelKeeps

section Seals
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {M P I D K : Type} {S B : Nat}

/-- The tagged send chain of a send attempt that requests a derivation, and nothing for an exhausted attempt. -/
noncomputable def sendChains (kernel : TKernel) (context : RawCtxSourceSend.SealContext) : List Chain :=
  match RawCtxChainSend.normalBegin kernel context with
  | .exhausted _ _ => []
  | .requested _ => [kernel.send_chain]

/-- The tagged send chains of one owner request. -/
noncomputable def ownerSeals {Metadata : Type} (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : RawCtxChainOwner.State TKernel Metadata) : List Chain :=
  match query with
  | .inr _ => []
  | .inl plaintext => if plaintext.isEmpty then [] else
      sendChains entry.kernel ⟨plaintext, entry.expectedSender, sender, entry.associatedData⟩

/-- The tagged send chains of one Beacon request. -/
noncomputable def beaconSeals (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : BeaconState TKernel I D K) : List Chain :=
  match entry.beacon.phase with
  | .established control ad kernel => ownerSeals entry.beacon.identityKeyId query (RawCtxGenericBeacon.selected entry control ad kernel)
  | _ => []

/-- The tagged send chains of one Server request. -/
noncomputable def serverSeals (sender : M → Std.U64) (query : RawCtxServerMixed.SourceSpec.Domain)
    (entry : ServerState TKernel M P) : List Chain :=
  match query with
  | .inr _ => []
  | .inl (plaintext, kid) => match RawCtxGenericServer.peerAssociatedData entry.server kid with
    | none => []
    | some ad => match entry.server.peers kid with
      | none => []
      | some peer => ownerSeals (sender entry.server.metadata) (.inl plaintext)
          (RawCtxGenericServer.selectedOwner kid ad peer entry.rawAttempts)

/-- The tagged send chains of one role or public request. -/
noncomputable def familySeals (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : Roles TKernel M P I D K S B) : List Chain :=
  match query with
  | .inl ⟨index, request⟩ => serverSeals sender request (roles.1 index)
  | .inr (.inl ⟨index, request⟩) => beaconSeals request (roles.2 index)
  | .inr (.inr _) => []

/-- The send chains of the source seal events of one send attempt are the represented tagged send chains. -/
theorem send_seals {Owner : Type} (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (kernel : TKernel) (context : RawCtxSourceSend.SealContext) :
    (RawCtxSourceEventRecorder.seals (RawCtxSelectedSendEvents.events prior none target nonce next owner
      (mapKernel target kernel) context)).map (fun occurrence => occurrence.entry.send_chain) =
      (sendChains kernel context).map (reveal target) := by
  unfold RawCtxSelectedSendEvents.events sendChains
  rw [mapKernel, RawCtxChainSend.normalBegin_native]
  cases RawCtxChainSend.normalBegin kernel context <;> rfl

end Seals

section FamilySeals
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {M P I D K : Type} {S B : Nat}

/-- The source seal events of one owner request carry the represented tagged send chains. -/
theorem owner_seals {Owner Metadata : Type} (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Owner) (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : RawCtxChainOwner.State TKernel Metadata) :
    (RawCtxSourceEventRecorder.seals (RawCtxSelectedRoleAuditLedger.ownerEvents prior none target nonce next label sender query
      ⟨mapKernel target entry.kernel, entry.expectedSender, entry.associatedData, entry.metadata, entry.rawAttempts⟩)).map
      (fun occurrence => occurrence.entry.send_chain) = (ownerSeals sender query entry).map (reveal target) := by
  cases query with
  | inr raw => rfl
  | inl plaintext =>
    simp only [RawCtxSelectedRoleAuditLedger.ownerEvents, ownerSeals]
    split
    · rfl
    · exact send_seals prior target nonce next label entry.kernel _

/-- The source seal events of one Beacon request carry the represented tagged send chains. -/
theorem beacon_seals {Owner : Type} (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Owner) (query : RawCtxMixedOwner.SourceSpec.Domain) (entry : BeaconState TKernel I D K) :
    (RawCtxSourceEventRecorder.seals (RawCtxSelectedRoleAuditLedger.beaconEvents prior none target nonce next label query
      (mapBeacon (mapKernel target) entry))).map (fun occurrence => occurrence.entry.send_chain) =
      (beaconSeals query entry).map (reveal target) := by
  unfold RawCtxSelectedRoleAuditLedger.beaconEvents beaconSeals
  cases phase : entry.beacon.phase with
  | established control ad kernel =>
    simp only [mapBeacon, phase, mapPhase]
    exact owner_seals prior target nonce next label entry.beacon.identityKeyId query
      (RawCtxGenericBeacon.selected entry control ad kernel)
  | fresh _ _ _ | freshWithCoins _ _ _ _ | initSent _ _ _ _ | aborted _ =>
    simp only [mapBeacon, phase, mapPhase]
    rfl

/-- The source seal events of one Server request carry the represented tagged send chains. -/
theorem server_seals {Owner : Type} (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (label : Std.U64 → Owner) (sender : M → Std.U64) (query : RawCtxServerMixed.SourceSpec.Domain) (entry : ServerState TKernel M P) :
    (RawCtxSourceEventRecorder.seals (RawCtxSelectedRoleAuditLedger.serverEvents prior none target nonce next label sender query
      (mapServer (mapKernel target) entry))).map (fun occurrence => occurrence.entry.send_chain) =
      (serverSeals sender query entry).map (reveal target) := by
  cases query with
  | inr raw => rfl
  | inl request =>
    obtain ⟨plaintext, kid⟩ := request
    simp only [RawCtxSelectedRoleAuditLedger.serverEvents, serverSeals, RawCtxGenericServer.peerAssociatedData, mapServer]
    cases found : entry.server.peers kid with
    | none => simp; rfl
    | some peer =>
      simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
      exact owner_seals prior target nonce next (label kid) (sender entry.server.metadata) (.inl plaintext)
        (RawCtxGenericServer.selectedOwner kid _ peer entry.rawAttempts)

/-- The source seal events of one role or public request carry the represented tagged send chains. -/
theorem family_seals (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (roles : Roles TKernel M P I D K S B) :
    (RawCtxSourceEventRecorder.seals (RawCtxSelectedRoleAuditLedger.familyEvents prior none target nonce next sender query
      (mapRoles (mapKernel target) roles))).map (fun occurrence => occurrence.entry.send_chain) =
      (familySeals sender query roles).map (reveal target) := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · exact server_seals prior target nonce next _ sender request (roles.1 index)
  · exact beacon_seals prior target nonce next _ request (roles.2 index)
  · rfl

end FamilySeals

section Near
open OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
variable {ι : Type} {spec : OracleSpec ι} {A N C β : Type}

/-- A computation over a shared state and a log keeps the auxiliary component and otherwise behaves as the same computation over a unit auxiliary component. -/
def KeepsLog (work : StateT (RawCtxSharedPrimitive.SharedState A × Log) ProbComp β)
    (unit : StateT (RawCtxSharedPrimitive.SharedState Unit × Log) ProbComp β) : Prop :=
  ∀ auxiliary cache log, work.run ((auxiliary, cache), log) =
    (fun result => (result.1, ((auxiliary, result.2.1.2), result.2.2))) <$> unit.run (((), cache), log)

/-- Keeping the auxiliary component beside a log is preserved by simulation. -/
theorem simulate_keeps_log (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState A × Log) ProbComp))
    (unitImpl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit × Log) ProbComp))
    (keeps : ∀ query, KeepsLog (impl query) (unitImpl query)) (work : OracleComp spec β) :
    KeepsLog (simulateQ impl work) (simulateQ unitImpl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => intro auxiliary cache log; simp
  | query_bind query continuation ih =>
    intro auxiliary cache log
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, keeps query auxiliary cache log, bind_map_left, map_bind]
    refine bind_congr fun result => ?_
    rw [ih result.1 auxiliary result.2.1.2 result.2.2]

/-- A kept shared-state service run beside the log keeps the auxiliary component. -/
theorem keep_log_keeps (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β)
    (unit : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp β) (keeps : Keeps work unit) :
    KeepsLog (keepLog work) (keepLog unit) := by
  intro auxiliary cache log
  change (fun reply => (reply.1, (reply.2, log))) <$> work.run (auxiliary, cache) =
    _ <$> ((fun reply => (reply.1, (reply.2, log))) <$> unit.run ((), cache))
  rw [keeps auxiliary cache]
  simp only [Functor.map_map]

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The target-free record services keep the auxiliary component. -/
theorem tagged_keeps (query : LabelSpec.Domain) :
    KeepsLog (taggedLabels (A := A) source writer prior key nonce next query) (taggedLabels (A := Unit) source writer prior key nonce next query) := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  · intro auxiliary cache log
    change (pure _ : ProbComp _) = _ <$> (pure _ : ProbComp _)
    simp
  · exact keep_log_keeps _ _ (compose_keeps _ _ (compose_keeps _ _ (native_family_keeps source writer _) _) _ _)
  · intro auxiliary cache log
    change (pure _ : ProbComp _) = _ <$> (pure _ : ProbComp _)
    simp
  · exact keep_log_keeps _ _ (compose_keeps _ _ (compose_keeps _ _ (native_family_keeps source writer _) _) _ _)
  · exact keep_log_keeps _ _ (compose_keeps _ _ (family_keeps source writer _) _ _)

/-- Removing the private audit of the source-local state. -/
def strip (state : Local A N C) : Local A N C := { state with audit := [] }

/-- The concrete shared state and the target-free shared state with its log agree except for the private audit. -/
def Near (first : RawCtxSharedPrimitive.SharedState (Local A N C)) (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) :
    Prop :=
  strip first.1 = strip second.1.1 ∧ first.2 = second.1.2

/-- Every record primitive program runs identically under the concrete and the target-free services from states that agree except for the private audit, until the selected value is logged. -/
theorem labels_near {γ : Type} (target : RootOutput) (work : OracleComp LabelSpec γ)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C)) (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log)
    (near : Near first second) :
    RelTriple ((simulateQ (concreteLabels source writer prior key nonce next target) work).run first)
      ((simulateQ (taggedLabels source writer prior key nonce next) work).run second)
      (UpTo Near (fun _ => False) (Logged target)) := by
  obtain ⟨firstLocal, cache⟩ := first
  obtain ⟨⟨secondLocal, secondCache⟩, log⟩ := second
  obtain ⟨stripped, sameCache⟩ := near
  simp only at stripped sameCache
  subst sameCache
  rw [program_keeps source writer prior key nonce next target work firstLocal cache,
    simulate_keeps_log _ _ (tagged_keeps source writer prior key nonce next) work secondLocal cache log]
  refine relTriple_map (relTriple_post_mono (labels_coupled source writer prior key nonce next target work ((), cache) log) ?_)
  intro left right held
  rcases held with impossible | bad | ⟨equal, same⟩
  · exact impossible.elim
  · exact Or.inr (Or.inl bad)
  · have cacheSame : left.2.2 = right.2.1.2 := congrArg Prod.snd (show left.2 = right.2.1 from same)
    exact Or.inr (Or.inr ⟨equal, stripped, cacheSame⟩)

end Near

section World
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The tagged front: tagged roles with the original registration controls and consumed identifiers. -/
structure TFront (M P I D K : Type) (S B : Nat) where
  roles : Roles TKernel M P I D K S B
  controls : Fin S → pqxdh.ServerState
  consumed : Fin S → List Pqxdh.Bytes

/-- The target-free world state: the tagged send chains of all seal events, the tagged front, and the source-local state, cache and derivation log. -/
structure TState (M P I D K A N C : Type) (S B : Nat) where
  seals : List Chain
  front : TFront M P I D K S B
  shared : RawCtxSharedPrimitive.SharedState (Local A N C) × Log

/-- A tagged chain reveal: known bytes are returned; the hidden slot, whose concrete reveal discloses the selected chain, returns a fixed chain. -/
def chainReply (kernel : Option TKernel) (pick : TKernel → Chain) : core.option.Option RatchetChain :=
  match kernel with
  | none => .None
  | some entry => match pick entry with
    | .known chain => .Some chain
    | .hidden => .Some RawCtxSelectedChain.unusedChain

/-- The skipped message-key lookup of a tagged kernel. -/
noncomputable def taggedSkipped (entry : TKernel) (sequence : Std.U64) : core.option.Option Material :=
  (refined.refined_receive_key_total entry sequence).choose

/-- The emitted reply of a reveal on tagged roles. -/
noncomputable def taggedEmit (request : RawCtxProtocolReveals.Request S B) (roles : Roles TKernel M P I D K S B) :
    Option ((RawCtxProtocolReveals.RevealSpec S B).Range request) :=
  match request with
  | .sendChain owner => some (chainReply (selectedKernel owner roles) (fun entry => entry.send_chain))
  | .receiveChain owner => some (chainReply (selectedKernel owner roles) (fun entry => entry.receive_chain))
  | .skippedKey owner sequence => RawCtxSelectedMessageReveals.emit (.skippedKey owner sequence)
      (match selectedKernel owner roles with
      | none => .None
      | some entry => taggedSkipped entry sequence)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

/-- A tagged role or public request: the symbolic step under the target-free services, with its tagged seal chains recorded. -/
noncomputable def taggedRecord (request : (RawCtxProtocolRoles.SourceSpec S B).Domain) :
    StateT (TState M P I D K A N C S B) ProbComp (Option ((RawCtxProtocolRoles.SourceSpec S B).Range request)) := fun state =>
  (fun result => (some result.1.1, ⟨state.seals ++ familySeals sender request state.front.roles,
      { state.front with roles := result.1.2 }, result.2⟩)) <$>
    (simulateQ (taggedLabels source writer prior key nonce next) (symbolicStep sender route decode request state.front.roles)).run
      state.shared

variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- A selector request on the source-local state, with the log and front unchanged. -/
noncomputable def taggedSelector (request : extra.Domain) :
    StateT (TState M P I D K A N C S B) ProbComp (Option (extra.Range request)) := fun state =>
  (fun result => (some result.1, { state with shared := (result.2, state.shared.2) })) <$>
    (PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initial selector aux
      (.inr (.inr (.inr (.inl request))))).run state.shared.1

/-- The target-free world: records under the target-free services, reveals on tagged roles, source-local selectors and a supplied finish operation. -/
noncomputable def world
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes))) :
    QueryImpl (Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (TState M P I D K A N C S B) ProbComp)
  | .inl (.inl (.inl request)) => taggedRecord source writer prior key nonce next sender route decode request
  | .inl (.inl (.inr request)) => fun state => pure (taggedEmit request state.front.roles, state)
  | .inl (.inr request) => taggedSelector pre application initial selector aux request
  | .inr (.finish index raw) => finishOp index raw

end World

section Relation
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The concrete source-post state of the history-extended source post. -/
abbrev Concrete (M P I D K A N C : Type) (S B : Nat) :=
  PqxdhFirstRecordNonceStop.History S B × PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B

/-- A concrete state is represented by a tagged state: represented roles, equal controls and consumed identifiers, source-local state equal up to the private audit, equal cache, and seal chains represented by the tagged seal chains. -/
def Represents (target : RootOutput) (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) : Prop :=
  first.2.1.roles.1 = mapRoles (mapKernel target) second.front.roles ∧
    first.2.1.controls = second.front.controls ∧ first.2.1.consumed = second.front.consumed ∧
    Near first.2.2 second.shared ∧
    (RawCtxSourceEventRecorder.seals first.1).map (fun occurrence => occurrence.entry.send_chain) =
      second.seals.map (reveal target)

/-- The selected chain has been disclosed by a concrete reveal. -/
def Disclosed (target : RootOutput) (first : Concrete M P I D K A N C S B) : Prop :=
  RawCtxFreshChainCut.concreteChain target ∈ RawCtxSelectedMessageFreshness.known [] first.2.1.roles.2

/-- The selected value is in the derivation log of the tagged world. -/
def Exposed (target : RootOutput) (second : TState M P I D K A N C S B) : Prop := target ∈ second.shared.2

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The concrete role or public request of the history-extended source post, unfolded to the original frontend. -/
theorem record_source (target : RootOutput) (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (first : Concrete M P I D K A N C S B) :
    ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
      target nonce next sender route decode) (.inl (.inl (.inl request)))).run first =
      (fun result => (some result.1.1, (first.1 ++ RawCtxSelectedRoleAuditLedger.familyEvents prior none target nonce next sender
          request first.2.1.roles.1,
        ({ first.2.1 with roles := (result.1.2, RawCtxSelectedMessageFamily.tick first.2.1.roles.2) }, result.2)))) <$>
        ((RawCtxGenericFamilyFrontend.impl (RawCtxSelectedMessageFamily.calls
          (receiveServices (A := Local A N C) source writer prior none key target nonce next)
          (sendServices source writer prior none key target nonce next) none target nonce next)
          (publicServices source writer prior key nonce next target) sender route decode request).run first.2.1.roles.1).run first.2.2 := by
  simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhFirstRecordNonceStop.sourceEvents,
    RawCtxSelectedLiveAuditLedger.events, PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
    RawCtxSelectedMessageStopping.stopping, RawCtxSelectedMessageStopping.sourceRecord, StateT.run, OptionT.run_mk,
    QueryImpl.flattenStateT, StateT.mk, Functor.map_map]
  rfl

end Relation

section RecordStep
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (taggedInitial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))

/-- Seal extraction distributes over appended histories. -/
theorem seals_append {Owner : Type} (first second : List (RawCtxSelectedDriverAudit.Event Owner)) :
    RawCtxSourceEventRecorder.seals (first ++ second) = RawCtxSourceEventRecorder.seals first ++ RawCtxSourceEventRecorder.seals second := by
  simp [RawCtxSourceEventRecorder.seals, List.filterMap_append]

/-- A role or public request of the concrete source post and of the tagged world are coupled up to a logged selected value. -/
theorem record_step (target : RootOutput) (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) (represents : Represents target first second) :
    RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
      target nonce next sender route decode) (.inl (.inl (.inl request)))).run first)
      ((world source writer prior key nonce next sender route decode pre application taggedInitial selector aux finishOp
        (.inl (.inl (.inl request)))).run second)
      (UpTo (Represents target) (Disclosed target) (Exposed target)) := by
  rw [record_source]
  obtain ⟨roles, controls, consumed, near, seals⟩ := represents
  rw [roles, record_symbolic, StateT.run_map, Functor.map_map]
  change RelTriple _ ((fun result => (some result.1.1, (⟨second.seals ++ familySeals sender request second.front.roles,
      { second.front with roles := result.1.2 }, result.2⟩ : TState M P I D K A N C S B))) <$>
    (simulateQ (taggedLabels source writer prior key nonce next) (symbolicStep sender route decode request second.front.roles)).run
      second.shared) _
  refine relTriple_map (relTriple_post_mono (labels_near source writer prior key nonce next target _ first.2.2 second.shared near) ?_)
  intro left right held
  rcases held with impossible | bad | ⟨equal, closer⟩
  · exact impossible.elim
  · exact Or.inr (Or.inl bad)
  · refine Or.inr (Or.inr ⟨by simp only [Prod.map_fst, equal, id_eq], ?_, controls, consumed, closer, ?_⟩)
    · simp only [Prod.map_snd, equal]
    · simp only [seals_append, List.map_append, seals, family_seals]

end RecordStep

section RevealStep
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (taggedInitial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))

/-- Selecting an owner's kernel commutes with a kernel map of the whole family. -/
theorem selected_map {Kernel Other : Type} (interpret : Kernel → Other) (owner : RawCtxProtocolReveals.Owner S B)
    (roles : Roles Kernel M P I D K S B) :
    selectedKernel owner (mapRoles interpret roles) = (selectedKernel owner roles).map interpret := by
  cases owner with
  | server index peer =>
    simp only [selectedKernel, mapRoles, mapServer, Option.map_map]
    rfl
  | beacon index =>
    simp only [selectedKernel, mapRoles, mapBeacon]
    cases (roles.2 index).beacon.phase <;> rfl

/-- The skipped-key lookup of a represented kernel is the tagged lookup. -/
theorem skipped_tagged (target : RootOutput) (entry : TKernel) (sequence : Std.U64) :
    RawCtxSelectedMessageReveals.skipped (mapKernel target entry) sequence = taggedSkipped entry sequence := by
  apply RustM.ok.inj
  rw [← RawCtxSelectedMessageReveals.skipped_exact]
  exact (refined.refined_receive_key_total entry sequence).choose_spec

/-- A concrete reveal of the history-extended source post returns the emitted reply and appends the observation. -/
theorem reveal_source (target : RootOutput) (request : RawCtxProtocolReveals.Request S B) (first : Concrete M P I D K A N C S B) :
    ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
      target nonce next sender route decode) (.inl (.inl (.inr request)))).run first =
      pure (RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request first.2.1.roles).1,
        (first.1 ++ [], ({ first.2.1 with roles := (RawCtxSelectedMessageReveals.step request first.2.1.roles).2 }, first.2.2))) := by
  simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhFirstRecordNonceStop.sourceEvents,
    RawCtxSelectedLiveAuditLedger.events, PqxdhSelectedPostCompiler.original, RawCtxSelectedFamilyNonceCoupling.original,
    RawCtxSelectedMessageStopping.stopping, StateT.run, OptionT.run_mk, map_pure]

/-- An observation whose reply carries a chain puts that chain among the known chains. -/
theorem known_note (history : RawCtxSelectedMessageFreshness.History S B) (observation : RawCtxSelectedMessageFreshness.Observation S B)
    (chain : RatchetChain) (listed : chain ∈ RawCtxSelectedMessageFreshness.candidates observation) :
    chain ∈ RawCtxSelectedMessageFreshness.known [] (RawCtxSelectedMessageFreshness.note observation history) := by
  simp only [RawCtxSelectedMessageFreshness.known, RawCtxSelectedMessageFreshness.note, List.nil_append, List.flatMap_append,
    List.mem_append, List.flatMap_singleton]
  exact Or.inr listed

/-- A reveal of the concrete source post and of the tagged world are coupled: equal replies unless the concrete reveal discloses the selected chain. -/
theorem reveal_step (target : RootOutput) (request : RawCtxProtocolReveals.Request S B)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) (represents : Represents target first second) :
    RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
      target nonce next sender route decode) (.inl (.inl (.inr request)))).run first)
      ((world source writer prior key nonce next sender route decode pre application taggedInitial selector aux finishOp
        (.inl (.inl (.inr request)))).run second)
      (UpTo (Represents target) (Disclosed target) (Exposed target)) := by
  rw [reveal_source]
  obtain ⟨roles, controls, consumed, near, seals⟩ := represents
  apply relTriple_pure_pure
  have kept : Represents target (first.1 ++ [], ({ first.2.1 with roles := (RawCtxSelectedMessageReveals.step request first.2.1.roles).2 },
      first.2.2)) second := ⟨roles, controls, consumed, near, by simpa only [List.append_nil] using seals⟩
  cases request with
  | sendChain owner =>
    cases found : selectedKernel owner second.front.roles with
    | none =>
      refine Or.inr (Or.inr ⟨?_, kept⟩)
      simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
        roles, selected_map, found, RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageReveals.emit, taggedEmit, chainReply]
    | some entry =>
      cases chain : entry.send_chain with
      | hidden =>
        refine Or.inl (known_note _ _ _ ?_)
        simp [RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner, roles, selected_map, found,
          RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageFreshness.candidates, mapKernel, mapChains, chain, reveal,
          RawCtxSelectedChain.interpret]
      | known value =>
        refine Or.inr (Or.inr ⟨?_, kept⟩)
        simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
          roles, selected_map, found, RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageReveals.emit, taggedEmit,
          chainReply, mapKernel, mapChains, chain, reveal, RawCtxSelectedChain.interpret]
  | receiveChain owner =>
    cases found : selectedKernel owner second.front.roles with
    | none =>
      refine Or.inr (Or.inr ⟨?_, kept⟩)
      simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
        roles, selected_map, found, RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageReveals.emit, taggedEmit, chainReply]
    | some entry =>
      cases chain : entry.receive_chain with
      | hidden =>
        refine Or.inl (known_note _ _ _ ?_)
        simp [RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner, roles, selected_map, found,
          RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageFreshness.candidates, mapKernel, mapChains, chain, reveal,
          RawCtxSelectedChain.interpret]
      | known value =>
        refine Or.inr (Or.inr ⟨?_, kept⟩)
        simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
          roles, selected_map, found, RawCtxSelectedMessageReveals.reply, RawCtxSelectedMessageReveals.emit, taggedEmit,
          chainReply, mapKernel, mapChains, chain, reveal, RawCtxSelectedChain.interpret]
  | skippedKey owner sequence =>
    refine Or.inr (Or.inr ⟨?_, kept⟩)
    cases found : selectedKernel owner second.front.roles with
    | none =>
      simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
        roles, selected_map, found, RawCtxSelectedMessageReveals.reply, taggedEmit]
    | some entry =>
      simp [RawCtxSelectedMessageReveals.step, RawCtxSelectedMessageReveals.selectedReply, RawCtxGenericFamilyRead.requestOwner,
        roles, selected_map, found, RawCtxSelectedMessageReveals.reply, taggedEmit, skipped_tagged]

end RevealStep

section SelectorStep
open OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Restore the private audit of a source-local result. -/
def restore {β : Type} (state : Local A N C) (result : β × RawCtxSharedPrimitive.SharedState (Local A N C)) :
    β × RawCtxSharedPrimitive.SharedState (Local A N C) :=
  (result.1, ({ result.2.1 with audit := state.audit }, result.2.2))

/-- A source-local callback keeps the private audit and does not read it. -/
theorem local_restore {β : Type} (work : LocalCallback A N C β) (state : Local A N C) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall work)).run (state, cache) =
      restore state <$> (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall work)).run (strip state, cache) := by
  change PqxdhSelectedStateInterpreter.pair <$> (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((fun result => (result.1, afterExternal state result.2)) <$>
        simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState state)))).run cache =
    restore state <$> (PqxdhSelectedStateInterpreter.pair <$> (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((fun result => (result.1, afterExternal (strip state) result.2)) <$>
        simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState (strip state))))).run cache)
  rw [simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map]
  simp only [Functor.map_map]
  rfl

/-- Two source-local states equal up to the private audit give coupled callback runs with equal replies and states equal up to the audit. -/
theorem local_coupled {β : Type} (work : LocalCallback A N C β)
    (first second : RawCtxSharedPrimitive.SharedState (Local A N C)) (stripped : strip first.1 = strip second.1)
    (cached : first.2 = second.2) :
    RelTriple ((PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall work)).run first)
      ((PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall work)).run second)
      (fun left right => left.1 = right.1 ∧ strip left.2.1 = strip right.2.1 ∧ left.2.2 = right.2.2) := by
  obtain ⟨firstLocal, cache⟩ := first
  obtain ⟨secondLocal, secondCache⟩ := second
  simp only at stripped cached
  subst cached
  rw [local_restore work firstLocal, local_restore work secondLocal, stripped]
  exact relTriple_map (relTriple_refl_of_mem_support _ fun _ _ => ⟨rfl, rfl, rfl⟩)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (taggedInitial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))

/-- A selector request of the concrete source post and of the tagged world are coupled with equal replies. -/
theorem selector_step (target : RootOutput) (request : extra.Domain)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B) (represents : Represents target first second) :
    RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior none key
      target nonce next sender route decode) (.inl (.inr request))).run first)
      ((world source writer prior key nonce next sender route decode pre application taggedInitial selector aux finishOp
        (.inl (.inr request))).run second)
      (UpTo (Represents target) (Disclosed target) (Exposed target)) := by
  obtain ⟨roles, controls, consumed, ⟨stripped, cached⟩, seals⟩ := represents
  simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhFirstRecordNonceStop.sourceEvents, PqxdhSelectedPostCompiler.original,
    StateT.run, Functor.map_map, List.append_nil]
  change RelTriple _ ((fun result => (some result.1, { second with shared := (result.2, second.shared.2) })) <$>
    (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall (selector request))).run second.shared.1) _
  change RelTriple (_ <$> (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall (selector request))).run first.2.2) _ _
  refine relTriple_map (relTriple_post_mono (local_coupled (selector request) first.2.2 second.shared.1 stripped cached) ?_)
  intro left right held
  obtain ⟨equal, localSame, cacheSame⟩ := held
  exact Or.inr (Or.inr ⟨by rw [equal], roles, controls, consumed, ⟨localSame, cacheSame⟩, seals⟩)

end SelectorStep

section Post
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A coupling can be strengthened by the support of its right computation. -/
theorem support_right {β γ : Type} {first : ProbComp β} {second : ProbComp γ} {post : β → γ → Prop}
    (coupled : RelTriple first second post) :
    RelTriple first second (fun left right => post left right ∧ right ∈ support second) := by
  rw [relTriple_iff_relWP, relWP_iff_couplingPost] at coupled ⊢
  obtain ⟨coupling, holds⟩ := coupled
  refine ⟨coupling, fun pair reached => ⟨holds pair reached, ?_⟩⟩
  have mapped : pair.2 ∈ (Prod.snd <$> coupling.1).support := by
    rw [spmf_support_map]
    exact ⟨pair, reached, rfl⟩
  rw [coupling.2.map_snd] at mapped
  exact (mem_support_iff_evalSPMF_apply_ne_zero second pair.2).2 ((SPMF.mem_support_iff _ _).1 mapped)

/-- Disclosure is monotone in the known chains. -/
theorem known_mono (first second : RawCtxSelectedMessageFreshness.History S B)
    (grows : ∃ added, second.observations = first.observations ++ added) (chain : RatchetChain)
    (known : chain ∈ RawCtxSelectedMessageFreshness.known [] first) : chain ∈ RawCtxSelectedMessageFreshness.known [] second := by
  obtain ⟨added, equal⟩ := grows
  simp only [RawCtxSelectedMessageFreshness.known, List.nil_append, equal, List.flatMap_append, List.mem_append] at known ⊢
  exact Or.inl known

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (taggedInitial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))

/-- Every operation of the history-extended source post only appends to the reveal history. -/
theorem source_grows (target : RootOutput) (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (first : Concrete M P I D K A N C S B)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × Concrete M P I D K A N C S B)
    (supported : result ∈ support (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux
      source writer prior none key target nonce next sender route decode) query).run first)) :
    ∃ added, result.2.2.1.roles.2.observations = first.2.1.roles.2.observations ++ added := by
  rcases query with ((request | request) | request) | ⟨index, raw⟩
  · rw [record_source, support_map] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact ⟨[], by simp [RawCtxSelectedMessageFamily.tick]⟩
  · rw [reveal_source, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨_, rfl⟩
  · simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhSelectedPostCompiler.original, StateT.run, support_map,
      Set.mem_image] at supported
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := supported
    exact ⟨[], by simp⟩
  · simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhSelectedPostCompiler.original, StateT.run, support_map,
      Set.mem_image] at supported
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := supported
    exact ⟨[], by simp [PqxdhSelectedPostCompiler.install, RawCtxSelectedMessageFamily.tick]⟩

/-- Disclosure of the selected chain is absorbing for the history-extended source post. -/
theorem disclosed_absorbing (target : RootOutput) (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (first : Concrete M P I D K A N C S B) (disclosed : Disclosed target first)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × Concrete M P I D K A N C S B)
    (supported : result ∈ support (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux
      source writer prior none key target nonce next sender route decode) query).run first)) :
    Disclosed target result.2 :=
  known_mono _ _ (source_grows source writer prior key nonce next sender route decode pre application initial selector aux target
    query first result supported) _ disclosed

/-- A logged selected value stays logged through every non-finish operation of the tagged world, and through finishes that keep the log. -/
theorem exposed_absorbing (target : RootOutput)
    (finishKeeps : ∀ index raw state, Exposed target state → ∀ result ∈ support ((finishOp index raw).run state), Exposed target result.2)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (second : TState M P I D K A N C S B) (exposed : Exposed target second)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × TState M P I D K A N C S B)
    (supported : result ∈ support ((world source writer prior key nonce next sender route decode pre application taggedInitial selector aux
      finishOp query).run second)) :
    Exposed target result.2 := by
  rcases query with ((request | request) | request) | ⟨index, raw⟩
  · simp only [world, taggedRecord, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    exact run_absorbing (taggedLabels source writer prior key nonce next) (Logged target)
      (labels_absorbing source writer prior key nonce next target) _ second.shared exposed inner innerSupported
  · simp only [world, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact exposed
  · simp only [world, taggedSelector, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact exposed
  · exact finishKeeps index raw second exposed result supported

end Post

section Impossible
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- The hidden slot, as a Boolean test. -/
def isHidden : Chain → Bool
  | .hidden => true
  | .known _ => false

/-- The number of hidden slots in a list of tagged send chains. -/
def hiddenCount (seals : List Chain) : Nat := seals.countP isHidden

/-- Two ordered positions satisfying a Boolean test give a count of at least two. -/
theorem two_le_countP {α : Type} (test : α → Bool) (list : List α) (first second : Nat)
    (firstBound : first < list.length) (secondBound : second < list.length) (ordered : first < second)
    (firstHolds : test list[first] = true) (secondHolds : test list[second] = true) : 2 ≤ list.countP test := by
  induction list generalizing first second with
  | nil => simp at firstBound
  | cons head tail ih =>
    cases second with
    | zero => omega
    | succ second =>
      cases first with
      | zero =>
        have positive : 0 < tail.countP test :=
          List.countP_pos_iff.mpr ⟨tail[second]'(by simpa using secondBound), List.getElem_mem _, secondHolds⟩
        simp only [List.getElem_cons_zero] at firstHolds
        rw [List.countP_cons_of_pos firstHolds]
        omega
      | succ first =>
        have inner := ih first second (by simpa using firstBound) (by simpa using secondBound) (by omega) firstHolds secondHolds
        rw [List.countP_cons]
        omega

/-- Two ordered seal positions at the exact selected chain are impossible for a represented history whose tagged seal chains have at most one hidden slot and log every known chain, while the selected value is not logged. -/
theorem repeated_impossible {Owner : Type} (target : RootOutput) (history : List (RawCtxSelectedDriverAudit.Event Owner))
    (seals : List Chain) (log : Log)
    (represents : (RawCtxSourceEventRecorder.seals history).map (fun occurrence => occurrence.entry.send_chain) =
      seals.map (reveal target))
    (logged : ∀ chain, RawCtxSelectedChain.Slot.known chain ∈ seals → RawCtxSelectedQueryTrace.rootVector chain ∈ log)
    (once : hiddenCount seals ≤ 1) (fresh : target ∉ log)
    (repeated : RawCtxSelectedSourceSendInputs.RepeatedInput target history) : False := by
  obtain ⟨first, second, ordered, firstChain, secondChain⟩ := repeated
  have lengths : (RawCtxSourceEventRecorder.seals history).length = seals.length := by
    simpa using congrArg List.length represents
  have atIndex : ∀ index (bound : index < (RawCtxSourceEventRecorder.seals history).length),
      ((RawCtxSourceEventRecorder.seals history)[index]).entry.send_chain = reveal target (seals[index]'(lengths ▸ bound)) := by
    intro index bound
    have := congrArg (fun list => list[index]?) represents
    simpa [List.getElem?_map, bound, lengths ▸ bound] using this
  have hiddenAt : ∀ index (bound : index < (RawCtxSourceEventRecorder.seals history).length),
      ((RawCtxSourceEventRecorder.seals history)[index]).entry.send_chain = RawCtxFreshChainCut.concreteChain target →
      isHidden (seals[index]'(lengths ▸ bound)) = true := by
    intro index bound selected
    rw [atIndex index bound] at selected
    cases slot : seals[index]'(lengths ▸ bound) with
    | hidden => rfl
    | known chain =>
      rw [slot] at selected
      simp only [reveal, RawCtxSelectedChain.interpret] at selected
      subst selected
      have present : RawCtxSelectedChain.Slot.known (RawCtxFreshChainCut.concreteChain target) ∈ seals := by
        rw [← slot]
        exact List.getElem_mem _
      have inLog := logged _ present
      rw [RawCtxSelectedQueryTrace.rootVector_concrete] at inLog
      exact absurd inLog fresh
  have firstHidden := hiddenAt first.val first.isLt firstChain
  have secondHidden := hiddenAt second.val second.isLt secondChain
  have two := two_le_countP isHidden seals first.val second.val (lengths ▸ first.isLt) (lengths ▸ second.isLt) ordered
    firstHidden secondHidden
  unfold hiddenCount at once
  omega

end Impossible

section PostCoupled
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (taggedInitial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (finishOp : (index : Fin B) → Pqxdh.Bytes → StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)))

/-- The whole adaptive history-extended source post and the tagged world are coupled up to disclosure of the selected chain or a logged selected value, keeping the representation and any invariant of the tagged world, given the coupling of one attempted finish. -/
theorem post_coupled {Result : Type} (target : RootOutput) (good : TState M P I D K A N C S B → Prop)
    (goodStep : ∀ query second, good second → ∀ result ∈ support ((world source writer prior key nonce next sender route decode pre
      application taggedInitial selector aux finishOp query).run second), good result.2)
    (finishStep : ∀ index raw first second, Represents target first second → good second → ¬ Disclosed target first →
      ¬ Exposed target second →
      RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior
        none key target nonce next sender route decode) (.inr (.finish index raw))).run first)
        ((finishOp index raw).run second) (UpTo (Represents target) (Disclosed target) (Exposed target)))
    (finishKeeps : ∀ index raw state, Exposed target state → ∀ result ∈ support ((finishOp index raw).run state), Exposed target result.2)
    (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B)
    (represents : Represents target first second) (initialGood : good second) :
    RelTriple ((simulateQ (PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer prior
        none key target nonce next sender route decode) client).run first)
      ((simulateQ (world source writer prior key nonce next sender route decode pre application taggedInitial selector aux finishOp)
        client).run second)
      (UpTo (fun left right => Represents target left right ∧ good right) (Disclosed target) (Exposed target)) := by
  refine coupled_run _ _ _ _ _
    (disclosed_absorbing source writer prior key nonce next sender route decode pre application initial selector aux target)
    (exposed_absorbing source writer prior key nonce next sender route decode pre application selector aux taggedInitial finishOp
      target finishKeeps)
    (fun query left right related leftGood rightGood => ?_) client first second (Or.inr (Or.inr ⟨represents, initialGood⟩))
  obtain ⟨leftRepresents, rightGood'⟩ := related
  have base : RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initial selector aux source writer
      prior none key target nonce next sender route decode) query).run left)
      ((world source writer prior key nonce next sender route decode pre application taggedInitial selector aux finishOp query).run right)
      (UpTo (Represents target) (Disclosed target) (Exposed target)) := by
    rcases query with ((request | request) | request) | ⟨index, raw⟩
    · exact record_step source writer prior key nonce next sender route decode pre application initial selector aux taggedInitial
        finishOp target request left right leftRepresents
    · exact reveal_step source writer prior key nonce next sender route decode pre application initial selector aux taggedInitial
        finishOp target request left right leftRepresents
    · exact selector_step source writer prior key nonce next sender route decode pre application initial selector aux taggedInitial
        finishOp target request left right leftRepresents
    · exact finishStep index raw left right leftRepresents rightGood' leftGood rightGood
  refine relTriple_post_mono (support_right base) fun leftResult rightResult held => ?_
  obtain ⟨post, supported⟩ := held
  rcases post with bad | bad | ⟨equal, kept⟩
  · exact Or.inl bad
  · exact Or.inr (Or.inl bad)
  · exact Or.inr (Or.inr ⟨equal, kept, goodStep query right rightGood' rightResult supported⟩)

end PostCoupled

section Marked
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxChainInterpretation RawCtxMaterialInterpretation

/-- The extracted zero-state constructor is total. -/
theorem new_total (send receive : Chain) : ∃ result, RefinedRatchet.new RatchetMaterial send receive = ok result := ⟨_, rfl⟩

/-- The zero-state tagged constructor whose send chain is the hidden slot and whose receive chain is the given known chain. -/
noncomputable def hiddenBase (other : RootOutput) : RefinedRatchet Chain Chain RatchetMaterial :=
  (new_total .hidden (.known (RawCtxFreshChainCut.concreteChain other))).choose

/-- The tagged kernel installed by the finish on the selected message: all cached keys known, the send chain hidden. -/
noncomputable def hiddenKernel (other : RootOutput) : TKernel := mapRefined RawCtxSelectedMessageKey.Slot.known (hiddenBase other)

/-- Every chain and cached key of a native kernel as a known tagged slot. -/
def knownTagged (kernel : RawCtxSelectedMessageReveals.Kernel) : TKernel := mapChains .known .known kernel

/-- A known tagged kernel represents its native kernel for every selected value. -/
theorem known_tagged (target : RootOutput) (kernel : RawCtxSelectedMessageReveals.Kernel) :
    mapKernel target (knownTagged kernel) = kernel := by
  rfl

/-- The Beacon kernel of the 64-byte initializer response `other ++ target` is the hidden-send tagged kernel at `target`. -/
theorem marked_kernel (root other target : RootOutput) :
    PqxdhSelectedMessageBeacon.knownKernel
        (PqxdhInitialRootAudit.kernel (root, RawCtxSelectedInitialConstructor.response64 (other ++ target))).refined =
      mapKernel target (hiddenKernel other) := by
  have base := (new_total .hidden (.known (RawCtxFreshChainCut.concreteChain other))).choose_spec
  have initialized : pqxdh.concrete.resume_initial_ratchet_kdf
      (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
      (RawCtxSelectedInitialConstructor.response64 (other ++ target)) =
      ok (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) (hiddenBase other)) := by
    have split := RawCtxSelectedInitialConstructor.from64_initial (true, PqxdhRootTableInitialization.rootArray root) other target
    simp only [RawCtxSelectedInitialConstructor.from64, ite_true, RawCtxSelectedInitialConstructor.initial,
      RawCtxSelectedInitialConstructor.sendSlot, RawCtxSelectedInitialConstructor.receiveSlot] at split
    rw [split, ← RawCtxSelectedInitialConstructor.new_map]
    change ConcreteRatchetKernel.new (RawCtxFreshChainCut.concreteChain target) (RawCtxFreshChainCut.concreteChain other) = _
    have other' := RawCtxSelectedInitialConstructor.new_map (RawCtxFreshChainCut.concreteChain target) .hidden
      (.known (RawCtxFreshChainCut.concreteChain other))
    change ConcreteRatchetKernel.new (RawCtxFreshChainCut.concreteChain target) (RawCtxFreshChainCut.concreteChain other) = _ at other'
    rw [other', base]
    rfl
  have normal := (PqxdhBeaconPhase2Publication.normalInitial_exact
    (PqxdhInitialRatchetComplementarity.beaconPending (PqxdhRootTableInitialization.rootArray root))
    (RawCtxSelectedInitialConstructor.response64 (other ++ target))).symm.trans initialized
  simp only [PqxdhInitialRootAudit.kernel]
  rw [RustM.ok.inj normal]
  rfl

end Marked

section FinishHelpers
open OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
variable {A N C : Type}

/-- A source-local computation keeps the private audit and does not read it. -/
def Restores {β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp β) : Prop :=
  ∀ state cache, work.run (state, cache) = restore state <$> work.run (strip state, cache)

/-- A source-local callback restores the audit. -/
theorem local_restores {β : Type} (work : LocalCallback A N C β) :
    Restores (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (localCall work)) :=
  fun state cache => local_restore work state cache

/-- Restoring the audit is preserved by simulation. -/
theorem simulate_restores {κ β : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp))
    (restores : ∀ query, Restores (impl query)) (work : OracleComp spec β) : Restores (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value => intro state cache; simp [restore, strip]
  | query_bind query continuation ih =>
    intro state cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, restores query state cache, bind_map_left, map_bind]
    refine bind_congr fun result => ?_
    change (simulateQ impl (continuation result.1)).run (({ result.2.1 with audit := state.audit } : Local A N C), result.2.2) = _
    rw [ih result.1 _ result.2.2, ih result.1 result.2.1 result.2.2, Functor.map_map]
    rfl

/-- Two source-local states equal up to the audit give coupled runs of an audit-restoring computation. -/
theorem restores_coupled {β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp β)
    (restores : Restores work) (first second : RawCtxSharedPrimitive.SharedState (Local A N C))
    (stripped : strip first.1 = strip second.1) (cached : first.2 = second.2) :
    RelTriple (work.run first) (work.run second)
      (fun left right => left.1 = right.1 ∧ strip left.2.1 = strip right.2.1 ∧ left.2.2 = right.2.2) := by
  obtain ⟨firstLocal, cache⟩ := first
  obtain ⟨secondLocal, secondCache⟩ := second
  simp only at stripped cached
  subst cached
  rw [restores firstLocal cache, restores secondLocal cache, stripped]
  exact relTriple_map (relTriple_refl_of_mem_support _ fun _ _ => ⟨rfl, rfl, rfl⟩)

/-- An audit-restoring computation run beside the log is coupled with the plain run, up to the audit. -/
theorem restores_near {β : Type} (target : RootOutput) (work : StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp β)
    (restores : Restores work) (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple (work.run first) ((keepLog work).run second) (UpTo Near (fun _ => False) (Logged target)) := by
  change RelTriple _ ((fun reply => (reply.1, (reply.2, second.2))) <$> work.run second.1) _
  rw [← id_map (work.run first)]
  refine relTriple_map (relTriple_post_mono (restores_coupled work restores first second.1 near.1 near.2) ?_)
  intro left right held
  exact Or.inr (Or.inr ⟨held.1, held.2.1, held.2.2⟩)

/-- The initializer callback appends its audit and otherwise ignores the audit: runs from states equal up to the audit are coupled with equal replies. -/
theorem initial_coupled (work : LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (first second : RawCtxSharedPrimitive.SharedState (Local A N C))
    (stripped : strip first.1 = strip second.1) (cached : first.2 = second.2) :
    RelTriple ((PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (initialCall work)).run first)
      ((PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (initialCall work)).run second)
      (fun left right => left.1 = right.1 ∧ strip left.2.1 = strip right.2.1 ∧ left.2.2 = right.2.2) := by
  obtain ⟨firstLocal, cache⟩ := first
  obtain ⟨secondLocal, secondCache⟩ := second
  simp only at stripped cached
  subst cached
  have external : externalState firstLocal = externalState secondLocal := by
    change externalState (strip firstLocal) = externalState (strip secondLocal)
    rw [stripped]
  change RelTriple (PqxdhSelectedStateInterpreter.pair <$> (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((fun result => (result.1.2, { afterExternal firstLocal result.2 with
        audit := firstLocal.audit ++ PqxdhInitialParentObserverCompiler.candidates result.1 })) <$>
        simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState firstLocal)))).run cache)
    (PqxdhSelectedStateInterpreter.pair <$> (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((fun result => (result.1.2, { afterExternal secondLocal result.2 with
        audit := secondLocal.audit ++ PqxdhInitialParentObserverCompiler.candidates result.1 })) <$>
        simulateQ RawCtxSelectiveSharedRom.coins (work.run (externalState secondLocal)))).run cache) _
  rw [external, simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map, Functor.map_map, Functor.map_map]
  refine relTriple_map (relTriple_refl_of_mem_support _ fun result _ => ⟨rfl, ?_, rfl⟩)
  change strip (afterExternal firstLocal result.1.2) = strip (afterExternal secondLocal result.1.2)
  have key : ∀ state : Local A N C, strip (afterExternal state result.1.2) = afterExternal (strip state) result.1.2 :=
    fun _ => rfl
  rw [key, key, stripped]

end FinishHelpers

section TaggedFinish
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The target-free initializer reply: on the selected message the hidden-send tagged kernel, otherwise the known tagged image of the actual initializer reply. -/
noncomputable def taggedInitialCall (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp (Option TKernel) :=
  if PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets then pure (some (hiddenKernel other))
  else Option.map (fun kernel => knownTagged (PqxdhSelectedMessageBeacon.knownKernel kernel)) <$>
    PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initial selector aux (.inr (.inr (.inl secrets)))

/-- The tagged first receive of an attempted finish and its staged registration. -/
noncomputable def taggedStage (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : TKernel) (raw : Pqxdh.Bytes) :
    StateT (RawCtxSharedPrimitive.SharedState (Local A N C) × Log) ProbComp (Option (PqxdhInitialGenericBeacon.Staged TKernel)) :=
  PqxdhSelectedBeaconCompiler.stage candidate <$>
    (RawCtxChainOwner.rawReceive (RawCtxGenericOwnerInterpretation.interpretedCalls
      (taggedLabels source writer prior key nonce next) symbolicCalls) decode raw).run
      (PqxdhInitialGenericBeacon.localOwner candidate kernel)

/-- The target-free attempted finish of a tagged Beacon: the same preparation and application callbacks, the target-free initializer reply and the tagged first receive. -/
noncomputable def taggedFinish (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K) :
    StateT (RawCtxSharedPrimitive.SharedState (Local A N C) × Log) ProbComp (Option Pqxdh.Bytes × BeaconState TKernel I D K) :=
  match before.beacon.phase with
  | .initSent control prekey oneTime kem => do
    let prepared ← keepLog (simulateQ (fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initial
      selector aux (.inl query)) (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw))
    match prepared with
    | none => pure (PqxdhInitialGenericBeacon.finish control before none)
    | some pending => do
      let kernel ← keepLog (taggedInitialCall pre application initial selector aux fixed selectedMessage other pending.root)
      match kernel with
      | none => pure (PqxdhInitialGenericBeacon.finish control before none)
      | some kernel => do
        let reply ← keepLog (PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initial selector aux
          (.inr (.inl pending.response)))
        let staged ← match reply with
          | none => pure none
          | some raw => (taggedStage source writer prior key nonce next decode (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernel raw)
        pure (PqxdhInitialGenericBeacon.finish control before staged)
  | _ => pure (none, before)

/-- A raw receive commutes with a kernel map of its owner, given the receive call equation. -/
theorem raw_map {Kernel Other Metadata : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Kernel → Other) (calls : RawCtxChainOwner.Calls Kernel m) (otherCalls : RawCtxChainOwner.Calls Other m)
    (receiveMap : ∀ entry sequence context, otherCalls.receive (interpret entry) sequence context =
      Prod.map interpret id <$> calls.receive entry sequence context)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : RawCtxChainOwner.State Kernel Metadata) :
    (RawCtxChainOwner.rawReceive otherCalls decode raw).run
      ⟨interpret state.kernel, state.expectedSender, state.associatedData, state.metadata, state.rawAttempts⟩ =
      (fun result => (result.1, (⟨interpret result.2.kernel, result.2.expectedSender, result.2.associatedData, result.2.metadata,
        result.2.rawAttempts⟩ : RawCtxChainOwner.State Other Metadata))) <$>
        (RawCtxChainOwner.rawReceive calls decode raw).run state := by
  simp only [RawCtxChainOwner.rawReceive, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp [empty, RawCtxChainOwner.publish]
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : decode raw with
    | none => simp [RawCtxChainOwner.publish]
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
      · simp only [valid, ite_true, receiveMap, bind_map_left, map_bind, map_pure]
        rfl
      · simp [valid, RawCtxChainOwner.publish]

end TaggedFinish

section StageCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {A N C : Type}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)

/-- The first receive of an attempted finish on a represented kernel and its tagged first receive are coupled up to a logged selected value, with the represented staged registration. -/
theorem stage_coupled (target : RootOutput) (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : TKernel) (raw : Pqxdh.Bytes)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C)) (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log)
    (near : Near first second) :
    RelTriple ((PqxdhSelectedBeaconCompiler.stage candidate <$>
        (RawCtxChainOwner.rawReceive (PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next) decode raw).run
          (PqxdhInitialGenericBeacon.localOwner candidate (mapKernel target kernel))).run first)
      ((taggedStage source writer prior key nonce next decode candidate kernel raw).run second)
      (fun left right => Logged target right.2 ∨
        (left.1 = right.1.map (PqxdhInitialGenericBeacon.mapStaged (mapKernel target)) ∧ Near left.2 right.2)) := by
  have mapped := raw_map (mapKernel target)
    (RawCtxGenericOwnerInterpretation.interpretedCalls (concreteLabels (A := Local A N C) source writer prior key nonce next target)
      symbolicCalls)
    (PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next)
    (fun entry sequence context => by
      change _ = Prod.map (mapKernel target) id <$> simulateQ (concreteLabels source writer prior key nonce next target)
        (simulateQ receiveInject (RawCtxChainReceive.execute entry sequence context))
      rw [labels_receive]
      exact receive_map source writer prior key nonce next target entry sequence context)
    decode raw (PqxdhInitialGenericBeacon.localOwner candidate kernel)
  have mapped' : (RawCtxChainOwner.rawReceive (PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next)
      decode raw).run (PqxdhInitialGenericBeacon.localOwner candidate (mapKernel target kernel)) = _ := mapped
  rw [mapped', ← RawCtxGenericOwnerInterpretation.raw_interpretation]
  unfold taggedStage
  rw [← RawCtxGenericOwnerInterpretation.raw_interpretation, StateT.run_map, StateT.run_map, StateT.run_map]
  try rw [Functor.map_map]
  refine relTriple_map (relTriple_post_mono (labels_near source writer prior key nonce next target _ first second near) ?_)
  intro left right held
  rcases held with impossible | bad | ⟨equal, closer⟩
  · exact impossible.elim
  · exact Or.inl bad
  · refine Or.inr ⟨?_, closer⟩
    simp only [PqxdhSelectedBeaconCompiler.stage, equal]
    exact PqxdhInitialGenericBeacon.opening_map (mapKernel target) candidate right.1.2.kernel right.1.1

end StageCoupling

section FinishCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- An audit-restoring computation run beside the log is coupled exactly with the plain run: equal replies and states equal up to the audit. -/
theorem restores_exact {β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp β)
    (restores : Restores work) (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple (work.run first) ((keepLog work).run second) (fun left right => left.1 = right.1 ∧ Near left.2 right.2) := by
  change RelTriple _ ((fun reply => (reply.1, (reply.2, second.2))) <$> work.run second.1) _
  rw [← id_map (work.run first)]
  exact relTriple_map (relTriple_post_mono (restores_coupled work restores first second.1 near.1 near.2)
    fun _ _ held => ⟨held.1, held.2.1, held.2.2⟩)

/-- The preparation of an attempted finish under the concrete source interpreter and under the target-free finish are coupled exactly. -/
theorem prepare_coupled {β : Type}
    (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (target : RootOutput) (work : OracleComp (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared) β)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple ((simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key
        target nonce next decode) (simulateQ PqxdhSelectedInitialOwnerCompiler.preForward work)).run first)
      ((keepLog (simulateQ (fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux
        (.inl query)) work)).run second)
      (fun left right => left.1 = right.1 ∧ Near left.2 right.2) := by
  have composed : simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key
      target nonce next decode) (simulateQ PqxdhSelectedInitialOwnerCompiler.preForward work) =
      simulateQ (fun query => PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux
        (.inl query)) work := by
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext query
    simp only [QueryImpl.compose, PqxdhSelectedInitialOwnerCompiler.preForward, simulateQ_spec_query]
    rfl
  rw [composed]
  exact restores_exact _ (simulate_restores _ (fun query => local_restores (pre query)) work) first second near

end FinishCoupling

section InitialStep
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The initializer query of an attempted finish and the target-free initializer reply are coupled: the concrete kernel is represented by the tagged kernel, states agree up to the audit. -/
theorem initial_step (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple ((PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialC selector aux
        (.inr (.inr (.inl secrets)))).run first)
      ((keepLog (taggedInitialCall pre application initialW selector aux fixed selectedMessage other secrets)).run second)
      (fun left right => left.1.map PqxdhSelectedMessageBeacon.knownKernel = right.1.map (mapKernel target) ∧
        Near left.2 right.2) := by
  cases selected : PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets with
  | true =>
    have tagged : (keepLog (taggedInitialCall pre application initialW selector aux fixed selectedMessage other secrets)).run second =
        pure (some (hiddenKernel other), second) := by
      simp only [taggedInitialCall, selected, ite_true]
      change (fun reply => (reply.1, (reply.2, second.2))) <$>
        (pure (some (hiddenKernel other)) : StateT (RawCtxSharedPrimitive.SharedState (Local A N C)) ProbComp _).run second.1 = _
      simp
    rw [tagged]
    refine relTriple_post_mono (product_coupling (Q := fun right => right = (some (hiddenKernel other), second))
      (marked secrets selected first) (fun _ reached => by simpa using reached)) ?_
    intro left right held
    obtain ⟨⟨kernel, stripped, cached⟩, rfl⟩ := held
    exact ⟨by simp [kernel], stripped.trans near.1, cached.trans near.2⟩
  | false =>
    have taggedFalse : taggedInitialCall pre application initialW selector aux fixed selectedMessage other secrets =
        Option.map (fun kernel => knownTagged (PqxdhSelectedMessageBeacon.knownKernel kernel)) <$>
          PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (initialCall (initialW secrets)) := by
      simp only [taggedInitialCall, selected, Bool.false_eq_true, ite_false]
      rfl
    rw [taggedFalse]
    change RelTriple ((PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (initialCall (initialC secrets))).run first)
      ((fun reply => (reply.1, (reply.2, second.2))) <$>
        (Option.map (fun kernel => knownTagged (PqxdhSelectedMessageBeacon.knownKernel kernel)) <$>
          (PqxdhSelectedStateInterpreter.evaluate AdaptiveCtxSharedHash.hashImpl (initialCall (initialW secrets)))).run second.1) _
    rw [unmarked secrets selected, StateT.run_map, Functor.map_map, ← id_map ((PqxdhSelectedStateInterpreter.evaluate
      AdaptiveCtxSharedHash.hashImpl (initialCall (initialW secrets))).run first)]
    refine relTriple_map (relTriple_post_mono (initial_coupled (initialW secrets) first second.1 near.1 near.2) ?_)
    intro left right held
    obtain ⟨equal, stripped, cached⟩ := held
    refine ⟨?_, stripped, cached⟩
    simp only [id_eq, equal, Option.map_map]
    rfl

end InitialStep

section OwnerCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The postcondition of a coupled attempted finish: a logged selected value, or represented replies and Beacons with states equal up to the audit. -/
def FinishPost (target : RootOutput) (left : PqxdhSelectedInitialOwnerCompiler.Reply I D K × RawCtxSharedPrimitive.SharedState (Local A N C))
    (right : (Option Pqxdh.Bytes × BeaconState TKernel I D K) × (RawCtxSharedPrimitive.SharedState (Local A N C) × Log)) : Prop :=
  Logged target right.2 ∨ (left.1 = Prod.map id (mapBeacon (mapKernel target)) right.1 ∧ Near left.2 right.2)

/-- An attempted finish of the concrete source post on a represented Beacon and the target-free finish on the tagged Beacon are coupled up to a logged selected value. -/
theorem owner_coupled (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C))
    (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) (near : Near first second) :
    RelTriple ((simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key
        target nonce next decode) (PqxdhSelectedInitialOwnerCompiler.owner raw (mapBeacon (mapKernel target) before))).run first)
      ((taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
        raw before).run second)
      (FinishPost target) := by
  unfold PqxdhSelectedInitialOwnerCompiler.owner taggedFinish
  cases phase : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    have concretePhase : (mapBeacon (mapKernel target) before).beacon.phase = .initSent control prekey oneTime kem := by
      simp [mapBeacon, phase, mapPhase]
    simp only [concretePhase, simulateQ_bind, StateT.run_bind]
    refine relTriple_bind (prepare_coupled source writer prior key nonce next decode pre application selector aux initialC initialW target
      (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw) first second near) ?_
    rintro ⟨prepared, middle⟩ ⟨prepared', middle'⟩ ⟨equal, closer⟩
    simp only at equal
    subst equal
    cases prepared with
    | none =>
      simp only [simulateQ_pure, StateT.run_pure]
      refine relTriple_pure_pure (Or.inr ⟨?_, closer⟩)
      simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
    | some pending =>
      dsimp only
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine relTriple_bind (initial_step pre application selector aux fixed selectedMessage other initialC initialW target marked unmarked
        pending.root middle middle' closer) ?_
      rintro ⟨kernelC, middle2⟩ ⟨kernelW, middle2'⟩ ⟨related, closer2⟩
      cases kernelC with
      | none =>
        cases kernelW with
        | none =>
          simp only [simulateQ_pure, StateT.run_pure]
          refine relTriple_pure_pure (Or.inr ⟨?_, closer2⟩)
          simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
        | some kernelW => simp at related
      | some kernelC =>
        cases kernelW with
        | none => simp at related
        | some kernelW =>
          simp only [Option.map_some, Option.some.injEq] at related
          dsimp only
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
          refine relTriple_bind (restores_exact _ (local_restores (application pending.response)) middle2 middle2' closer2) ?_
          rintro ⟨reply, middle3⟩ ⟨reply', middle3'⟩ ⟨equal, closer3⟩
          simp only at equal
          subst equal
          dsimp only
          simp only [PqxdhSelectedInitialOwnerCompiler.source]
          rw [related]
          cases reply with
          | none =>
            simp only [map_pure, StateT.run_pure, pure_bind]
            refine relTriple_pure_pure (Or.inr ⟨?_, closer3⟩)
            simpa using PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before none
          | some delivered =>
            simp only [bind_pure_comp, StateT.run_map]
            have staging := stage_coupled source writer prior key nonce next decode target
              (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernelW delivered middle3 middle3' closer3
            rw [StateT.run_map] at staging
            refine relTriple_map (relTriple_post_mono staging ?_)
            intro left right held
            rcases held with bad | ⟨staged, closer4⟩
            · exact Or.inl bad
            · refine Or.inr ⟨?_, closer4⟩
              simp only [staged]
              exact PqxdhInitialGenericBeacon.finish_map (mapKernel target) control before right.1
  | fresh _ _ _ | freshWithCoins _ _ _ _ | established _ _ _ | aborted _ =>
    simp only [mapBeacon, phase, mapPhase, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (Or.inr ⟨by simp [mapBeacon, phase, mapPhase], near⟩)

end OwnerCoupling

section FinishStep
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A computation over a shared state and log never removes a logged selected value. -/
def Grows {σ β : Type} (target : RootOutput) (work : StateT (σ × Log) ProbComp β) : Prop :=
  ∀ state, target ∈ state.2 → ∀ result ∈ support (work.run state), target ∈ result.2.2

/-- A return never removes a logged selected value. -/
theorem grows_pure {σ β : Type} (target : RootOutput) (value : β) : Grows (σ := σ) target (pure value) := by
  intro state logged result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact logged

/-- Sequencing two computations that never remove a logged selected value never removes it. -/
theorem grows_bind {σ β γ : Type} (target : RootOutput) (work : StateT (σ × Log) ProbComp β)
    (continuation : β → StateT (σ × Log) ProbComp γ) (first : Grows target work)
    (rest : ∀ value, Grows target (continuation value)) : Grows target (work >>= continuation) := by
  intro state logged result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, middleSupported, restSupported⟩ := supported
  exact rest middle.1 middle.2 (first state logged middle middleSupported) result restSupported

/-- Mapping the result of a computation keeps the logged-value property. -/
theorem grows_map {σ β γ : Type} (target : RootOutput) (work : StateT (σ × Log) ProbComp β) (function : β → γ)
    (grows : Grows target work) : Grows target (function <$> work) := by
  intro state logged result supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, middleSupported, rfl⟩ := supported
  exact grows state logged middle middleSupported

/-- A shared-state service run beside an unchanged log never removes a logged selected value. -/
theorem grows_keep {β : Type} (target : RootOutput) (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β) :
    Grows target (keepLog work) := by
  intro state logged result supported
  simp only [keepLog, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact logged

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)

/-- A record primitive program under the target-free services never removes a logged selected value. -/
theorem grows_labels {β : Type} (target : RootOutput) (work : OracleComp LabelSpec β) :
    Grows (σ := RawCtxSharedPrimitive.SharedState A) target (simulateQ (taggedLabels source writer prior key nonce next) work) :=
  fun state logged result supported => run_absorbing (taggedLabels source writer prior key nonce next) (Logged target)
    (labels_absorbing source writer prior key nonce next target) work state logged result supported

/-- The tagged first receive of an attempted finish never removes a logged selected value. -/
theorem grows_stage (target : RootOutput) (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : TKernel) (raw : Pqxdh.Bytes) :
    Grows (σ := RawCtxSharedPrimitive.SharedState (Local A N C)) target
      (taggedStage source writer prior key nonce next decode candidate kernel raw) := by
  unfold taggedStage
  rw [← RawCtxGenericOwnerInterpretation.raw_interpretation]
  intro state logged result supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, middleSupported, rfl⟩ := supported
  exact grows_labels source writer prior key nonce next target _ state logged middle middleSupported

variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The target-free finish never removes a logged selected value. -/
theorem grows_finish (target : RootOutput) (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K) :
    Grows target (taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage
      other raw before) := by
  unfold taggedFinish
  split
  · refine grows_bind target _ _ (grows_keep target _) fun prepared => ?_
    rcases prepared with _ | pending
    · exact grows_pure target _
    · refine grows_bind target _ _ (grows_keep target _) fun kernel => ?_
      rcases kernel with _ | kernel
      · exact grows_pure target _
      · refine grows_bind target _ _ (grows_keep target _) fun reply => ?_
        rcases reply with _ | delivered
        · exact grows_bind target _ _ (grows_pure target _) fun _ => grows_pure target _
        · exact grows_bind target _ _ (grows_stage source writer prior key nonce next decode target _ _ _) fun _ => grows_pure target _
  · exact grows_pure target _

/-- The attempted-finish operation of the tagged world: the target-free finish of the indexed tagged Beacon, installed in place. -/
noncomputable def taggedFinishOp (index : Fin B) (raw : Pqxdh.Bytes) :
    StateT (TState M P I D K A N C S B) ProbComp (Option (Option Pqxdh.Bytes)) := fun state =>
  (fun result => (some result.1.1, ⟨state.seals, { state.front with
      roles := (state.front.roles.1, Function.update state.front.roles.2 index result.1.2) }, result.2⟩)) <$>
    (taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other raw
      (state.front.roles.2 index)).run state.shared

/-- The tagged finish operation never removes a logged selected value. -/
theorem finish_keeps (target : RootOutput) (index : Fin B) (raw : Pqxdh.Bytes) (state : TState M P I D K A N C S B)
    (exposed : Exposed target state)
    (result : Option (Option Pqxdh.Bytes) × TState M P I D K A N C S B)
    (supported : result ∈ support ((taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux
      fixed selectedMessage other index raw).run state)) : Exposed target result.2 := by
  simp only [taggedFinishOp, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  exact grows_finish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
    target raw _ state.shared exposed inner innerSupported

end FinishStep

section FinishStepCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable RawCtxChainInterpretation PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- A concrete attempted finish of the history-extended source post, unfolded to the owner program. -/
theorem finish_source (initialC : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput) (index : Fin B) (raw : Pqxdh.Bytes)
    (first : Concrete M P I D K A N C S B) :
    ((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initialC selector aux source writer prior none key
      target nonce next sender route decode) (.inr (.finish index raw))).run first =
      (fun result => (some result.1.1, (first.1 ++ [], (PqxdhSelectedPostCompiler.install index first.2.1 result.1.2, result.2)))) <$>
        (simulateQ (PqxdhSelectedInitialOwnerCompiler.source pre application initialC selector aux source writer prior none key target
          nonce next decode) (PqxdhSelectedInitialOwnerCompiler.owner raw (first.2.1.roles.1.2 index))).run first.2.2 := by
  simp only [PqxdhFirstRecordNonceStop.sourceObserved, PqxdhFirstRecordNonceStop.sourceEvents, PqxdhSelectedPostCompiler.original,
    StateT.run, Functor.map_map]
  rfl

/-- An attempted finish of the concrete source post and of the tagged world are coupled up to a logged selected value. -/
theorem finish_step (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply) (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ first : RawCtxSharedPrimitive.SharedState (Local A N C), ∀ result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal
        (X := X) pre application initialC selector aux (.inr (.inr (.inl secrets)))).run first),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip first.1 ∧ result.2.2 = first.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (index : Fin B) (raw : Pqxdh.Bytes) (first : Concrete M P I D K A N C S B) (second : TState M P I D K A N C S B)
    (represents : Represents target first second) :
    RelTriple (((PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initialC selector aux source writer prior none
      key target nonce next sender route decode) (.inr (.finish index raw))).run first)
      ((taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
        index raw).run second)
      (UpTo (Represents target) (Disclosed target) (Exposed target)) := by
  rw [finish_source]
  obtain ⟨roles, controls, consumed, near, seals⟩ := represents
  have beacon : first.2.1.roles.1.2 index = mapBeacon (mapKernel target) (second.front.roles.2 index) := by
    rw [roles]
    rfl
  rw [beacon]
  refine relTriple_map (relTriple_post_mono (owner_coupled source writer prior key nonce next decode pre application selector aux fixed
    selectedMessage other initialC initialW target marked unmarked raw (second.front.roles.2 index) first.2.2 second.shared near) ?_)
  intro left right held
  rcases held with bad | ⟨equal, closer⟩
  · exact Or.inr (Or.inl bad)
  · refine Or.inr (Or.inr ⟨by rw [equal]; rfl, ?_, controls, consumed, closer, by simpa using seals⟩)
    simp only [PqxdhSelectedPostCompiler.install, equal, roles, mapRoles, Prod.map_snd]
    congr 1
    funext position
    by_cases same : position = index
    · subst same
      simp
    · simp [same]

end FinishStepCoupling

section InitialInstances
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
variable {ι I D K X Response A N : Type} {extra : OracleSpec ι}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)

/-- A state-monad return applied to a state. -/
theorem state_pure_apply {σ α : Type} (value : α) (state : σ) : (pure value : StateT σ ProbComp α) state = pure (value, state) := rfl

/-- A state-monad map applied to a state. -/
theorem state_map_apply {σ α β : Type} (function : α → β) (work : StateT σ ProbComp α) (state : σ) :
    (function <$> work) state = (fun result => (function result.1, result.2)) <$> work state :=
  StateT.run_map function work state

/-- On the selected message the actual initializer callback with the 64-byte response `other ++ target` returns the represented hidden-send kernel and changes only the private audit. -/
theorem initial_marked (other target : RootOutput) (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (selected : PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true)
    (first : RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache))
    (result : Option (PqxdhInitialPendingPost.KernelOf RatchetChain) × RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache))
    (supported : result ∈ support ((PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application
      (initialLocal fixed selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
      selector aux (.inr (.inr (.inl secrets)))).run first)) :
    result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
      strip result.2.1 = strip first.1 ∧ result.2.2 = first.2 := by
  have request := (PqxdhInitialSelectedOrigin.selectedRequest_iff selectedMessage _).mp selected
  obtain ⟨state, cache⟩ := first
  simp only [PqxdhSelectedInitialOwnerCompiler.sourceExternal, PqxdhSelectedStateInterpreter.evaluate,
    PqxdhSelectedCallbackCompiler.callback, initialCall, initialLocal, request, PqxdhInitialRootAudit.retained, ite_true,
    StateT.run, state_pure_apply, map_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact ⟨by simp [PqxdhSelectedStateInterpreter.pair, marked_kernel], rfl, rfl⟩

end InitialInstances

section SendPreservation
open ratchet.refined ratchet.control RawCtxChainInterpretation RawCtxMaterialInterpretation

/-- The saved kernel of a chain-handle receive effect. -/
def chainEntry {Send Receive Material Context : Type} :
    RawCtxChainReceive.Effect Send Receive Material Context → RefinedRatchet Send Receive Material
  | .rejected entry _ => entry
  | .kdfRequested pending => pending.entry
  | .openRequested opening => opening.entry

/-- Two distinct chains used to separate one chain handle from all others. -/
def chainOne : RatchetChain := RawCtxFreshChainCut.concreteChain (List.Vector.replicate 32 0)
/-- The second separating chain. -/
def chainTwo : RatchetChain := RawCtxFreshChainCut.concreteChain (List.Vector.replicate 32 1)

/-- The two separating chains differ. -/
theorem chains_differ : chainOne ≠ chainTwo := by
  intro same
  have values := congrArg RawCtxSelectedQueryTrace.rootVector same
  simp only [chainOne, chainTwo, RawCtxSelectedQueryTrace.rootVector_concrete] at values
  have first := congrArg (fun vector : List.Vector UInt8 32 => vector.head) values
  simp at first

/-- Separate one value from all others. -/
noncomputable def separate {α : Type} (value : α) (other : α) : RatchetChain :=
  @ite _ (other = value) (Classical.propDecidable _) chainOne chainTwo

/-- The separating chain assignment of a value distinguishes that value from every other value. -/
theorem separate_eq {α : Type} (value other : α) (same : separate value other = separate value value) : other = value := by
  by_contra different
  unfold separate at same
  rw [@ite_eq_right _ (Classical.propDecidable _) different, @ite_eq_left _ (Classical.propDecidable _) rfl] at same
  exact chains_differ same.symm

/-- A fixed material used for the separating interpretation. -/
noncomputable def someMaterial : RatchetMaterial :=
  (RawCtxInterpretedReceive.decodeResponse ⟨⟨List.replicate 76 0#u8, by simp⟩⟩).2

/-- Actual receive admission saves the given kernel. -/
theorem begin_send {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material)
    (target : Std.U64) (context : Context) :
    (chainEntry (RawCtxChainReceive.normalBegin kernel target context)).send_chain = kernel.send_chain := by
  let send := separate kernel.send_chain
  let receive : Receive → RatchetChain := fun _ => chainOne
  let material : Material → RatchetMaterial := fun _ => someMaterial
  have saved := RawCtxOwnerOracle.begin_entry ⟨mapRefined material (mapChains send receive kernel)⟩ target context
  rw [RawCtxInterpretedReceive.normalBegin_native, RawCtxInterpretedReceive.normalBegin_map,
    RawCtxChainReceive.normalBegin_native] at saved
  apply separate_eq
  change send _ = send _
  cases effect : RawCtxChainReceive.normalBegin kernel target context <;>
    simp only [effect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect, RawCtxInterpretedReceive.nativeEffect,
      effectEntry, RawCtxInterpretedReceive.nativeKdf, RawCtxInterpretedReceive.mapKdf, RawCtxChainReceive.nativeKdf,
      RawCtxInterpretedOpening.toNative, RawCtxInterpretedOpening.mapOpening, mapOpeningChains, ConcreteRatchetKernel.mk.injEq,
      chainEntry] at saved ⊢
  all_goals exact congrArg (fun entry => entry.send_chain) saved

/-- A receive resumption keeps the saved kernel. -/
theorem resume_send {Send Receive Material Context : Type} (pending : RawCtxChainReceive.Kdf Send Receive Material Context)
    (reply : Receive × Material) :
    (chainEntry (RawCtxChainReceive.normalResume pending reply)).send_chain = pending.entry.send_chain := by
  let send := separate pending.entry.send_chain
  let receive : Receive → RatchetChain := fun _ => chainOne
  have native := RawCtxChainReceive.normalResume_native send receive pending reply
  obtain ⟨result, resumed, progress⟩ := RawCtxInterpretedReceive.resume_progress
    (RawCtxChainReceive.nativeKdf send receive pending) (receive reply.1, reply.2)
  have normal := (RawCtxInterpretedReceive.normalResume_exact (RawCtxChainReceive.nativeKdf send receive pending)
    (receive reply.1, reply.2)).symm.trans resumed
  have same := RustM.ok.inj normal
  rw [native] at same
  have saved := progress.1
  rw [← same] at saved
  apply separate_eq
  change send _ = send _
  cases effect : RawCtxChainReceive.normalResume pending reply <;>
    simp only [effect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.effectEntry, RawCtxChainReceive.nativeKdf,
      mapOpeningChains, chainEntry] at saved ⊢
  all_goals exact congrArg (fun entry => entry.send_chain) saved

/-- Cached publication keeps the send chain. -/
theorem cached_send {Send Receive Material : Type} (state : RefinedRatchet Send Receive Material) (prepared : PreparedCachedReceive)
    (result : RefinedRatchet Send Receive Material) (published : publish_cached_receive state prepared = ok result) :
    result.send_chain = state.send_chain := by
  by_cases targetBound : prepared.target_slot.val < 50
  · by_cases lastBound : prepared.last_slot.val < 50
    · obtain ⟨actual, actualEq, _, chainEq, _⟩ := publish_cached_receive_exact state prepared targetBound lastBound
      cases RustM.ok.inj (actualEq.symm.trans published)
      exact chainEq
    · simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok,
        ite_eq_right (by scalar_tac : ¬UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64),
        ite_eq_left (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.last_slot ≥ UScalar.cast UScalarTy.Usize 50#u64)] at published
      cases RustM.ok.inj published
      rfl
  · simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok,
      ite_eq_left (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64)] at published
    cases RustM.ok.inj published
    rfl

/-- Future publication keeps the send chain. -/
theorem future_send {Send Receive Material : Type} (state : RefinedRatchet Send Receive Material)
    (prepared : PendingReceive Receive Material)
    (result : RefinedRatchet Send Receive Material) (published : publish_future_receive state prepared = ok result) :
    result.send_chain = state.send_chain := by
  by_cases bound : prepared.first_slot.val + prepared.skipped.val ≤ 50
  · obtain ⟨actual, actualEq, _, chainEq, _⟩ := publish_future_receive_exact state prepared bound
    cases RustM.ok.inj (actualEq.symm.trans published)
    exact chainEq
  · simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok] at published
    by_cases firstBound : 50 < prepared.first_slot.val
    · rw [ite_eq_left (by scalar_tac)] at published
      cases RustM.ok.inj published
      rfl
    · rw [ite_eq_right (by scalar_tac)] at published
      obtain ⟨available, availableEq, availableVal⟩ := uscalar_sub_eq_ok
        (UScalar.cast UScalarTy.Usize 50#u64) (UScalar.cast UScalarTy.Usize prepared.first_slot) (by scalar_tac)
      simp only [availableEq, bind_tc_ok,
        ite_eq_left (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.skipped > available)] at published
      cases RustM.ok.inj published
      rfl

/-- A receive opening's publication keeps the send chain on every reply. -/
theorem finish_send {Send Receive Material Context Plaintext : Type}
    (pending : RawCtxInterpretedOpening.Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    (RawCtxChainReceive.normalFinish pending reply).1.send_chain = pending.entry.send_chain := by
  have exact := RawCtxChainReceive.normalFinish_exact pending reply
  cases reply with
  | none =>
    simp only [RawCtxInterpretedOpening.finish] at exact
    rw [← RustM.ok.inj exact]
  | some value =>
    cases prepared : pending.prepared with
    | PreparedReceiveCachedCase cached =>
      obtain ⟨published, publishedEq⟩ := publish_cached_receive_ok pending.entry cached
      simp only [RawCtxInterpretedOpening.finish, prepared, publishedEq, bind_tc_ok] at exact
      rw [← RustM.ok.inj exact]
      exact cached_send pending.entry cached published publishedEq
    | PreparedReceiveFutureCase future =>
      obtain ⟨published, publishedEq⟩ := publish_future_receive_ok pending.entry future
      simp only [RawCtxInterpretedOpening.finish, prepared, publishedEq, bind_tc_ok] at exact
      rw [← RustM.ok.inj exact]
      exact future_send pending.entry future published publishedEq

/-- Send admission either keeps the kernel exhausted or requests a derivation on the kernel's own send chain. -/
theorem send_begin {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    (∃ other, RawCtxChainSend.normalBegin kernel context = .exhausted kernel other) ∨
      ∃ pending, RawCtxChainSend.normalBegin kernel context = .requested pending ∧ pending.entry = kernel ∧
        pending.request = kernel.send_chain := by
  have begun := RawCtxChainSend.normalBegin_exact kernel context
  cases start : RawCtxChainSend.normalBegin kernel context with
  | exhausted entry other =>
    rw [start] at begun
    simp only [RawCtxChainSend.beginSend, Bind.bind, Aeneas.Std.bind] at begun
    repeat' split at begun
    all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
    all_goals cases begun
    all_goals exact Or.inl ⟨_, rfl⟩
  | requested pending =>
    rw [start] at begun
    simp only [RawCtxChainSend.beginSend, Bind.bind, Aeneas.Std.bind] at begun
    repeat' split at begun
    all_goals simp_all only [RustM.ok.injEq, reduceCtorEq]
    all_goals cases begun
    all_goals exact Or.inr ⟨_, rfl, rfl, rfl⟩

end SendPreservation

section CallFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- Every chain-handle receive program keeps the send chain of its saved kernel, under arbitrary stateful labels. -/
theorem program_send {Send Receive Material Context Plaintext σ : Type}
    (labels : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) (StateT σ ProbComp))
    (effect : RawCtxChainReceive.Effect Send Receive Material Context) (state : σ)
    (result : (RefinedRatchet Send Receive Material × core.option.Option Plaintext) × σ)
    (supported : result ∈ support ((simulateQ labels (RawCtxChainReceive.program effect)).run state)) :
    result.1.1.send_chain = (chainEntry effect).send_chain := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      rw [RawCtxChainReceive.program] at supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
    | openRequested pending =>
      rw [RawCtxChainReceive.program] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact finish_send pending reply.1
    | kdfRequested pending =>
      rw [RawCtxChainReceive.program] at supported
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, rest⟩ := supported
      rw [ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending reply.1) _ reply.2 result rest rfl]
      exact resume_send pending reply.1

/-- Every chain-handle receive keeps the kernel's send chain. -/
theorem execute_send {Send Receive Material Context Plaintext σ : Type}
    (labels : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) (StateT σ ProbComp))
    (kernel : RefinedRatchet Send Receive Material) (sequence : Std.U64) (context : Context) (state : σ)
    (result : (RefinedRatchet Send Receive Material × core.option.Option Plaintext) × σ)
    (supported : result ∈ support ((simulateQ labels (RawCtxChainReceive.execute kernel sequence context)).run state)) :
    result.1.1.send_chain = kernel.send_chain :=
  (program_send labels _ state result supported).trans (begin_send kernel sequence context)

/-- The target-free services only append to the log. -/
theorem labels_prefix {β : Type} (work : OracleComp LabelSpec β) (state : RawCtxSharedPrimitive.SharedState A × Log)
    (result : β × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support ((simulateQ (taggedLabels source writer prior key nonce next) work).run state)) :
    state.2 <+: result.2.2 := by
  refine run_absorbing (taggedLabels source writer prior key nonce next) (fun current => state.2 <+: current.2) ?_ work state
    (List.prefix_refl _) result supported
  intro query current held reply reached
  rcases query with (slot | pending) | ((slot | pending) | query)
  all_goals first
    | (simp only [taggedLabels, StateT.run, support_pure, Set.mem_singleton_iff] at reached
       subst reached
       exact held.trans (List.prefix_append _ _))
    | (simp only [taggedLabels, keepLog, StateT.run, support_map, Set.mem_image] at reached
       obtain ⟨_, _, rfl⟩ := reached
       exact held)

end CallFacts

section TaggedCalls
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The chain-handle calls of the tagged world. -/
noncomputable def taggedCalls : RawCtxChainOwner.Calls TKernel (StateT (RawCtxSharedPrimitive.SharedState A × Log) ProbComp) :=
  RawCtxGenericOwnerInterpretation.interpretedCalls (taggedLabels source writer prior key nonce next) symbolicCalls

/-- Every target-free service call only appends to the log. -/
theorem label_prefix (query : LabelSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A × Log)
    (result : LabelSpec.Range query × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support ((taggedLabels source writer prior key nonce next query).run state)) :
    state.2 <+: result.2.2 := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  all_goals first
    | (simp only [taggedLabels, StateT.run, support_pure, Set.mem_singleton_iff] at supported
       subst supported
       exact List.prefix_append _ _)
    | (simp only [taggedLabels, keepLog, StateT.run, support_map, Set.mem_image] at supported
       obtain ⟨_, _, rfl⟩ := supported
       exact List.prefix_refl _)

/-- The target-free derivation always returns a known chain. -/
theorem tagged_known (slot : Chain) : isHidden (taggedStep prior nonce next slot).1 = false := by
  cases slot <;> rfl

/-- A tagged receive keeps the send chain and only appends to the log. -/
theorem tagged_receive (kernel : TKernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState A × Log)
    (result : (TKernel × core.option.Option RawCtxWholeOwner.Decrypted) × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support (((taggedCalls source writer prior key nonce next).receive kernel sequence context).run state)) :
    result.1.1.send_chain = kernel.send_chain ∧ state.2 <+: result.2.2 := by
  refine ⟨?_, labels_prefix source writer prior key nonce next _ state result supported⟩
  change result ∈ support ((simulateQ (taggedLabels source writer prior key nonce next)
    (simulateQ receiveInject (RawCtxChainReceive.execute kernel sequence context))).run state) at supported
  rw [← QueryImpl.simulateQ_compose] at supported
  exact execute_send _ kernel sequence context state result supported

/-- A tagged send either leaves an exhausted kernel unchanged, or requests a derivation on the kernel's send chain, which is logged, and installs a known send chain. -/
theorem tagged_send (kernel : TKernel) (context : RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState A × Log)
    (result : (TKernel × Option RawCtxSourceSend.Encrypted) × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support (((taggedCalls source writer prior key nonce next).send kernel context).run state)) :
    (sendChains kernel context = [] ∧ result.1.1 = kernel ∧ state.2 <+: result.2.2) ∨
      (sendChains kernel context = [kernel.send_chain] ∧ isHidden result.1.1.send_chain = false ∧
        state.2 ++ logged kernel.send_chain <+: result.2.2) := by
  change result ∈ support ((simulateQ (taggedLabels source writer prior key nonce next)
    (simulateQ sendInject (RawCtxChainSend.execute kernel context))).run state) at supported
  rw [← QueryImpl.simulateQ_compose] at supported
  unfold RawCtxChainSend.execute at supported
  rcases send_begin kernel context with ⟨other, begun⟩ | ⟨pending, begun, entry, request⟩
  · rw [begun, RawCtxChainSend.program] at supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Or.inl ⟨by simp [sendChains, begun], rfl, List.prefix_refl _⟩
  · rw [begun, RawCtxChainSend.program] at supported
    simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨reply, replySupported, sealed, sealedSupported, rfl⟩ := supported
    change reply ∈ support ((pure (taggedStep prior nonce next pending.request, (state.1, state.2 ++ logged pending.request)) :
      ProbComp _)) at replySupported
    simp only [support_pure, Set.mem_singleton_iff] at replySupported
    subst replySupported
    have kept := label_prefix source writer prior key nonce next _ _ sealed
      (by simpa only [QueryImpl.compose, sendInject, simulateQ_spec_query] using sealedSupported)
    refine Or.inr ⟨by simp [sendChains, begun], tagged_known prior nonce next pending.request, ?_⟩
    rw [← request]
    exact kept

end TaggedCalls

section OwnerFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {σ : Type} (logOf : σ → Log) (calls : RawCtxChainOwner.Calls TKernel (StateT σ ProbComp))

/-- The known send chains of a seal list are logged. -/
def SealsLogged (seals : List Chain) (log : Log) : Prop :=
  ∀ chain, RawCtxSelectedChain.Slot.known chain ∈ seals → RawCtxSelectedQueryTrace.rootVector chain ∈ log

/-- A receive call keeps the send chain and appends to the log. -/
def ReceiveKeeps : Prop :=
  ∀ kernel sequence context state, ∀ result ∈ support ((calls.receive kernel sequence context).run state),
    result.1.1.send_chain = kernel.send_chain ∧ logOf state <+: logOf result.2

/-- A send call is exhausted, or requests and logs a derivation on the send chain and installs a known send chain. -/
def SendLogs : Prop :=
  ∀ kernel context state, ∀ result ∈ support ((calls.send kernel context).run state),
    (sendChains kernel context = [] ∧ result.1.1 = kernel ∧ logOf state <+: logOf result.2) ∨
      (sendChains kernel context = [kernel.send_chain] ∧ isHidden result.1.1.send_chain = false ∧
        logOf state ++ logged kernel.send_chain <+: logOf result.2)

/-- The effect of an owner request on its kernel, seal chains and log. -/
def OwnerEffect (seals : List Chain) (before after : TKernel) (log log' : Log) : Prop :=
  log <+: log' ∧ SealsLogged seals log' ∧
    ((seals = [] ∧ after.send_chain = before.send_chain) ∨ (seals = [before.send_chain] ∧ isHidden after.send_chain = false))

/-- A known seal chain whose bytes were appended to the log is logged. -/
theorem logged_known (chain : RatchetChain) (log : Log) :
    SealsLogged [RawCtxSelectedChain.Slot.known chain] (log ++ logged (.known chain)) := by
  intro value listed
  simp only [List.mem_singleton, RawCtxSelectedChain.Slot.known.injEq] at listed
  subst listed
  simp [logged]

/-- A single seal chain whose logged value was appended to a prefix of the log is logged. -/
theorem logged_single (slot : Chain) (log log' : Log) (grows : log ++ logged slot <+: log') : SealsLogged [slot] log' := by
  intro value listed
  simp only [List.mem_singleton] at listed
  subst listed
  exact grows.subset (by simp [logged])

/-- The empty list of seal chains is logged. -/
theorem logged_nil (log : Log) : SealsLogged [] log := fun _ impossible => absurd impossible (List.not_mem_nil)

/-- An owner request has an owner effect on its kernel. -/
theorem owner_effect (receiveKeeps : ReceiveKeeps logOf calls) (sendLogs : SendLogs logOf calls) {Metadata : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : RawCtxChainOwner.State TKernel Metadata) (state : σ)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxChainOwner.State TKernel Metadata) × σ)
    (supported : result ∈ support (((RawCtxChainOwner.ownerImpl calls sender decode query).run owner).run state)) :
    OwnerEffect (ownerSeals sender query owner) owner.kernel result.1.2.kernel (logOf state) (logOf result.2) := by
  cases query with
  | inr raw =>
    have unfolded : (RawCtxChainOwner.ownerImpl calls sender decode (.inr raw)).run owner =
        if raw.isEmpty then pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) else
        match decode raw with
        | none => pure (RawCtxChainOwner.publish owner (owner.kernel, .None))
        | some frame =>
          if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then
            RawCtxChainOwner.publish owner <$> calls.receive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩
          else pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) := by
      simp only [RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run, bind_pure_comp]
      rfl
    rw [unfolded] at supported
    have rejected : ∀ result ∈ support ((pure (RawCtxChainOwner.publish owner (owner.kernel, .None)) :
        StateT σ ProbComp _).run state), OwnerEffect (ownerSeals sender (.inr raw) owner) owner.kernel result.1.2.kernel
          (logOf state) (logOf result.2) := by
      intro result reached
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      exact ⟨List.prefix_refl _, logged_nil _, Or.inl ⟨rfl, rfl⟩⟩
    split at supported
    · exact rejected result supported
    · split at supported
      · exact rejected result supported
      · split at supported
        · simp only [StateT.run_map, support_map, Set.mem_image] at supported
          obtain ⟨inner, innerSupported, rfl⟩ := supported
          obtain ⟨same, grows⟩ := receiveKeeps _ _ _ state inner innerSupported
          exact ⟨grows, logged_nil _, Or.inl ⟨rfl, same⟩⟩
        · exact rejected result supported
  | inl plaintext =>
    have unfolded : (RawCtxChainOwner.ownerImpl calls sender decode (.inl plaintext)).run owner =
        if plaintext.isEmpty then pure (none, owner) else
          (fun reply => (reply.2, { owner with kernel := reply.1 })) <$>
            calls.send owner.kernel ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ := by
      simp only [RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run, bind_pure_comp]
    rw [unfolded] at supported
    by_cases empty : plaintext.isEmpty = true
    · simp only [empty, ite_true, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨List.prefix_refl _, by simp [ownerSeals, empty, logged_nil], Or.inl ⟨by simp [ownerSeals, empty], rfl⟩⟩
    · simp only [empty, Bool.false_eq_true, ite_false, StateT.run_map, support_map, Set.mem_image] at supported
      obtain ⟨inner, innerSupported, rfl⟩ := supported
      have seals : ownerSeals sender (.inl plaintext) owner =
          sendChains owner.kernel ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ := by
        simp [ownerSeals, empty]
      rw [seals]
      rcases sendLogs _ _ state inner innerSupported with ⟨none, same, grows⟩ | ⟨single, known, grows⟩
      · rw [none]
        exact ⟨grows, logged_nil _, Or.inl ⟨rfl, by rw [same]⟩⟩
      · rw [single]
        exact ⟨(List.prefix_append _ _).trans grows, logged_single _ _ _ grows, Or.inr ⟨rfl, known⟩⟩

end OwnerFacts

section RoleFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {σ M P I D K : Type} (logOf : σ → Log) (calls : RawCtxChainOwner.Calls TKernel (StateT σ ProbComp))

/-- A tagged kernel with a known send chain. -/
def KnownSend (kernel : TKernel) : Prop := isHidden kernel.send_chain = false

/-- Every Server peer keeps its send chain or gets a known send chain. -/
def PeersStep (before after : ServerState TKernel M P) : Prop :=
  ∀ kid peer', after.server.peers kid = some peer' → ∃ peer, before.server.peers kid = some peer ∧
    (peer'.kernel.send_chain = peer.kernel.send_chain ∨ KnownSend peer'.kernel)

/-- A Server request appends to the log, logs its known seal chains, seals only existing peers' send chains and steps its peers. -/
theorem server_effect (receiveKeeps : ReceiveKeeps logOf calls) (sendLogs : SendLogs logOf calls)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (before : ServerState TKernel M P) (state : σ)
    (result : (RawCtxServerMixed.SourceSpec.Range query × ServerState TKernel M P) × σ)
    (supported : result ∈ support (((RawCtxGenericServer.serverImpl calls senderId route decode query).run before).run state)) :
    logOf state <+: logOf result.2 ∧ SealsLogged (serverSeals senderId query before) (logOf result.2) ∧
      (∀ chain ∈ serverSeals senderId query before, ∃ kid peer, before.server.peers kid = some peer ∧
        chain = peer.kernel.send_chain) ∧ PeersStep before result.1.2 := by
  have kept : ∀ peers : Std.U64 → Option (Peer TKernel P), (∀ kid peer', peers kid = some peer' → before.server.peers kid = some peer') →
      ∀ kid peer', peers kid = some peer' → ∃ peer, before.server.peers kid = some peer ∧
        (peer'.kernel.send_chain = peer.kernel.send_chain ∨ KnownSend peer'.kernel) :=
    fun peers same kid peer' found => ⟨peer', same kid peer' found, Or.inl rfl⟩
  rcases query with ⟨plaintext, kid⟩ | raw
  · change result ∈ support ((RawCtxGenericServer.sendServer calls senderId plaintext kid before).run state) at supported
    unfold RawCtxGenericServer.sendServer at supported
    cases associated : RawCtxGenericServer.peerAssociatedData before.server kid with
    | none =>
      simp only [associated, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨List.prefix_refl _, by simp [serverSeals, associated, logged_nil], by simp [serverSeals, associated],
        kept _ fun _ _ found => found⟩
    | some ad =>
      cases found : before.server.peers kid with
      | none =>
        simp only [associated, found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨List.prefix_refl _, by simp [serverSeals, associated, found, logged_nil],
          by simp [serverSeals, associated, found], kept _ fun _ _ found => found⟩
      | some peer =>
        simp only [associated, found, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at supported
        obtain ⟨inner, innerSupported, rfl⟩ := supported
        have effect := owner_effect logOf calls receiveKeeps sendLogs (senderId before.server.metadata) decode (.inl plaintext)
          (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) state inner innerSupported
        have seals : serverSeals senderId (.inl (plaintext, kid)) before =
            ownerSeals (senderId before.server.metadata) (.inl plaintext)
              (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) := by
          simp [serverSeals, associated, found]
        rw [seals]
        obtain ⟨grows, logs, kernelEffect⟩ := effect
        refine ⟨grows, logs, ?_, ?_⟩
        · intro chain listed
          rcases kernelEffect with ⟨none, _⟩ | ⟨single, _⟩
          · rw [none] at listed
            exact absurd listed (List.not_mem_nil)
          · rw [single, List.mem_singleton] at listed
            exact ⟨kid, peer, found, listed⟩
        · intro other peer' reached
          simp only [RawCtxGenericServer.putPeer] at reached
          by_cases same : other = kid
          · subst same
            simp only [Function.update_self, Option.some.injEq] at reached
            subst reached
            refine ⟨peer, found, ?_⟩
            rcases kernelEffect with ⟨_, equal⟩ | ⟨_, known⟩
            · exact Or.inl equal
            · exact Or.inr known
          · simp only [Function.update_of_ne same] at reached
            exact ⟨peer', reached, Or.inl rfl⟩
  · change result ∈ support ((RawCtxGenericServer.rawServer calls route decode raw before).run state) at supported
    unfold RawCtxGenericServer.rawServer at supported
    have noSeals : serverSeals senderId (.inr raw) before = [] := rfl
    rw [noSeals]
    cases routed : route raw with
    | none =>
      simp only [routed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨List.prefix_refl _, logged_nil _, by simp, kept _ fun _ _ found => found⟩
    | some kid =>
      cases associated : RawCtxGenericServer.peerAssociatedData before.server kid with
      | none =>
        simp only [routed, associated, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact ⟨List.prefix_refl _, logged_nil _, by simp, kept _ fun _ _ found => found⟩
      | some ad =>
        cases found : before.server.peers kid with
        | none =>
          simp only [routed, associated, found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact ⟨List.prefix_refl _, logged_nil _, by simp, kept _ fun _ _ found => found⟩
        | some peer =>
          simp only [routed, associated, found, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
            Set.mem_singleton_iff] at supported
          obtain ⟨inner, innerSupported, rfl⟩ := supported
          have effect := owner_effect logOf calls receiveKeeps sendLogs (senderId before.server.metadata) decode (.inr raw)
            (RawCtxGenericServer.selectedOwner kid ad peer before.rawAttempts) state inner innerSupported
          obtain ⟨grows, _, kernelEffect⟩ := effect
          refine ⟨grows, logged_nil _, by simp, ?_⟩
          intro other peer' reached
          simp only [RawCtxGenericServer.putPeer] at reached
          by_cases same : other = kid
          · subst same
            simp only [Function.update_self, Option.some.injEq] at reached
            subst reached
            refine ⟨peer, found, ?_⟩
            rcases kernelEffect with ⟨_, equal⟩ | ⟨impossible, _⟩
            · exact Or.inl equal
            · exact absurd impossible (by simp [ownerSeals])
          · simp only [Function.update_of_ne same] at reached
            exact ⟨peer', reached, Or.inl rfl⟩

end RoleFacts

section BeaconFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {σ M P I D K : Type} (logOf : σ → Log) (calls : RawCtxChainOwner.Calls TKernel (StateT σ ProbComp))

/-- The phase step of one Beacon request: an established kernel keeps its send chain unless it sealed and became known; other phases are unchanged and seal nothing. -/
def BeaconStep (seals : List Chain) (before after : BeaconState TKernel I D K) : Prop :=
  (∃ control ad kernel kernel', before.beacon.phase = .established control ad kernel ∧
      after.beacon.phase = .established control ad kernel' ∧
      ((seals = [] ∧ kernel'.send_chain = kernel.send_chain) ∨ (seals = [kernel.send_chain] ∧ KnownSend kernel'))) ∨
    (after.beacon.phase = before.beacon.phase ∧ seals = [])

/-- A Beacon request appends to the log, logs its known seal chains and steps its phase. -/
theorem beacon_effect (receiveKeeps : ReceiveKeeps logOf calls) (sendLogs : SendLogs logOf calls)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (before : BeaconState TKernel I D K)
    (state : σ) (result : (RawCtxMixedOwner.SourceSpec.Range query × BeaconState TKernel I D K) × σ)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode query).run before).run state)) :
    logOf state <+: logOf result.2 ∧ SealsLogged (beaconSeals query before) (logOf result.2) ∧
      BeaconStep (beaconSeals query before) before result.1.2 := by
  cases phase : before.beacon.phase with
  | established control ad kernel =>
    rw [RawCtxGenericBeacon.established calls decode query before control ad kernel phase] at supported
    simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    have seals : beaconSeals query before = ownerSeals before.beacon.identityKeyId query
        (RawCtxGenericBeacon.selected before control ad kernel) := by
      simp [beaconSeals, phase]
    obtain ⟨grows, logs, kernelEffect⟩ := owner_effect logOf calls receiveKeeps sendLogs before.beacon.identityKeyId decode query
      (RawCtxGenericBeacon.selected before control ad kernel) state inner innerSupported
    rw [seals]
    exact ⟨grows, logs, Or.inl ⟨control, ad, kernel, inner.1.2.kernel, phase, rfl, kernelEffect⟩⟩
  | fresh _ _ _ | freshWithCoins _ _ _ _ | initSent _ _ _ _ | aborted _ =>
    simp only [RawCtxGenericBeacon.impl, StateT.run, phase] at supported
    subst supported
    have seals : beaconSeals query before = [] := by simp [beaconSeals, phase]
    rw [seals]
    refine ⟨List.prefix_refl _, logged_nil _, Or.inr ⟨?_, rfl⟩⟩
    cases query <;> rfl

end BeaconFacts

section FamilyFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {σ M P I D K : Type} {S B : Nat} (logOf : σ → Log) (calls : RawCtxChainOwner.Calls TKernel (StateT σ ProbComp))
  (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT σ ProbComp))

/-- Public services only append to the log. -/
def PublicKeeps : Prop :=
  ∀ query state, ∀ result ∈ support ((publicCalls query).run state), logOf state <+: logOf result.2

/-- The role step of one family request: exactly the addressed Server steps its peers, or exactly the addressed Beacon steps its phase, or nothing changes. -/
def FamilyStep (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (before after : Roles TKernel M P I D K S B) : Prop :=
  match query with
  | .inl ⟨index, request⟩ => after.2 = before.2 ∧ (∀ other, other ≠ index → after.1 other = before.1 other) ∧
      PeersStep (before.1 index) (after.1 index) ∧
      ∀ chain ∈ serverSeals sender request (before.1 index), ∃ kid peer, (before.1 index).server.peers kid = some peer ∧
        chain = peer.kernel.send_chain
  | .inr (.inl ⟨index, request⟩) => after.1 = before.1 ∧ (∀ other, other ≠ index → after.2 other = before.2 other) ∧
      BeaconStep (beaconSeals request (before.2 index)) (before.2 index) (after.2 index)
  | .inr (.inr _) => after = before

/-- A family request appends to the log, logs its known seal chains and steps the roles. -/
theorem family_effect (receiveKeeps : ReceiveKeeps logOf calls) (sendLogs : SendLogs logOf calls)
    (publicKeeps : PublicKeeps logOf publicCalls)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles TKernel M P I D K S B) (state : σ)
    (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles TKernel M P I D K S B) × σ)
    (supported : result ∈ support (((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run before).run
      state)) :
    logOf state <+: logOf result.2 ∧ SealsLogged (familySeals sender query before) (logOf result.2) ∧
      FamilyStep sender query before result.1.2 := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · have unfolded : ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode (.inl ⟨index, request⟩)).run before).run
        state = (show (RawCtxServerMixed.SourceSpec.Range request × ServerState TKernel M P) × σ →
            ((RawCtxProtocolRoles.SourceSpec S B).Range (.inl ⟨index, request⟩) × Roles TKernel M P I D K S B) × σ from
          fun inner => ((inner.1.1, (Function.update before.1 index inner.1.2, before.2)), inner.2)) <$>
          ((RawCtxGenericServer.serverImpl calls sender route decode request).run (before.1 index)).run state := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [unfolded, support_map] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    obtain ⟨grows, logs, seals, peers⟩ := server_effect logOf calls receiveKeeps sendLogs sender route decode request
      (before.1 index) state inner innerSupported
    refine ⟨grows, logs, rfl, fun other different => ?_, ?_, seals⟩
    · exact Function.update_of_ne different _ _
    · simpa using peers
  · have unfolded : ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode (.inr (.inl ⟨index, request⟩))).run
        before).run state = (show (RawCtxMixedOwner.SourceSpec.Range request × BeaconState TKernel I D K) × σ →
            ((RawCtxProtocolRoles.SourceSpec S B).Range (.inr (.inl ⟨index, request⟩)) × Roles TKernel M P I D K S B) × σ from
          fun inner => ((inner.1.1, (before.1, Function.update before.2 index inner.1.2)), inner.2)) <$>
          ((RawCtxGenericBeacon.impl calls decode request).run (before.2 index)).run state := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [unfolded, support_map] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    obtain ⟨grows, logs, step⟩ := beacon_effect logOf calls receiveKeeps sendLogs decode request (before.2 index) state inner
      innerSupported
    refine ⟨grows, logs, rfl, fun other different => ?_, ?_⟩
    · exact Function.update_of_ne different _ _
    · simpa using step
  · have unfolded : ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode (.inr (.inr request))).run
        before).run state = (show RawCtxServerServices.PublicSpec.Range request × σ →
            ((RawCtxProtocolRoles.SourceSpec S B).Range (.inr (.inr request)) × Roles TKernel M P I D K S B) × σ from
          fun inner => ((inner.1, before), inner.2)) <$> (publicCalls request).run state := by
      rw [map_eq_bind_pure_comp]
      rfl
    rw [unfolded, support_map] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    exact ⟨publicKeeps request state inner innerSupported, logged_nil _, rfl⟩

end FamilyFacts

section Good
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {M P I D K : Type} {S B : Nat} (first : Fin B) (Markable : K → Prop)

/-- One if the first Beacon is established with a hidden send chain. -/
def firstHidden (roles : Roles TKernel M P I D K S B) : Nat :=
  match (roles.2 first).beacon.phase with
  | .established _ _ kernel => (isHidden kernel.send_chain).toNat
  | _ => 0

/-- One if the first Beacon waits for its finish with a markable KEM handle. -/
noncomputable def firstMarkable (roles : Roles TKernel M P I D K S B) : Nat :=
  match (roles.2 first).beacon.phase with
  | .initSent _ _ _ kem => @ite _ (Markable kem) (Classical.propDecidable _) 1 0
  | _ => 0

/-- The tagged-world invariant: every Server peer and every Beacon other than the first has a known send chain, only the first Beacon can be marked, the hidden send chain occurs at most once among seal chains, the first Beacon and a pending marked finish, and every known seal chain is logged. -/
structure Good (roles : Roles TKernel M P I D K S B) (seals : List Chain) (log : Log) : Prop where
  servers : ∀ index kid peer, (roles.1 index).server.peers kid = some peer → KnownSend peer.kernel
  beacons : ∀ index, index ≠ first → ∀ control ad kernel,
    (roles.2 index).beacon.phase = .established control ad kernel → KnownSend kernel
  unmarkable : ∀ index, index ≠ first → ∀ control prekey oneTime kem,
    (roles.2 index).beacon.phase = .initSent control prekey oneTime kem → ¬ Markable kem
  once : hiddenCount seals + firstHidden first roles + firstMarkable first Markable roles ≤ 1
  logged : SealsLogged seals log

/-- The hidden count of appended seal lists is the sum of their hidden counts. -/
theorem hidden_append (first second : List Chain) : hiddenCount (first ++ second) = hiddenCount first + hiddenCount second := by
  simp [hiddenCount, List.countP_append]

/-- Logged seal chains stay logged when the log is extended. -/
theorem logged_mono (seals : List Chain) (log log' : Log) (logged : SealsLogged seals log) (grows : log <+: log') :
    SealsLogged seals log' := fun chain listed => grows.subset (logged chain listed)

/-- Two logged lists of seal chains give a logged concatenation. -/
theorem logged_append (first second : List Chain) (log : Log) (left : SealsLogged first log) (right : SealsLogged second log) :
    SealsLogged (first ++ second) log := by
  intro chain listed
  rcases List.mem_append.mp listed with inFirst | inSecond
  · exact left chain inFirst
  · exact right chain inSecond

/-- A list of known seal chains has hidden count zero. -/
theorem known_count (seals : List Chain) (known : ∀ chain ∈ seals, isHidden chain = false) : hiddenCount seals = 0 := by
  simp only [hiddenCount, List.countP_eq_zero]
  intro chain listed
  simp [known chain listed]

variable (logOf : Log → Log)

/-- A family step preserves the invariant, with the appended seal chains and a grown log. -/
theorem good_family (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (before after : Roles TKernel M P I D K S B) (seals : List Chain) (log log' : Log)
    (good : Good first Markable before seals log) (step : FamilyStep sender query before after)
    (grows : log <+: log') (newLogged : SealsLogged (familySeals sender query before) log') :
    Good first Markable after (seals ++ familySeals sender query before) log' := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · obtain ⟨beacons, others, peers, sealed⟩ := step
    have noHidden : hiddenCount (familySeals sender (.inl ⟨index, request⟩) before) = 0 := by
      apply known_count
      intro chain listed
      obtain ⟨kid, peer, found, rfl⟩ := sealed chain listed
      exact good.servers index kid peer found
    have hiddenSame : firstHidden first after = firstHidden first before := by simp [firstHidden, beacons]
    have markSame : firstMarkable first Markable after = firstMarkable first Markable before := by simp [firstMarkable, beacons]
    refine ⟨fun server kid peer' found => ?_, fun other different control ad kernel phase => ?_,
      fun other different control prekey oneTime kem phase => ?_, ?_, ?_⟩
    · by_cases same : server = index
      · subst same
        obtain ⟨peer, previous, choice⟩ := peers kid peer' found
        rcases choice with equal | known
        · unfold KnownSend
          rw [equal]
          exact good.servers server kid peer previous
        · exact known
      · rw [others server same] at found
        exact good.servers server kid peer' found
    · rw [beacons] at phase
      exact good.beacons other different control ad kernel phase
    · rw [beacons] at phase
      exact good.unmarkable other different control prekey oneTime kem phase
    · have := good.once
      rw [hidden_append, noHidden, hiddenSame, markSame]
      omega
    · exact logged_append _ _ _ (logged_mono _ _ _ good.logged grows) newLogged
  · obtain ⟨servers, others, beaconStep⟩ := step
    have familyIs : familySeals sender (.inr (.inl ⟨index, request⟩)) before = beaconSeals request (before.2 index) := rfl
    rw [familyIs] at newLogged ⊢
    refine ⟨fun server kid peer found => ?_, fun other different control ad kernel phase => ?_,
      fun other different control prekey oneTime kem phase => ?_, ?_, ?_⟩
    · rw [servers] at found
      exact good.servers server kid peer found
    · by_cases same : other = index
      · subst same
        rcases beaconStep with ⟨control', ad', kernel', kernel'', previous, current, choice⟩ | ⟨unchanged, _⟩
        · rw [current] at phase
          cases phase
          have previousKnown := good.beacons other different _ _ kernel' previous
          rcases choice with ⟨_, equal⟩ | ⟨_, known⟩
          · unfold KnownSend
            rw [equal]
            exact previousKnown
          · exact known
        · rw [unchanged] at phase
          exact good.beacons other different control ad kernel phase
      · rw [others other same] at phase
        exact good.beacons other different control ad kernel phase
    · by_cases same : other = index
      · subst same
        rcases beaconStep with ⟨control', ad', kernel', kernel'', previous, current, _⟩ | ⟨unchanged, _⟩
        · rw [current] at phase
          cases phase
        · rw [unchanged] at phase
          exact good.unmarkable other different control prekey oneTime kem phase
      · rw [others other same] at phase
        exact good.unmarkable other different control prekey oneTime kem phase
    · have once := good.once
      by_cases same : first = index
      · subst same
        rcases beaconStep with ⟨control', ad', kernel', kernel'', previous, current, choice⟩ | ⟨unchanged, sealsNil⟩
        · have hiddenBefore : firstHidden first before = (isHidden kernel'.send_chain).toNat := by simp [firstHidden, previous]
          have markBefore : firstMarkable first Markable before = 0 := by simp [firstMarkable, previous]
          have markAfter : firstMarkable first Markable after = 0 := by simp [firstMarkable, current]
          rcases choice with ⟨sealsNil, equal⟩ | ⟨sealsOne, known⟩
          · have hiddenAfter : firstHidden first after = (isHidden kernel'.send_chain).toNat := by
              simp [firstHidden, current, equal]
            rw [hidden_append, sealsNil, hiddenAfter, markAfter]
            rw [hiddenBefore, markBefore] at once
            simp [hiddenCount] at once ⊢
            omega
          · have hiddenAfter : firstHidden first after = 0 := by
              simp only [firstHidden, current]
              unfold KnownSend at known
              simp [known]
            rw [hidden_append, sealsOne, hiddenAfter, markAfter]
            rw [hiddenBefore, markBefore] at once
            cases hidden : isHidden kernel'.send_chain <;> simp [hiddenCount, hidden] at once ⊢ <;> omega
        · have hiddenSame : firstHidden first after = firstHidden first before := by simp [firstHidden, unchanged]
          have markSame : firstMarkable first Markable after = firstMarkable first Markable before := by
            simp [firstMarkable, unchanged]
          rw [hidden_append, sealsNil, hiddenSame, markSame]
          simpa [hiddenCount] using once
      · have hiddenSame : firstHidden first after = firstHidden first before := by
          simp [firstHidden, others first same]
        have markSame : firstMarkable first Markable after = firstMarkable first Markable before := by
          simp [firstMarkable, others first same]
        have noHidden : hiddenCount (beaconSeals request (before.2 index)) = 0 := by
          apply known_count
          intro chain listed
          rcases beaconStep with ⟨control', ad', kernel', kernel'', previous, current, choice⟩ | ⟨unchanged, sealsNil⟩
          · rcases choice with ⟨sealsNil, _⟩ | ⟨sealsOne, _⟩
            · rw [sealsNil] at listed
              exact absurd listed (List.not_mem_nil)
            · rw [sealsOne, List.mem_singleton] at listed
              subst listed
              exact good.beacons index (Ne.symm same) control' ad' kernel' previous
          · rw [sealsNil] at listed
            exact absurd listed (List.not_mem_nil)
        rw [hidden_append, noHidden, hiddenSame, markSame]
        omega
    · exact logged_append _ _ _ (logged_mono _ _ _ good.logged grows) newLogged
  · have unchanged : after = before := step
    have noSeals : familySeals sender (.inr (.inr request)) before = [] := rfl
    rw [unchanged, noSeals, List.append_nil]
    exact ⟨good.servers, good.beacons, good.unmarkable, good.once, logged_mono _ _ _ good.logged grows⟩

end Good

section GoodWorld
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (first : Fin B) (Markable : K → Prop)

/-- The invariant of a tagged world state. -/
def GoodState (state : TState M P I D K A N C S B) : Prop :=
  Good first Markable state.front.roles state.seals state.shared.2

/-- The tagged calls keep send chains on receive. -/
theorem tagged_receive_keeps : ReceiveKeeps (Prod.snd : RawCtxSharedPrimitive.SharedState A × Log → Log)
    (taggedCalls source writer prior key nonce next) :=
  fun kernel sequence context state result supported =>
    tagged_receive source writer prior key nonce next kernel sequence context state result supported

/-- The tagged calls log the send chains of their sends. -/
theorem tagged_send_logs : SendLogs (Prod.snd : RawCtxSharedPrimitive.SharedState A × Log → Log)
    (taggedCalls source writer prior key nonce next) :=
  fun kernel context state result supported =>
    tagged_send source writer prior key nonce next kernel context state result supported

/-- The tagged public services keep the log. -/
theorem tagged_public_keeps : PublicKeeps (Prod.snd : RawCtxSharedPrimitive.SharedState A × Log → Log)
    (fun query => simulateQ (taggedLabels source writer prior key nonce next) (publicInject query)) := by
  intro query state result supported
  simp only [publicInject, simulateQ_spec_query] at supported
  exact label_prefix source writer prior key nonce next (.inr (.inr query)) state result supported

/-- A tagged record keeps the invariant. -/
theorem good_record (request : (RawCtxProtocolRoles.SourceSpec S B).Domain) (state : TState M P I D K A N C S B)
    (good : GoodState first Markable state)
    (result : Option ((RawCtxProtocolRoles.SourceSpec S B).Range request) × TState M P I D K A N C S B)
    (supported : result ∈ support ((taggedRecord source writer prior key nonce next sender route decode request).run state)) :
    GoodState first Markable result.2 := by
  simp only [taggedRecord, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  rw [symbolicStep, RawCtxGenericFamilyInterpretation.step_interpretation] at innerSupported
  obtain ⟨grows, logs, step⟩ := family_effect Prod.snd (taggedCalls source writer prior key nonce next) _
    (tagged_receive_keeps source writer prior key nonce next) (tagged_send_logs source writer prior key nonce next)
    (tagged_public_keeps source writer prior key nonce next) sender route decode request state.front.roles state.shared inner
    innerSupported
  exact good_family first Markable sender request state.front.roles inner.1.2 state.seals state.shared.2 inner.2.2 good step grows logs

end GoodWorld

section FinishEffect
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily

/-- Every supported result of a stateful computation from a given state satisfies a predicate. -/
def Reaches {σ β : Type} (work : StateT σ ProbComp β) (state : σ) (holds : β × σ → Prop) : Prop :=
  ∀ result ∈ support (work.run state), holds result

/-- A return reaches every property that holds of its value and state. -/
theorem reaches_pure {σ β : Type} (value : β) (state : σ) (holds : β × σ → Prop) (valid : holds (value, state)) :
    Reaches (pure value : StateT σ ProbComp β) state holds := by
  intro result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact valid

/-- A bind reaches a property if its continuations reach it from every reached intermediate result. -/
theorem reaches_bind {σ β γ : Type} (work : StateT σ ProbComp β) (continuation : β → StateT σ ProbComp γ) (state : σ)
    (holds : γ × σ → Prop) (first : Reaches work state fun middle => Reaches (continuation middle.1) middle.2 holds) :
    Reaches (work >>= continuation) state holds := by
  intro result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, middleSupported, rest⟩ := supported
  exact first middle middleSupported result rest

/-- A shared-state service run beside an unchanged log reaches every property of its own results with the log unchanged. -/
theorem reaches_keep {A β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β)
    (state : RawCtxSharedPrimitive.SharedState A × Log) (holds : β × (RawCtxSharedPrimitive.SharedState A × Log) → Prop)
    (valid : ∀ inner ∈ support (work.run state.1), holds (inner.1, (inner.2, state.2))) : Reaches (keepLog work) state holds := by
  intro result supported
  simp only [keepLog, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  exact valid inner innerSupported

/-- Reached properties are closed under implication. -/
theorem reaches_mono {σ β : Type} (work : StateT σ ProbComp β) (state : σ) (holds holds' : β × σ → Prop)
    (reached : Reaches work state holds) (implies : ∀ result, holds result → holds' result) : Reaches work state holds' :=
  fun result supported => implies result (reached result supported)

/-- A staged registration carries the opened owner's kernel. -/
theorem opening_kernel {Kernel : Type} (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : Kernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : PqxdhInitialGenericBeacon.Staged Kernel)
    (found : PqxdhInitialGenericBeacon.afterOpening candidate kernel reply = some staged) : staged.kernel = kernel := by
  unfold PqxdhInitialGenericBeacon.afterOpening at found
  split at found
  · cases found
  · split_ifs at found
    · split at found
      · cases found
      · cases found
        rfl

/-- A finish attempt aborts, or establishes exactly the staged kernel. -/
theorem finish_result {Kernel I D K : Type} (control : pqxdh.BeaconInitSent)
    (state : BeaconState Kernel I D K) (staged : Option (PqxdhInitialGenericBeacon.Staged Kernel)) :
    (∃ aborted, (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase = .aborted aborted) ∨
      ∃ value established ad, staged = some value ∧
        (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase = .established established ad value.kernel := by
  unfold PqxdhInitialGenericBeacon.finish
  rcases staged with _ | value
  · exact Or.inl ⟨_, rfl⟩
  · simp only
    split_ifs
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨value, _, _, rfl, rfl⟩

variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)
    (Markable : K → Prop)

/-- The phase step of a finish: a pending Beacon ends aborted or established with a known send chain, or with a hidden send chain only for a markable KEM handle; other phases are unchanged. -/
def FinishStep (before after : BeaconState TKernel I D K) : Prop :=
  (∀ control prekey oneTime kem, before.beacon.phase = .initSent control prekey oneTime kem →
    (∃ aborted, after.beacon.phase = .aborted aborted) ∨
      ∃ established ad kernel, after.beacon.phase = .established established ad kernel ∧ (KnownSend kernel ∨ Markable kem)) ∧
    ((∀ control prekey oneTime kem, before.beacon.phase ≠ .initSent control prekey oneTime kem) →
      after.beacon.phase = before.beacon.phase)

/-- The tagged first receive stages the initializer kernel's send chain and only appends to the log. -/
theorem stage_reaches (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : TKernel) (raw : Pqxdh.Bytes)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) :
    Reaches (taggedStage source writer prior key nonce next decode candidate kernel raw) state fun result =>
      state.2 <+: result.2.2 ∧ ∀ staged, result.1 = some staged → staged.kernel.send_chain = kernel.send_chain := by
  intro result supported
  simp only [taggedStage, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  obtain ⟨grows, _, effect⟩ := owner_effect Prod.snd (taggedCalls source writer prior key nonce next)
    (tagged_receive_keeps source writer prior key nonce next) (tagged_send_logs source writer prior key nonce next)
    candidate.server_binding.identity_key_id decode (.inr raw) (PqxdhInitialGenericBeacon.localOwner candidate kernel) state inner
    innerSupported
  refine ⟨grows, fun staged found => ?_⟩
  rw [opening_kernel candidate _ _ staged found]
  rcases effect with ⟨_, same⟩ | ⟨impossible, _⟩
  · exact same
  · exact absurd impossible (by simp [ownerSeals])

end FinishEffect

section FinishEffect2
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {ι I D K X Response A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)
    (Markable : K → Prop)

/-- The known tagged image of a native kernel has a known send chain. -/
theorem known_send (kernel : PqxdhInitialPendingPost.KernelOf RatchetChain) :
    KnownSend (knownTagged (PqxdhSelectedMessageBeacon.knownKernel kernel)) := rfl

/-- The tagged finish only appends to the log and steps the Beacon, given that a marked preparation needs a markable KEM handle. -/
theorem finish_effect
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux (.inl query))
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true → Markable kem)
    (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K) (state : RawCtxSharedPrimitive.SharedState (Local A N C) × Log) :
    Reaches (taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
      raw before) state fun result => state.2 <+: result.2.2 ∧ FinishStep Markable before result.1.2 := by
  have aborts : ∀ (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K) (current : RawCtxSharedPrimitive.SharedState (Local A N C)),
      before.beacon.phase = .initSent control prekey oneTime kem →
      Reaches (pure (PqxdhInitialGenericBeacon.finish control before none)) (current, state.2)
        fun result => state.2 <+: result.2.2 ∧ FinishStep Markable before result.1.2 := by
    intro control prekey oneTime kem current phase
    refine reaches_pure _ _ _ ⟨List.prefix_refl _, fun _ _ _ _ _ => Or.inl ⟨_, rfl⟩, fun notSent => absurd phase (notSent _ _ _ _)⟩
  unfold taggedFinish
  cases phase : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    dsimp only
    refine reaches_bind _ _ _ _ (reaches_keep _ _ _ fun prepared preparedSupported => ?_)
    obtain ⟨preparedValue, preparedState⟩ := prepared
    cases preparedValue with
    | none => exact aborts control prekey oneTime kem preparedState phase
    | some pending =>
      dsimp only
      refine reaches_bind _ _ _ _ (reaches_keep _ _ _ fun initialized initializedSupported => ?_)
      obtain ⟨kernelValue, kernelState⟩ := initialized
      cases kernelValue with
      | none => exact aborts control prekey oneTime kem kernelState phase
      | some kernel =>
        have kernelFact : KnownSend kernel ∨ Markable kem := by
          cases selected : PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root with
          | true =>
            exact Or.inr (markable control before.beacon.identity prekey oneTime kem raw state.1 _ preparedSupported pending rfl
              selected)
          | false =>
            simp only [taggedInitialCall, selected, Bool.false_eq_true, ite_false, StateT.run_map, support_map,
              Set.mem_image] at initializedSupported
            obtain ⟨native, _, equal⟩ := initializedSupported
            simp only [Prod.mk.injEq] at equal
            obtain ⟨kernelEqual, _⟩ := equal
            cases found : native.1 with
            | none => rw [found] at kernelEqual; cases kernelEqual
            | some nativeKernel =>
              rw [found] at kernelEqual
              simp only [Option.map_some, Option.some.injEq] at kernelEqual
              rw [← kernelEqual]
              exact Or.inl (known_send nativeKernel)
        dsimp only
        refine reaches_bind _ _ _ _ (reaches_keep _ _ _ fun replied _ => ?_)
        obtain ⟨replyValue, replyState⟩ := replied
        cases replyValue with
        | none =>
          dsimp only
          refine reaches_bind _ _ _ _ (reaches_pure _ _ _ ?_)
          exact reaches_pure _ _ _ ⟨List.prefix_refl _, fun _ _ _ _ _ => Or.inl ⟨_, rfl⟩,
            fun notSent => absurd phase (notSent _ _ _ _)⟩
        | some delivered =>
          dsimp only
          refine reaches_bind _ _ _ _ ?_
          refine reaches_mono _ _ _ _ (stage_reaches source writer prior key nonce next decode
            (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata) kernel delivered (replyState, state.2)) ?_
          intro staged ⟨grows, kernelOf⟩
          refine reaches_pure _ _ _ ⟨grows, fun control' prekey' oneTime' kem' phase' => ?_, fun notSent => absurd phase (notSent _ _ _ _)⟩
          rw [phase] at phase'
          cases phase'
          rcases finish_result control before staged.1 with ⟨aborted, abortedPhase⟩ | ⟨value, established, ad, found, establishedPhase⟩
          · exact Or.inl ⟨aborted, abortedPhase⟩
          · refine Or.inr ⟨established, ad, value.kernel, establishedPhase, ?_⟩
            rcases kernelFact with known | markableKem
            · left
              unfold KnownSend at known ⊢
              rw [kernelOf value found]
              exact known
            · exact Or.inr markableKem
  | fresh _ _ _ | freshWithCoins _ _ _ _ | established _ _ _ | aborted _ =>
    dsimp only
    refine reaches_pure _ _ _ ⟨List.prefix_refl _, ?_, fun _ => rfl⟩
    intro control' prekey' oneTime' kem' impossible
    rw [phase] at impossible
    cases impossible

end FinishEffect2

section GoodStep
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)
    (first : Fin B) (Markable : K → Prop)

/-- A tagged finish keeps the invariant. -/
theorem good_finish
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux (.inl query))
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true → Markable kem)
    (index : Fin B) (raw : Pqxdh.Bytes) (state : TState M P I D K A N C S B) (good : GoodState first Markable state)
    (result : Option (Option Pqxdh.Bytes) × TState M P I D K A N C S B)
    (supported : result ∈ support ((taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux
      fixed selectedMessage other index raw).run state)) :
    GoodState first Markable result.2 := by
  simp only [taggedFinishOp, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  obtain ⟨grows, step⟩ := finish_effect source writer prior key nonce next decode pre application initialW selector aux fixed
    selectedMessage other Markable markable raw (state.front.roles.2 index) state.shared inner innerSupported
  obtain ⟨sent, unsent⟩ := step
  have atIndex : ∀ other, other ≠ index → Function.update state.front.roles.2 index inner.1.2 other = state.front.roles.2 other :=
    fun other different => Function.update_of_ne different _ _
  refine ⟨good.servers, fun other different control ad kernel phase => ?_, fun other different control prekey oneTime kem phase => ?_,
    ?_, logged_mono _ _ _ good.logged grows⟩
  · by_cases same : other = index
    · subst same
      simp only [Function.update_self] at phase
      by_cases pending : ∃ control prekey oneTime kem, (state.front.roles.2 other).beacon.phase = .initSent control prekey oneTime kem
      · obtain ⟨control', prekey', oneTime', kem', previous⟩ := pending
        rcases sent control' prekey' oneTime' kem' previous with ⟨aborted, abortedPhase⟩ | ⟨established, ad', kernel', current, choice⟩
        · rw [abortedPhase] at phase
          cases phase
        · rw [current] at phase
          cases phase
          rcases choice with known | markableKem
          · exact known
          · exact absurd markableKem (good.unmarkable other different control' prekey' oneTime' kem' previous)
      · have unchanged := unsent fun control prekey oneTime kem found => pending ⟨control, prekey, oneTime, kem, found⟩
        rw [unchanged] at phase
        exact good.beacons other different control ad kernel phase
    · simp only [atIndex other same] at phase
      exact good.beacons other different control ad kernel phase
  · by_cases same : other = index
    · subst same
      simp only [Function.update_self] at phase
      by_cases pending : ∃ control prekey oneTime kem, (state.front.roles.2 other).beacon.phase = .initSent control prekey oneTime kem
      · obtain ⟨control', prekey', oneTime', kem', previous⟩ := pending
        rcases sent control' prekey' oneTime' kem' previous with ⟨aborted, abortedPhase⟩ | ⟨established, ad', kernel', current, _⟩
        · rw [abortedPhase] at phase
          cases phase
        · rw [current] at phase
          cases phase
      · have unchanged := unsent fun control prekey oneTime kem found => pending ⟨control, prekey, oneTime, kem, found⟩
        rw [unchanged] at phase
        exact good.unmarkable other different control prekey oneTime kem phase
    · simp only [atIndex other same] at phase
      exact good.unmarkable other different control prekey oneTime kem phase
  · have once := good.once
    by_cases same : first = index
    · subst same
      change hiddenCount state.seals + firstHidden first (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) +
        firstMarkable first Markable (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) ≤ 1
      by_cases pending : ∃ control prekey oneTime kem, (state.front.roles.2 first).beacon.phase = .initSent control prekey oneTime kem
      · obtain ⟨control', prekey', oneTime', kem', previous⟩ := pending
        have hiddenBefore : firstHidden first state.front.roles = 0 := by simp [firstHidden, previous]
        have markBefore : firstMarkable first Markable state.front.roles =
            @ite _ (Markable kem') (Classical.propDecidable _) 1 0 := by simp [firstMarkable, previous]
        rw [hiddenBefore, markBefore] at once
        rcases sent control' prekey' oneTime' kem' previous with ⟨aborted, abortedPhase⟩ | ⟨established, ad', kernel', current, choice⟩
        · simp [firstHidden, firstMarkable, abortedPhase]
          omega
        · have markAfter : firstMarkable first Markable (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) = 0 := by
            simp [firstMarkable, current]
          rw [markAfter]
          rcases choice with known | markableKem
          · have hiddenAfter : firstHidden first (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) = 0 := by
              simp only [firstHidden, Function.update_self, current]
              unfold KnownSend at known
              simp [known]
            rw [hiddenAfter]
            omega
          · rw [@ite_eq_left _ (Classical.propDecidable _) markableKem] at once
            have bounded : firstHidden first (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) ≤ 1 := by
              simp only [firstHidden, Function.update_self, current]
              exact Bool.toNat_le _
            omega
      · have unchanged := unsent fun control prekey oneTime kem found => pending ⟨control, prekey, oneTime, kem, found⟩
        have hiddenSame : firstHidden first (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) =
            firstHidden first state.front.roles := by simp [firstHidden, unchanged]
        have markSame : firstMarkable first Markable (state.front.roles.1, Function.update state.front.roles.2 first inner.1.2) =
            firstMarkable first Markable state.front.roles := by simp [firstMarkable, unchanged]
        rw [hiddenSame, markSame]
        exact once
    · change hiddenCount state.seals + firstHidden first (state.front.roles.1, Function.update state.front.roles.2 index inner.1.2) +
        firstMarkable first Markable (state.front.roles.1, Function.update state.front.roles.2 index inner.1.2) ≤ 1
      have hiddenSame : firstHidden first (state.front.roles.1, Function.update state.front.roles.2 index inner.1.2) =
          firstHidden first state.front.roles := by simp [firstHidden, atIndex first same]
      have markSame : firstMarkable first Markable (state.front.roles.1, Function.update state.front.roles.2 index inner.1.2) =
          firstMarkable first Markable state.front.roles := by simp [firstMarkable, atIndex first same]
      rw [hiddenSame, markSame]
      exact once

/-- Every operation of the tagged world keeps the invariant. -/
theorem good_step
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux (.inl query))
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true → Markable kem)
    (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (state : TState M P I D K A N C S B)
    (good : GoodState first Markable state)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × TState M P I D K A N C S B)
    (supported : result ∈ support ((world source writer prior key nonce next sender route decode pre application initialW selector aux
      (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other)
      query).run state)) :
    GoodState first Markable result.2 := by
  rcases query with ((request | request) | request) | ⟨index, raw⟩
  · exact good_record source writer prior key nonce next sender route decode first Markable request state good result supported
  · simp only [world, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact good
  · simp only [world, taggedSelector, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact good
  · exact good_finish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other
      first Markable markable index raw state good result supported

end GoodStep

section PostBound
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)
    (first : Fin B) (Markable : K → Prop)

/-- The restricted repetition event of the history-extended source post (two ordered seals at the selected chain, selected chain undisclosed) has at most the probability that the selected value is logged by the tagged world, from represented start states satisfying the tagged invariant. The premises are the initializer and preparation facts of the actual callbacks, discharged separately. -/
theorem post_bound {Result : Type} (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ start : RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache), ∀ result ∈ support
        ((PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialC selector aux
          (.inr (.inr (.inl secrets)))).run start),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip start.1 ∧ result.2.2 = start.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux (.inl query))
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true → Markable kem)
    (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (start : Concrete M P I D K A N RootOracle.QueryCache S B) (tagged : TState M P I D K A N RootOracle.QueryCache S B)
    (represents : Represents target start tagged) (good : GoodState first Markable tagged) :
    Pr[fun result => RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1 ∧
        PqxdhFirstBeaconRecordIntegrity.Undisclosed target [] [] result.2.2 |
      (simulateQ (PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initialC selector aux source writer prior
        none key target nonce next sender route decode) client).run start] ≤
    Pr[fun result => Exposed target result.2 |
      (simulateQ (world source writer prior key nonce next sender route decode pre application initialW selector aux
        (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other))
        client).run tagged] := by
  refine probEvent_le_of_relTriple (post_coupled source writer prior key nonce next sender route decode pre application initialC selector
    aux initialW (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage
      other) target (GoodState first Markable)
    (good_step source writer prior key nonce next sender route decode pre application initialW selector aux fixed selectedMessage other
      first Markable markable)
    (fun index raw left right leftRepresents _ _ _ => finish_step source writer prior key nonce next sender route decode pre application
      selector aux fixed selectedMessage other initialC initialW target marked unmarked index raw left right leftRepresents)
    (finish_keeps source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other target)
    client start tagged represents good) ?_
  intro left right held holds
  obtain ⟨repeated, undisclosed⟩ := holds
  rcases held with disclosed | exposed | ⟨_, leftRepresents, rightGood⟩
  · exact absurd disclosed (undisclosed _ (List.mem_singleton_self _))
  · exact exposed
  · by_contra fresh
    have once : hiddenCount right.2.seals ≤ 1 := by
      have := rightGood.once
      omega
    exact repeated_impossible target left.2.1 right.2.seals right.2.shared.2 leftRepresents.2.2.2.2 rightGood.logged once fresh
      repeated

end PostBound

section ServerKernel
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxChainInterpretation RawCtxMaterialInterpretation

/-- The zero-state tagged Server constructor: known send chain, hidden receive chain. -/
noncomputable def serverBase (other : RootOutput) : RefinedRatchet Chain Chain RatchetMaterial :=
  (new_total (.known (RawCtxFreshChainCut.concreteChain other)) .hidden).choose

/-- The tagged Server kernel of the initializer response `other ++ target`, with all cached keys known. -/
noncomputable def serverKernel (other : RootOutput) : TKernel := mapRefined RawCtxSelectedMessageKey.Slot.known (serverBase other)

/-- The Server kernel of the 64-byte initializer response `other ++ target` is the hidden-receive tagged kernel at `target`. -/
theorem server_kernel (other target : RootOutput) :
    PqxdhSelectedFirstRecord.initialKernel (RawCtxSelectedInitialConstructor.response64 (other ++ target)) =
      ok (mapKernel target (serverKernel other)) := by
  have base := (new_total (.known (RawCtxFreshChainCut.concreteChain other)) .hidden).choose_spec
  have split := RawCtxSelectedInitialConstructor.from64_initial (false, PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0))
    other target
  simp only [RawCtxSelectedInitialConstructor.from64, Bool.false_eq_true, ite_false, RawCtxSelectedInitialConstructor.initial,
    RawCtxSelectedInitialConstructor.sendSlot, RawCtxSelectedInitialConstructor.receiveSlot] at split
  rw [← RawCtxSelectedInitialConstructor.new_map] at split
  change _ = ConcreteRatchetKernel.new (RawCtxFreshChainCut.concreteChain other) (RawCtxFreshChainCut.concreteChain target) at split
  have mapped := RawCtxSelectedInitialConstructor.new_map (RawCtxFreshChainCut.concreteChain target)
    (.known (RawCtxFreshChainCut.concreteChain other)) .hidden
  change ConcreteRatchetKernel.new (RawCtxFreshChainCut.concreteChain other) (RawCtxFreshChainCut.concreteChain target) = _ at mapped
  rw [mapped, base] at split
  have kernelOf : PqxdhInitialReplyErasure.kernelOf false (RawCtxSelectedInitialConstructor.response64 (other ++ target)) =
      ok (RawCtxSelectedChain.nativeKernel (RawCtxFreshChainCut.concreteChain target) (serverBase other)) := by
    simp only [PqxdhInitialReplyErasure.kernelOf, PqxdhInitialResponseService.pending, Bool.false_eq_true, ite_false]
    exact split
  simp only [PqxdhSelectedFirstRecord.initialKernel, kernelOf]
  rfl

end ServerKernel

section UpToBind
open OracleComp.ProgramLogic.Relational
variable {σ₁ σ₂ : Type} (related : σ₁ → σ₂ → Prop) (bad : σ₂ → Prop)

/-- A right computation that keeps a bad state bad. -/
def Absorbs {β : Type} (work : StateT σ₂ ProbComp β) : Prop :=
  ∀ state, bad state → ∀ result ∈ support (work.run state), bad result.2

/-- A return keeps bad states bad. -/
theorem absorbs_pure {β : Type} (value : β) : Absorbs bad (pure value : StateT σ₂ ProbComp β) := by
  intro state holds result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact holds

/-- Sequencing two computations that keep bad states bad keeps them bad. -/
theorem absorbs_bind {β γ : Type} (work : StateT σ₂ ProbComp β) (continuation : β → StateT σ₂ ProbComp γ)
    (first : Absorbs bad work) (rest : ∀ value, Absorbs bad (continuation value)) : Absorbs bad (work >>= continuation) := by
  intro state holds result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, middleSupported, restSupported⟩ := supported
  exact rest middle.1 middle.2 (first state holds middle middleSupported) result restSupported

/-- Mapping the result of a computation that keeps bad states bad keeps them bad. -/
theorem absorbs_map {β γ : Type} (work : StateT σ₂ ProbComp β) (function : β → γ) (first : Absorbs bad work) :
    Absorbs bad (function <$> work) := by
  intro state holds result supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, middleSupported, rfl⟩ := supported
  exact first state holds middle middleSupported

/-- The up-to-bad postcondition with a relation on replies. -/
def UpToWith {β₁ β₂ : Type} (reply : β₁ → β₂ → Prop) (left : β₁ × σ₁) (right : β₂ × σ₂) : Prop :=
  bad right.2 ∨ (reply left.1 right.1 ∧ related left.2 right.2)

/-- Sequencing two up-to-bad couplings whose right continuation keeps bad states bad. -/
theorem bind_upto {α₁ α₂ β₁ β₂ : Type} (first : StateT σ₁ ProbComp α₁) (second : StateT σ₂ ProbComp α₂)
    (continuation₁ : α₁ → StateT σ₁ ProbComp β₁) (continuation₂ : α₂ → StateT σ₂ ProbComp β₂)
    (middle : α₁ → α₂ → Prop) (reply : β₁ → β₂ → Prop) (state₁ : σ₁) (state₂ : σ₂)
    (coupled : RelTriple (first.run state₁) (second.run state₂) (UpToWith related bad middle))
    (absorbs : ∀ value, Absorbs bad (continuation₂ value))
    (next : ∀ (left : α₁ × σ₁) (right : α₂ × σ₂), middle left.1 right.1 → related left.2 right.2 → ¬ bad right.2 →
      RelTriple ((continuation₁ left.1).run left.2) ((continuation₂ right.1).run right.2) (UpToWith related bad reply)) :
    RelTriple ((first >>= continuation₁).run state₁) ((second >>= continuation₂).run state₂) (UpToWith related bad reply) := by
  simp only [StateT.run_bind]
  refine relTriple_bind coupled fun left right held => ?_
  by_cases isBad : bad right.2
  · exact relTriple_post_mono (product_coupling (P := fun _ => True) (fun _ _ => trivial)
      (absorbs right.1 right.2 isBad)) fun _ _ holds => Or.inl holds.2
  · rcases held with impossible | ⟨replied, same⟩
    · exact absurd impossible isBad
    · exact next left right replied same isBad

/-- Two pure replies are coupled when related. -/
theorem pure_upto {β₁ β₂ : Type} (reply : β₁ → β₂ → Prop) (value₁ : β₁) (value₂ : β₂) (state₁ : σ₁) (state₂ : σ₂)
    (replied : reply value₁ value₂) (same : related state₁ state₂) :
    RelTriple ((pure value₁ : StateT σ₁ ProbComp β₁).run state₁) ((pure value₂ : StateT σ₂ ProbComp β₂).run state₂)
      (UpToWith related bad reply) := by
  simp only [StateT.run_pure]
  exact relTriple_pure_pure (Or.inr ⟨replied, same⟩)

end UpToBind

section BuilderCoupling
open OracleComp.ProgramLogic.Relational
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhRefinement
variable {Kernel Other M P Consumed σ₁ σ₂ : Type} (interpret : Other → Kernel)
  (calls₁ : RawCtxChainOwner.Calls Kernel (StateT σ₁ ProbComp)) (calls₂ : RawCtxChainOwner.Calls Other (StateT σ₂ ProbComp))
  (aux₁ : QueryImpl AuxSpec (StateT σ₁ ProbComp)) (aux₂ : QueryImpl AuxSpec (StateT σ₂ ProbComp))
  (related : σ₁ → σ₂ → Prop) (bad : σ₂ → Prop)

/-- Publishing commutes with a kernel map of the publication state. -/
theorem publish_map (state : PqxdhInitialGenericPublication.State Other M P Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : Other) (metadata : P) :
    PqxdhSelectedFirstRecord.pubMap interpret (PqxdhInitialGenericPublication.publish state candidate kernel metadata) =
      PqxdhInitialGenericPublication.publish (PqxdhSelectedFirstRecord.pubMap interpret state) candidate (interpret kernel) metadata := by
  simp only [PqxdhSelectedFirstRecord.pubMap, PqxdhInitialGenericPublication.publish, RawCtxGenericRoleStorage.mapServer]
  congr 1
  congr 1
  funext key
  by_cases same : key = candidate.key_id
  · subst key
    simp only [Function.update_self, Option.map_some]
    rfl
  · simp only [Function.update_of_ne same]

variable (auxAbsorbs : ∀ query, Absorbs bad (aux₂ query)) (sendAbsorbs : ∀ kernel context, Absorbs bad (calls₂.send kernel context))

include auxAbsorbs sendAbsorbs in
/-- The tagged first-send tail keeps bad states bad. -/
theorem after_absorbs (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Other)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) :
    Absorbs bad (PqxdhInitialGenericPublication.afterInitialization calls₂ aux₂ candidate authenticated kernel metadata state) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine absorbs_bind bad _ _ (sendAbsorbs _ _) fun sent => ?_
  obtain ⟨advanced, encrypted⟩ := sent
  refine absorbs_bind bad _ _ (auxAbsorbs _) fun _ => ?_
  cases encrypted with
  | none => exact absorbs_pure bad _
  | some encrypted =>
    refine absorbs_bind bad _ _ (auxAbsorbs _) fun serialized => ?_
    cases serialized <;> exact absorbs_pure bad _

variable (auxCoupled : ∀ query first second, related first second → ¬ bad second →
    RelTriple ((aux₁ query).run first) ((aux₂ query).run second) (UpToWith related bad Eq))
  (sendCoupled : ∀ kernel context first second, related first second → ¬ bad second →
    RelTriple ((calls₁.send (interpret kernel) context).run first) ((calls₂.send kernel context).run second)
      (UpToWith related bad fun left right => left = Prod.map interpret id right))

include auxAbsorbs auxCoupled sendCoupled in
/-- The first-send tail of the builder under a kernel map is coupled up to bad. -/
theorem after_coupled (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Other)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) (first : σ₁) (second : σ₂)
    (same : related first second) (good : ¬ bad second) :
    RelTriple ((PqxdhInitialGenericPublication.afterInitialization calls₁ aux₁ candidate authenticated (interpret kernel) metadata
        (PqxdhSelectedFirstRecord.pubMap interpret state)).run first)
      ((PqxdhInitialGenericPublication.afterInitialization calls₂ aux₂ candidate authenticated kernel metadata state).run second)
      (UpToWith related bad fun left right => left = Prod.map id (PqxdhSelectedFirstRecord.pubMap interpret) right) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine bind_upto related bad _ _ _ _ _ _ first second (sendCoupled kernel _ first second same good)
    (fun sent => ?_) fun left right mapped closer notBad => ?_
  · obtain ⟨advanced, encrypted⟩ := sent
    refine absorbs_bind bad _ _ (auxAbsorbs _) fun _ => ?_
    cases encrypted with
    | none => exact absorbs_pure bad _
    | some encrypted =>
      refine absorbs_bind bad _ _ (auxAbsorbs _) fun serialized => ?_
      cases serialized <;> exact absorbs_pure bad _
  · obtain ⟨⟨advanced, encrypted⟩, rightState⟩ := right
    obtain ⟨⟨advanced', encrypted'⟩, leftState⟩ := left
    simp only [Prod.map, Prod.mk.injEq] at mapped
    obtain ⟨rfl, rfl⟩ := mapped
    refine bind_upto related bad _ _ _ _ Eq _ leftState rightState (auxCoupled _ leftState rightState closer notBad)
      (fun _ => ?_) fun left right equal closer' notBad' => ?_
    · cases encrypted' with
      | none => exact absorbs_pure bad _
      | some encrypted =>
        refine absorbs_bind bad _ _ (auxAbsorbs _) fun serialized => ?_
        cases serialized <;> exact absorbs_pure bad _
    · cases encrypted' with
      | none => exact pure_upto related bad _ _ _ _ _ rfl closer'
      | some encrypted =>
        refine bind_upto related bad _ _ _ _ Eq _ left.2 right.2 (auxCoupled _ left.2 right.2 closer' notBad')
          (fun serialized => by cases serialized <;> exact absorbs_pure bad _) fun left' right' equal' closer'' _ => ?_
        rw [equal']
        cases right'.1 with
        | none => exact pure_upto related bad _ _ _ _ _ rfl closer''
        | some serialized =>
          refine pure_upto related bad _ _ _ _ _ ?_ closer''
          simp only [Prod.map, id_eq, publish_map]

include auxAbsorbs sendAbsorbs in
/-- The tagged candidate builder after its identity check keeps bad states bad. -/
theorem reserve_absorbs (initial : RustM Other) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) (reserved : Bool) :
    Absorbs bad (if !reserved then (pure (ok (none, state)) : StateT σ₂ ProbComp _) else
      PqxdhInitialGenericBuilder.continueRust initial fun kernel => do
        let plaintext := data.getD registrationWitness
        if plaintext.isEmpty then pure (ok (none, state))
        else if 8 + plaintext.length ≤ Usize.max then do
          let allocated ← aux₂ (.reservePlaintext (8 + plaintext.length))
          if !allocated then pure (ok (none, state)) else
            PqxdhInitialGenericBuilder.continueRust (candidate.key_id_binding) fun binding =>
              ok <$> PqxdhInitialGenericPublication.afterInitialization calls₂ aux₂ candidate
                (absBytes binding.bytes ++ plaintext) kernel metadata state
        else pure (ok (none, state))) := by
  split
  · exact absorbs_pure bad _
  · cases initial with
    | fail error => exact absorbs_pure bad _
    | div => exact absorbs_pure bad _
    | ok kernel =>
      simp only [PqxdhInitialGenericBuilder.continueRust]
      split
      · exact absorbs_pure bad _
      · split
        · refine absorbs_bind bad _ _ (auxAbsorbs _) fun allocated => ?_
          split
          · exact absorbs_pure bad _
          · cases candidate.key_id_binding with
            | fail error => exact absorbs_pure bad _
            | div => exact absorbs_pure bad _
            | ok binding =>
              exact absorbs_map bad _ _ (after_absorbs calls₂ aux₂ bad auxAbsorbs sendAbsorbs _ _ _ _ _)
        · exact absorbs_pure bad _

include auxAbsorbs sendAbsorbs in
/-- The tagged candidate builder keeps bad states bad. -/
theorem candidate_absorbs (initial : RustM Other) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) :
    Absorbs bad (PqxdhInitialGenericBuilder.candidate calls₂ aux₂ initial candidate data metadata state) := by
  unfold PqxdhInitialGenericBuilder.candidate
  refine absorbs_bind bad _ _ (auxAbsorbs _) fun valid => ?_
  split
  · exact absorbs_pure bad _
  · exact absorbs_bind bad _ _ (auxAbsorbs _) fun reserved =>
      reserve_absorbs calls₂ aux₂ bad auxAbsorbs sendAbsorbs initial candidate data metadata state reserved

/-- The reply relation of the builder under a kernel map. -/
def BuiltReply (left : RustM (Option Response × PqxdhInitialGenericPublication.State Kernel M P Consumed))
    (right : RustM (Option Response × PqxdhInitialGenericPublication.State Other M P Consumed)) : Prop :=
  left = Prod.map id (PqxdhSelectedFirstRecord.pubMap interpret) <$> right

include auxAbsorbs sendAbsorbs auxCoupled sendCoupled in
/-- The candidate builder under a kernel map is coupled up to bad. -/
theorem candidate_coupled (initial : RustM Other) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) (first : σ₁) (second : σ₂)
    (same : related first second) (good : ¬ bad second) :
    RelTriple ((PqxdhInitialGenericBuilder.candidate calls₁ aux₁ (interpret <$> initial) candidate data metadata
        (PqxdhSelectedFirstRecord.pubMap interpret state)).run first)
      ((PqxdhInitialGenericBuilder.candidate calls₂ aux₂ initial candidate data metadata state).run second)
      (UpToWith related bad (BuiltReply interpret)) := by
  unfold PqxdhInitialGenericBuilder.candidate
  refine bind_upto related bad _ _ _ _ Eq _ first second (auxCoupled _ first second same good) (fun valid => ?_)
    fun left right equal closer notBad => ?_
  · split
    · exact absorbs_pure bad _
    · exact absorbs_bind bad _ _ (auxAbsorbs _) fun reserved =>
        reserve_absorbs calls₂ aux₂ bad auxAbsorbs sendAbsorbs initial candidate data metadata state reserved
  · rw [equal]
    by_cases rejected : (!right.1) = true
    · simp only [rejected, ite_true]
      exact pure_upto related bad _ _ _ _ _ rfl closer
    · simp only [rejected, Bool.false_eq_true, ite_false]
      refine bind_upto related bad _ _ _ _ Eq _ left.2 right.2 (auxCoupled _ left.2 right.2 closer notBad)
        (fun reserved => reserve_absorbs calls₂ aux₂ bad auxAbsorbs sendAbsorbs initial candidate data metadata state reserved)
        fun later later' equal' closer' notBad' => ?_
      rw [equal']
      by_cases reservedRejected : (!later'.1) = true
      · simp only [reservedRejected, ite_true]
        exact pure_upto related bad _ _ _ _ _ rfl closer'
      · simp only [reservedRejected, Bool.false_eq_true, ite_false]
        cases initial with
        | fail error => exact pure_upto related bad _ _ _ _ _ rfl closer'
        | div => exact pure_upto related bad _ _ _ _ _ rfl closer'
        | ok kernel =>
          simp only [PqxdhInitialGenericBuilder.continueRust, RawCtxMaterialInterpretation.rust_map_ok]
          split
          · exact pure_upto related bad _ _ _ _ _ rfl closer'
          · split
            · refine bind_upto related bad _ _ _ _ Eq _ later.2 later'.2 (auxCoupled _ later.2 later'.2 closer' notBad')
                (fun allocated => ?_) fun final final' equal'' closer'' notBad'' => ?_
              · split
                · exact absorbs_pure bad _
                · cases candidate.key_id_binding with
                  | fail error => exact absorbs_pure bad _
                  | div => exact absorbs_pure bad _
                  | ok binding => exact absorbs_map bad _ _ (after_absorbs calls₂ aux₂ bad auxAbsorbs sendAbsorbs _ _ _ _ _)
              · rw [equal'']
                split
                · exact pure_upto related bad _ _ _ _ _ rfl closer''
                · cases candidate.key_id_binding with
                  | fail error => exact pure_upto related bad _ _ _ _ _ rfl closer''
                  | div => exact pure_upto related bad _ _ _ _ _ rfl closer''
                  | ok binding =>
                    simp only [StateT.run_map]
                    refine relTriple_map (relTriple_post_mono (after_coupled interpret calls₁ calls₂ aux₁ aux₂ related bad
                      auxAbsorbs auxCoupled sendCoupled candidate _ kernel metadata state final.2 final'.2 closer'' notBad'') ?_)
                    intro leftResult rightResult held
                    rcases held with isBad | ⟨replied, closerFinal⟩
                    · exact Or.inl isBad
                    · exact Or.inr ⟨by simp only [BuiltReply, replied]; rfl, closerFinal⟩
            · exact pure_upto related bad _ _ _ _ _ rfl closer'

include auxAbsorbs sendAbsorbs auxCoupled sendCoupled in
/-- The consumed-input builder under a kernel map is coupled up to bad. -/
theorem used_coupled (initial : RustM Other) (pending : PqxdhRegistrationInputs.UsedInput) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Other M P Consumed) (first : σ₁) (second : σ₂)
    (same : related first second) (good : ¬ bad second) :
    RelTriple ((PqxdhInitialGenericBuilder.usedBuild calls₁ aux₁ (interpret <$> initial) pending data metadata
        (PqxdhSelectedFirstRecord.pubMap interpret state)).run first)
      ((PqxdhInitialGenericBuilder.usedBuild calls₂ aux₂ initial pending data metadata state).run second)
      (UpToWith related bad (BuiltReply interpret)) := by
  unfold PqxdhInitialGenericBuilder.usedBuild
  have control : (PqxdhSelectedFirstRecord.pubMap interpret state).control = state.control := rfl
  have identity : (PqxdhSelectedFirstRecord.pubMap interpret state).server.identity = state.server.identity := rfl
  have keyId : (PqxdhSelectedFirstRecord.pubMap interpret state).identityKeyId = state.identityKeyId := rfl
  have occupied : ∀ key, ((PqxdhSelectedFirstRecord.pubMap interpret state).server.peers key).isSome =
      (state.server.peers key).isSome := by
    intro key
    simp [PqxdhSelectedFirstRecord.pubMap, RawCtxGenericRoleStorage.mapServer]
  rw [control, identity, keyId]
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => exact pure_upto related bad _ _ _ _ _ rfl same
  | div => exact pure_upto related bad _ _ _ _ _ rfl same
  | ok result =>
    cases result with
    | Err error => exact pure_upto related bad _ _ _ _ _ rfl same
    | Ok key =>
      simp only [PqxdhInitialGenericBuilder.continueRust, occupied]
      cases prepared : PqxdhRegistrationInputs.prepare state.control pending ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
      | fail error => exact pure_upto related bad _ _ _ _ _ rfl same
      | div => exact pure_upto related bad _ _ _ _ _ rfl same
      | ok value =>
        cases value with
        | Err error => exact pure_upto related bad _ _ _ _ _ rfl same
        | Ok value =>
          exact candidate_coupled interpret calls₁ calls₂ aux₁ aux₂ related bad auxAbsorbs sendAbsorbs auxCoupled
            sendCoupled initial value data metadata state first second same good

include auxAbsorbs sendAbsorbs auxCoupled sendCoupled in
/-- The Ready builder under a kernel map is coupled up to bad. -/
theorem ready_coupled (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (initial : RustM Other)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (state : PqxdhInitialGenericPublication.State Other M P Consumed) (first : σ₁) (second : σ₂)
    (same : related first second) (good : ¬ bad second) :
    RelTriple ((PqxdhInitialGenericBuilder.readyBuild source calls₁ aux₁ (interpret <$> initial) binding ready metadata
        (PqxdhSelectedFirstRecord.pubMap interpret state)).run first)
      ((PqxdhInitialGenericBuilder.readyBuild source calls₂ aux₂ initial binding ready metadata state).run second)
      (UpToWith related bad (BuiltReply interpret)) :=
  used_coupled interpret calls₁ calls₂ aux₁ aux₂ related bad auxAbsorbs sendAbsorbs auxCoupled sendCoupled initial _ _ metadata state
    first second same good

end BuilderCoupling

section TaggedBuilder
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A concrete front is represented by a tagged front. -/
def FrontRep (target : RootOutput) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (tagged : TFront M P I D K S B) : Prop :=
  front.roles.1 = mapRoles (mapKernel target) tagged.roles ∧ front.controls = tagged.controls ∧ front.consumed = tagged.consumed

/-- The all-known tagged image of a concrete front. -/
def frontOf (front : PqxdhSelectedPostCompiler.Front M P I D K S B) : TFront M P I D K S B :=
  ⟨mapRoles knownTagged front.roles.1, front.controls, front.consumed⟩

/-- A kernel map followed by its left inverse keeps every Server state. -/
theorem server_inverse {Kernel Other : Type} (represent : Kernel → Other) (interpret : Other → Kernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel) (state : ServerState Kernel M P) :
    mapServer interpret (mapServer represent state) = state := by
  obtain ⟨⟨identity, peers, metadata⟩, attempts⟩ := state
  simp only [mapServer, Option.map_map]
  congr
  funext kid
  cases peers kid <;> simp [mapPeer, inverse]

/-- A kernel map followed by its left inverse keeps every Beacon state. -/
theorem beacon_inverse {Kernel Other : Type} (represent : Kernel → Other) (interpret : Other → Kernel)
    (inverse : ∀ kernel, interpret (represent kernel) = kernel) (state : BeaconState Kernel I D K) :
    mapBeacon interpret (mapBeacon represent state) = state := by
  cases phase : state.beacon.phase <;> simp [mapBeacon, mapPhase, phase, inverse]
  all_goals rw [← phase]

/-- A concrete front is represented by its all-known tagged image. -/
theorem front_rep (target : RootOutput) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    FrontRep target front (frontOf front) := by
  refine ⟨?_, rfl, rfl⟩
  simp only [frontOf, mapRoles]
  ext index
  · exact (server_inverse knownTagged (mapKernel target) (known_tagged target) _).symm
  · exact (beacon_inverse knownTagged (mapKernel target) (known_tagged target) _).symm

/-- Record the consumed registration identifier in a tagged front. -/
def tConsume (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready) (before : TFront M P I D K S B) : TFront M P I D K S B :=
  { before with consumed := Function.update before.consumed index ready.consumed.consumed }

/-- The selected Server's tagged publication state. -/
def tServer (sender : M → Std.U64) (index : Fin S) (before : TFront M P I D K S B) :
    PqxdhInitialGenericPublication.State TKernel M P (List Pqxdh.Bytes) :=
  ⟨(before.roles.1 index).server, sender (before.roles.1 index).server.metadata, before.controls index, before.consumed index⟩

/-- Install an updated tagged Server publication state. -/
def tInstall (index : Fin S) (before : TFront M P I D K S B)
    (updated : PqxdhInitialGenericPublication.State TKernel M P (List Pqxdh.Bytes)) : TFront M P I D K S B :=
  ⟨(Function.update before.roles.1 index { before.roles.1 index with server := updated.server }, before.roles.2),
    Function.update before.controls index updated.control, Function.update before.consumed index updated.consumed⟩

/-- Reinstall a tagged builder result. -/
def tReinstall (index : Fin S) (before : TFront M P I D K S B)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State TKernel M P (List Pqxdh.Bytes))) :
    RustM (Option PqxdhServerRegistrationPublication.Response) × TFront M P I D K S B :=
  match result with
  | .ok value => (.ok value.1, tInstall index before value.2)
  | .fail error => (.fail error, before)
  | .div => (.div, before)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The tagged first Server builder: the same consumed input, gates, first send and publication, with the tagged Server kernel. -/
noncomputable def taggedBuild (other : RootOutput) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    StateT (TFront M P I D K S B) (StateT (RawCtxSharedPrimitive.SharedState (Local A N C) × Log) ProbComp)
      (RustM (Option PqxdhServerRegistrationPublication.Response)) := fun before =>
  let current := tConsume index ready before
  let input := tServer sender index current
  tReinstall index current <$> PqxdhInitialGenericBuilder.readyBuild source (taggedCalls source writer prior key nonce next)
    (fun query => keepLog (PqxdhSelectedFirstRecord.serverAux (X := X) (extra := extra) pre application initial selector aux query))
    (.ok (serverKernel other)) ⟨input.server.identity, input.identityKeyId⟩ ready metadata input

end TaggedBuilder

section BuildCoupling
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Recording the consumed registration identifier on both sides keeps the front representation. -/
theorem consume_rep (target : RootOutput) (index : Fin S) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (tagged : TFront M P I D K S B) (rep : FrontRep target front tagged) :
    FrontRep target (PqxdhSelectedFirstRecord.consumeFront index ready front) (tConsume index ready tagged) := by
  obtain ⟨roles, controls, consumed⟩ := rep
  exact ⟨roles, controls, by simp [PqxdhSelectedFirstRecord.consumeFront, tConsume, consumed]⟩

/-- The selected Server publication state of a represented front is the kernel map of the tagged publication state. -/
theorem server_rep (target : RootOutput) (sender : M → Std.U64) (index : Fin S)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (tagged : TFront M P I D K S B) (rep : FrontRep target front tagged) :
    PqxdhSelectedFirstRecord.selectedServer sender index front =
      PqxdhSelectedFirstRecord.pubMap (mapKernel target) (tServer sender index tagged) := by
  obtain ⟨roles, controls, consumed⟩ := rep
  simp only [PqxdhSelectedFirstRecord.selectedServer, tServer, PqxdhSelectedFirstRecord.pubMap, roles, controls, consumed, mapRoles,
    mapServer]

/-- Reinstalling a builder result and its kernel map gives the same reply and keeps the front representation. -/
theorem reinstall_rep (target : RootOutput) (index : Fin S)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (tagged : TFront M P I D K S B) (rep : FrontRep target front tagged)
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State TKernel M P (List Pqxdh.Bytes))) :
    (PqxdhSelectedFirstRecord.reinstallServer index front
        (Prod.map id (PqxdhSelectedFirstRecord.pubMap (mapKernel target)) <$> result)).1 = (tReinstall index tagged result).1 ∧
      FrontRep target (PqxdhSelectedFirstRecord.reinstallServer index front
        (Prod.map id (PqxdhSelectedFirstRecord.pubMap (mapKernel target)) <$> result)).2 (tReinstall index tagged result).2 := by
  obtain ⟨roles, controls, consumed⟩ := rep
  cases result with
  | fail error => exact ⟨rfl, roles, controls, consumed⟩
  | div => exact ⟨rfl, roles, controls, consumed⟩
  | ok value =>
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp only [PqxdhSelectedFirstRecord.reinstallServer, tReinstall, PqxdhSelectedFirstRecord.installServer, tInstall,
        RawCtxMaterialInterpretation.rust_map_ok, Prod.map, roles, mapRoles]
      congr 1
      funext position
      by_cases same : position = index
      · subst same
        simp only [Function.update_self, mapServer, PqxdhSelectedFirstRecord.pubMap]
      · simp only [Function.update_of_ne same]
    · simp [PqxdhSelectedFirstRecord.reinstallServer, tReinstall, PqxdhSelectedFirstRecord.installServer, tInstall,
        RawCtxMaterialInterpretation.rust_map_ok, controls, PqxdhSelectedFirstRecord.pubMap]
    · simp [PqxdhSelectedFirstRecord.reinstallServer, tReinstall, PqxdhSelectedFirstRecord.installServer, tInstall,
        RawCtxMaterialInterpretation.rust_map_ok, consumed, PqxdhSelectedFirstRecord.pubMap]

end BuildCoupling

section BuildInstance
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The selected first Server builder and the tagged builder are coupled up to a logged selected value, with represented fronts. -/
theorem build_coupled (target other : RootOutput) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (tagged : TFront M P I D K S B) (rep : FrontRep target front tagged)
    (first : RawCtxSharedPrimitive.SharedState (Local A N C)) (second : RawCtxSharedPrimitive.SharedState (Local A N C) × Log)
    (near : Near first second) (fresh : ¬ Logged target second) :
    RelTriple ((PqxdhSelectedFirstRecord.selectedBuild (extra := extra) pre application initial selector aux source writer prior none key
        target nonce next sender (PqxdhSelectedFirstRecord.initialKernel (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
        index metadata ready front).run first)
      ((taggedBuild source writer prior key nonce next sender pre application initial selector aux other index metadata ready tagged).run
        second)
      (UpToWith Near (Logged target) fun left right => left.1 = right.1 ∧ FrontRep target left.2 right.2) := by
  have consumed := consume_rep target index ready front tagged rep
  unfold PqxdhSelectedFirstRecord.selectedBuild taggedBuild
  simp only
  rw [server_rep target sender index _ _ consumed, server_kernel]
  rw [StateT.run_map, StateT.run_map]
  refine relTriple_map (relTriple_post_mono (ready_coupled (mapKernel target)
    (PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next)
    (taggedCalls source writer prior key nonce next)
    (PqxdhSelectedFirstRecord.serverAux (X := X) (extra := extra) pre application initial selector aux)
    (fun query => keepLog (PqxdhSelectedFirstRecord.serverAux (X := X) (extra := extra) pre application initial selector aux query))
    Near (Logged target) ?_ ?_ ?_ ?_ source (.ok (serverKernel other)) _ ready metadata _ first second near fresh) ?_)
  · exact fun query state logged result supported => grows_keep target _ state logged result supported
  · exact fun kernel context state logged result supported =>
      (labels_prefix source writer prior key nonce next _ state result supported).subset logged
  · intro query left right closer _
    refine relTriple_post_mono (restores_exact _ (local_restores (aux query)) left right closer) ?_
    intro leftResult rightResult held
    exact Or.inr held
  · intro kernel context left right closer _
    have mapped := send_map (A := Local A N C) source writer prior key nonce next target kernel context
    change RelTriple ((PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next).send
      (mapKernel target kernel) context |>.run left) _ _
    rw [show (PqxdhSelectedMessageBeacon.materialCalls source writer prior none key target nonce next).send (mapKernel target kernel)
      context = _ from mapped, ← labels_send, StateT.run_map]
    change RelTriple _ ((simulateQ (taggedLabels source writer prior key nonce next)
      (simulateQ sendInject (RawCtxChainSend.execute kernel context))).run right) _
    rw [← id_map ((simulateQ (taggedLabels source writer prior key nonce next)
      (simulateQ sendInject (RawCtxChainSend.execute kernel context))).run right)]
    refine relTriple_map (relTriple_post_mono (labels_near source writer prior key nonce next target _ left right closer) ?_)
    intro leftResult rightResult held
    rcases held with impossible | bad | ⟨equal, closer'⟩
    · exact impossible.elim
    · exact Or.inl bad
    · exact Or.inr ⟨by simp [equal], closer'⟩
  · intro leftResult rightResult held
    rcases held with bad | ⟨replied, closer⟩
    · exact Or.inl bad
    · simp only [BuiltReply] at replied
      rw [replied]
      obtain ⟨sameReply, sameFront⟩ := reinstall_rep target index _ _ consumed rightResult.1
      exact Or.inr ⟨⟨sameReply, sameFront⟩, closer⟩

end BuildInstance

section BuilderPeers
open ratchet.refined
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhRefinement RawCtxGenericRoleStorage
variable {M P Consumed σ : Type} (calls : RawCtxChainOwner.Calls TKernel (StateT σ ProbComp)) (aux : QueryImpl AuxSpec (StateT σ ProbComp))

/-- Every peer of a tagged publication state has a known send chain. -/
def AllKnown (state : PqxdhInitialGenericPublication.State TKernel M P Consumed) : Prop :=
  ∀ kid peer, state.server.peers kid = some peer → KnownSend peer.kernel

/-- A send call keeps a known send chain known. -/
def SendKnown : Prop := ∀ kernel context state, KnownSend kernel →
  ∀ result ∈ support ((calls.send kernel context).run state), KnownSend result.1.1

/-- The tagged send calls keep a known send chain known. -/
theorem send_known {A : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (key : PqxdhSecretInputKdf.RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput)
    (next : PqxdhSecretInputKdf.RootOutput) : SendKnown (taggedCalls (A := A) source writer prior key nonce next) := by
  intro kernel context state known result supported
  rcases tagged_send source writer prior key nonce next kernel context state result supported with ⟨_, same, _⟩ | ⟨_, known', _⟩
  · rw [same]
    exact known
  · exact known'

/-- Publishing a kernel with a known send chain keeps every peer's send chain known. -/
theorem publish_known (state : PqxdhInitialGenericPublication.State TKernel M P Consumed) (candidate : pqxdh.ServerRegistrationCandidate)
    (kernel : TKernel) (metadata : P) (known : AllKnown state) (fresh : KnownSend kernel) :
    AllKnown (PqxdhInitialGenericPublication.publish state candidate kernel metadata) := by
  intro kid peer found
  simp only [PqxdhInitialGenericPublication.publish] at found
  by_cases same : kid = candidate.key_id
  · subst same
    simp only [Function.update_self, Option.some.injEq] at found
    subst found
    exact fresh
  · simp only [Function.update_of_ne same] at found
    exact known kid peer found

variable (sendKnown : SendKnown calls)

include sendKnown in
/-- The tagged builder keeps every peer's send chain known when the initial kernel's is known. -/
theorem ready_known (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (kernel : TKernel) (fresh : KnownSend kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (state : PqxdhInitialGenericPublication.State TKernel M P Consumed) (known : AllKnown state) (start : σ) :
    Reaches (PqxdhInitialGenericBuilder.readyBuild source calls aux (ok kernel) binding ready metadata state) start
      fun result => ∀ value, result.1 = ok value → AllKnown value.2 := by
  have done : ∀ (current : σ), Reaches (pure (ok ((none : Option Response), state)) : StateT σ ProbComp (RustM (Option Response ×
      PqxdhInitialGenericPublication.State TKernel M P Consumed))) current
      fun result => ∀ value, result.1 = ok value → AllKnown value.2 := fun current =>
    reaches_pure _ _ _ fun value found => by cases found; exact known
  have failed : ∀ (error : Error) (current : σ), Reaches (pure (fail error) : StateT σ ProbComp (RustM (Option Response ×
      PqxdhInitialGenericPublication.State TKernel M P Consumed))) current fun result => ∀ value, result.1 = ok value → AllKnown value.2 :=
    fun error current => reaches_pure _ _ _ fun value found => by cases found
  have diverged : ∀ (current : σ), Reaches (pure div : StateT σ ProbComp (RustM (Option Response ×
      PqxdhInitialGenericPublication.State TKernel M P Consumed))) current fun result => ∀ value, result.1 = ok value → AllKnown value.2 :=
    fun current => reaches_pure _ _ _ fun value found => by cases found
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => exact failed error start
  | div => exact diverged start
  | ok result =>
    cases result with
    | Err error => exact done start
    | Ok key =>
      simp only [PqxdhInitialGenericBuilder.continueRust]
      cases prepared : PqxdhRegistrationInputs.prepare state.control (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
      | fail error => exact failed error start
      | div => exact diverged start
      | ok value =>
        cases value with
        | Err error => exact done start
        | Ok candidate =>
          unfold PqxdhInitialGenericBuilder.candidate
          refine reaches_bind _ _ _ _ fun valid _ => ?_
          dsimp only
          split
          · exact done _
          · refine reaches_bind _ _ _ _ fun reserved _ => ?_
            dsimp only
            split
            · exact done _
            · simp only [PqxdhInitialGenericBuilder.continueRust]
              split
              · exact done _
              · split
                · refine reaches_bind _ _ _ _ fun allocated _ => ?_
                  dsimp only
                  split
                  · exact done _
                  · cases candidate.key_id_binding with
                    | fail error => exact failed error _
                    | div => exact diverged _
                    | ok bound =>
                      simp only
                      intro final finalSupported
                      simp only [StateT.run_map, support_map, Set.mem_image] at finalSupported
                      obtain ⟨inner, innerSupported, rfl⟩ := finalSupported
                      intro value found
                      simp only [RustM.ok.injEq] at found
                      subst found
                      unfold PqxdhInitialGenericPublication.afterInitialization at innerSupported
                      simp only [StateT.run_bind, mem_support_bind_iff] at innerSupported
                      obtain ⟨sent, sentSupported, rest⟩ := innerSupported
                      have advancedKnown := sendKnown _ _ _ fresh sent sentSupported
                      obtain ⟨⟨advanced, encrypted⟩, sentState⟩ := sent
                      obtain ⟨erased, _, rest⟩ := rest
                      cases encrypted with
                      | none =>
                        simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
                        subst rest
                        exact known
                      | some encrypted =>
                        simp only [StateT.run_bind, mem_support_bind_iff] at rest
                        obtain ⟨⟨serializedValue, serializedState⟩, _, rest⟩ := rest
                        cases serializedValue with
                        | none =>
                          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
                          subst rest
                          exact known
                        | some bytes =>
                          simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
                          subst rest
                          exact publish_known _ _ _ _ known advancedKnown
                · exact done _

end BuilderPeers


section Growth
variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

/-- A natural measure of the state that every query raises by at most one if it satisfies a predicate, and not at all otherwise, is raised over a whole stateful simulation by at most the predicate query bound of the client. -/
theorem predicate_growth {α : Type} (impl : QueryImpl spec (StateT σ ProbComp)) (measure : σ → Nat) (p : ι → Prop)
    [DecidablePred p]
    (step : ∀ query state, ∀ result ∈ support ((impl query).run state), measure result.2 ≤ measure state + if p query then 1 else 0)
    (client : OracleComp spec α) (budget : Nat) (bounded : client.IsQueryBoundP p budget) (state : σ) :
    ∀ result ∈ support ((simulateQ impl client).run state), measure result.2 ≤ measure state + budget := by
  induction client using OracleComp.inductionOn generalizing state budget with
  | pure value =>
    intro result supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    intro result supported
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, middleSupported, rest⟩ := supported
    rw [isQueryBoundP_query_bind_iff] at bounded
    have later := ih middle.1 _ (bounded.2 middle.1) middle.2 result rest
    have here := step query state middle middleSupported
    by_cases holds : p query
    · have positive := bounded.1.resolve_left (not_not.mpr holds)
      simp only [holds, ite_true] at later here
      omega
    · simp only [holds, ite_false] at later here
      omega

/-- A natural measure of the state that every query raises by at most the weight of its kind is raised over a whole stateful simulation by at most a potential of the per-kind query budgets of the client, provided one query of a kind with positive budget pays its weight out of the potential. -/
theorem weighted_growth {κ α : Type} [DecidableEq κ] (impl : QueryImpl spec (StateT σ ProbComp)) (measure : σ → Nat)
    (kind : ι → κ) (weight : κ → Nat) (potential : (κ → Nat) → Nat)
    (step : ∀ query state, ∀ result ∈ support ((impl query).run state), measure result.2 ≤ measure state + weight (kind query))
    (drop : ∀ budget k, 0 < budget k → weight k + potential (Function.update budget k (budget k - 1)) ≤ potential budget)
    (client : OracleComp spec α) (budget : κ → Nat)
    (bounded : ∀ k, client.IsQueryBoundP (fun query => kind query = k) (budget k)) (state : σ) :
    ∀ result ∈ support ((simulateQ impl client).run state), measure result.2 ≤ measure state + potential budget := by
  induction client using OracleComp.inductionOn generalizing state budget with
  | pure value =>
    intro result supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    intro result supported
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, middleSupported, rest⟩ := supported
    have here := bounded (kind query)
    rw [isQueryBoundP_query_bind_iff] at here
    have positive : 0 < budget (kind query) := here.1.resolve_left (not_not.mpr rfl)
    have later : ∀ k, (continuation middle.1).IsQueryBoundP (fun query => kind query = k)
        (Function.update budget (kind query) (budget (kind query) - 1) k) := by
      intro k
      have current := bounded k
      rw [isQueryBoundP_query_bind_iff] at current
      by_cases same : kind query = k
      · subst same
        simpa only [Function.update_self, ite_true] using current.2 middle.1
      · rw [Function.update_of_ne (Ne.symm same)]
        simpa only [same, ite_false] using current.2 middle.1
    have final := ih middle.1 _ later middle.2 result rest
    have grown := step query state middle middleSupported
    have dropped := drop budget (kind query) positive
    omega

/-- A predicate query bound transfers through a stateless query translation that spends at most one target query of the target predicate on a source query of the source predicate, and none otherwise. -/
theorem inject_bound {κ α : Type} {target : OracleSpec κ} (inject : QueryImpl spec (OracleComp target)) (p : ι → Prop)
    [DecidablePred p] (q : κ → Prop) [DecidablePred q]
    (step : ∀ query, (inject query).IsQueryBoundP q (if p query then 1 else 0))
    (work : OracleComp spec α) (budget : Nat) (bounded : work.IsQueryBoundP p budget) :
    (simulateQ inject work).IsQueryBoundP q budget := by
  induction work using OracleComp.inductionOn generalizing budget with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query]
    refine (isQueryBoundP_bind (step query) fun reply _ => ih reply _ (bounded.2 reply)).mono ?_
    by_cases holds : p query
    · have positive := bounded.1.resolve_left (not_not.mpr holds)
      simp only [holds, ite_true]
      omega
    · simp only [holds, ite_false]
      omega

end Growth

section LogGrowth
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable
variable {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- A private derivation request among the record primitive queries. -/
def kdfQuery : LabelSpec.Domain → Bool
  | .inl (.inl _) => true
  | .inr (.inl (.inl _)) => true
  | _ => false

/-- One target-free service call adds at most one log entry, and only on a private derivation. -/
theorem label_growth (query : LabelSpec.Domain) (state : RawCtxSharedPrimitive.SharedState A × Log)
    (result : LabelSpec.Range query × (RawCtxSharedPrimitive.SharedState A × Log))
    (supported : result ∈ support ((taggedLabels source writer prior key nonce next query).run state)) :
    result.2.2.length ≤ state.2.length + if kdfQuery query = true then 1 else 0 := by
  rcases query with (slot | pending) | ((slot | pending) | query)
  all_goals first
    | (simp only [taggedLabels, StateT.run, support_pure, Set.mem_singleton_iff] at supported
       subst supported
       cases slot <;> simp [logged, kdfQuery])
    | (simp only [taggedLabels, keepLog, StateT.run, support_map, Set.mem_image] at supported
       obtain ⟨_, _, rfl⟩ := supported
       simp [kdfQuery])

/-- The log of the target-free services grows by at most the number of private derivation requests of the program. -/
theorem labels_growth {β : Type} (work : OracleComp LabelSpec β) (budget : Nat)
    (bounded : work.IsQueryBoundP (fun query => kdfQuery query = true) budget) (state : RawCtxSharedPrimitive.SharedState A × Log) :
    ∀ result ∈ support ((simulateQ (taggedLabels source writer prior key nonce next) work).run state),
      result.2.2.length ≤ state.2.length + budget :=
  predicate_growth _ (fun state => state.2.length) _ (label_growth source writer prior key nonce next) work budget bounded state

/-- The private derivation weight of a record kind: one for a send, fifty-one for a raw receive, none otherwise. -/
def kdfWeight : RawCtxServerServiceBounds.Kind → Nat
  | .send => 1
  | .raw => 51
  | _ => 0

/-- A symbolic receive makes at most fifty-one private derivation requests. -/
theorem receive_kdf (kernel : TKernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    ((symbolicCalls).receive kernel sequence context).IsQueryBoundP (fun query => kdfQuery query = true) 51 :=
  inject_bound receiveInject (fun query => query.isLeft = true) _ (fun query => by cases query <;> simp [receiveInject, kdfQuery])
    _ 51 (RawCtxChainReceiveBounds.receive_bound kernel sequence context)

/-- A symbolic send makes at most one private derivation request. -/
theorem send_kdf (kernel : TKernel) (context : RawCtxSourceSend.SealContext) :
    ((symbolicCalls).send kernel context).IsQueryBoundP (fun query => kdfQuery query = true) 1 :=
  inject_bound sendInject (fun query => query.isLeft = true) _ (fun query => by cases query <;> simp [sendInject, kdfQuery])
    _ 1 (RawCtxChainSend.program_kdf_bound _)

/-- A public query makes no private derivation request. -/
theorem public_kdf (query : RawCtxServerServices.PublicSpec.Domain) :
    (publicInject query).IsQueryBoundP (fun query => kdfQuery query = true) 0 := by
  simp only [publicInject, isQueryBoundP_query_iff]
  intro holds
  exact Bool.noConfusion holds

/-- A symbolic role or public operation makes at most the private derivation weight of its record kind. -/
theorem step_kdf {M P I D K : Type} {S B : Nat} (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (roles : RawCtxGenericRoleFamily.Roles TKernel M P I D K S B) :
    (symbolicStep sender route decode query roles).IsQueryBoundP (fun query => kdfQuery query = true)
      (kdfWeight (RawCtxProtocolBudgets.sourceKind query)) :=
  RawCtxGenericFamilyBudgets.family_step symbolicCalls publicInject _ kdfWeight receive_kdf send_kdf
    (fun query => (public_kdf query).mono (Nat.zero_le _)) sender route decode query roles

/-- A computation over a shared state and log adds at most `bound` log entries. -/
def LogBound {σ β : Type} (bound : Nat) (work : StateT (σ × Log) ProbComp β) : Prop :=
  ∀ state, ∀ result ∈ support (work.run state), result.2.2.length ≤ state.2.length + bound

/-- A return adds no log entry. -/
theorem log_pure {σ β : Type} (value : β) : LogBound (σ := σ) 0 (pure value) := by
  intro state result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  subst supported
  exact Nat.le_add_right _ _

/-- A log bound can be weakened. -/
theorem log_mono {σ β : Type} {work : StateT (σ × Log) ProbComp β} {first second : Nat} (bound : LogBound first work)
    (le : first ≤ second) : LogBound second work := fun state result supported => (bound state result supported).trans (by omega)

/-- Log bounds add along a bind. -/
theorem log_bind {σ β γ : Type} {first second : Nat} (work : StateT (σ × Log) ProbComp β)
    (continuation : β → StateT (σ × Log) ProbComp γ) (head : LogBound first work)
    (rest : ∀ value, LogBound second (continuation value)) : LogBound (first + second) (work >>= continuation) := by
  intro state result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, middleSupported, restSupported⟩ := supported
  have one := head state middle middleSupported
  have two := rest middle.1 middle.2 result restSupported
  omega

/-- Mapping the result of a computation keeps its log bound. -/
theorem log_map {σ β γ : Type} {bound : Nat} (work : StateT (σ × Log) ProbComp β) (function : β → γ)
    (head : LogBound bound work) : LogBound bound (function <$> work) := by
  intro state result supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨middle, middleSupported, rfl⟩ := supported
  exact head state middle middleSupported

/-- A shared-state service run beside an unchanged log adds no log entry. -/
theorem log_keep {β : Type} (work : StateT (RawCtxSharedPrimitive.SharedState A) ProbComp β) : LogBound 0 (keepLog work) := by
  intro state result supported
  simp only [keepLog, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨_, _, rfl⟩ := supported
  exact Nat.le_add_right _ _

/-- A record primitive program with at most `budget` private derivation requests adds at most `budget` log entries under the target-free services. -/
theorem log_labels {β : Type} (work : OracleComp LabelSpec β) (budget : Nat)
    (bounded : work.IsQueryBoundP (fun query => kdfQuery query = true) budget) :
    LogBound (σ := RawCtxSharedPrimitive.SharedState A) budget (simulateQ (taggedLabels source writer prior key nonce next) work) :=
  fun state => labels_growth source writer prior key nonce next work budget bounded state

/-- A tagged send adds at most one log entry. -/
theorem send_log (kernel : TKernel) (context : RawCtxSourceSend.SealContext) :
    LogBound 1 ((taggedCalls (A := A) source writer prior key nonce next).send kernel context) :=
  log_labels source writer prior key nonce next _ 1 (send_kdf kernel context)

end LogGrowth

section WorldGrowth
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)

/-- The tagged first receive of an attempted finish adds at most fifty-one log entries. -/
theorem stage_log (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : TKernel) (raw : Pqxdh.Bytes) :
    LogBound 51 (taggedStage (A := A) (N := N) (C := C) source writer prior key nonce next decode candidate kernel raw) := by
  unfold taggedStage
  rw [← RawCtxGenericOwnerInterpretation.raw_interpretation]
  exact log_map _ _ (log_labels source writer prior key nonce next _ 51
    (RawCtxGenericFamilyBudgets.owner_raw symbolicCalls _ 51 receive_kdf decode raw _))

variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)

/-- The target-free attempted finish adds at most fifty-one log entries. -/
theorem finish_log (raw : Pqxdh.Bytes) (before : BeaconState TKernel I D K) :
    LogBound 51 (taggedFinish source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage
      other raw before) := by
  unfold taggedFinish
  split
  · refine log_mono (log_bind (first := 0) (second := 51) _ _ (log_keep _) fun prepared => ?_) (by omega)
    rcases prepared with _ | pending
    · exact log_mono (log_pure _) (by omega)
    · refine log_mono (log_bind (first := 0) (second := 51) _ _ (log_keep _) fun kernel => ?_) (by omega)
      rcases kernel with _ | kernel
      · exact log_mono (log_pure _) (by omega)
      · refine log_mono (log_bind (first := 0) (second := 51) _ _ (log_keep _) fun reply => ?_) (by omega)
        rcases reply with _ | delivered
        · exact log_mono (log_bind (first := 0) (second := 0) _ _ (log_pure _) fun _ => log_pure _) (by omega)
        · exact log_mono (log_bind (first := 51) (second := 0) _ _ (stage_log source writer prior key nonce next decode _ _ _)
            fun _ => log_pure _) (by omega)
  · exact log_mono (log_pure _) (by omega)

/-- The private derivation weight of a world operation: the record weight, fifty-one for an attempted finish, none for reveals and selectors. -/
def worldWeight : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain → Nat
  | .inl (.inl (.inl request)) => kdfWeight (RawCtxProtocolBudgets.sourceKind request)
  | .inl (.inl (.inr _)) => 0
  | .inl (.inr _) => 0
  | .inr _ => 51

/-- Every operation of the tagged world adds at most its private derivation weight to the log. -/
theorem world_growth (query : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain) (state : TState M P I D K A N C S B)
    (result : (Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × TState M P I D K A N C S B)
    (supported : result ∈ support ((world source writer prior key nonce next sender route decode pre application initialW selector aux
      (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other)
      query).run state)) :
    result.2.shared.2.length ≤ state.shared.2.length + worldWeight query := by
  rcases query with ((request | request) | request) | ⟨index, raw⟩
  · simp only [world, taggedRecord, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    exact labels_growth source writer prior key nonce next _ _ (step_kdf sender route decode request state.front.roles) state.shared
      inner innerSupported
  · simp only [world, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact Nat.le_add_right _ _
  · simp only [world, taggedSelector, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact Nat.le_add_right _ _
  · have finished : result ∈ support ((taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux
        fixed selectedMessage other index raw).run state) := supported
    simp only [taggedFinishOp, StateT.run, support_map] at finished
    obtain ⟨inner, innerSupported, rfl⟩ := finished
    exact finish_log source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other raw _
      state.shared inner innerSupported

end WorldGrowth

section Budget
open PqxdhPhase2SourceSchedulerBounds (Kind classify)

/-- The private derivation weight of a certified post query kind: one per send, fifty-one per raw receive and per attempted finish. -/
def stopWeight (kind : Kind) : Nat :=
  if kind = .inl .send then 1 else if kind = .inl .raw then 51 else if kind = .inr 5 then 51 else 0

/-- The derivation potential of a post query budget. -/
def stopPotential (budget : Kind → Nat) : Nat :=
  budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5))

/-- One query of a kind with positive budget pays its weight out of the potential. -/
theorem stop_drop (budget : Kind → Nat) (kind : Kind) (positive : 0 < budget kind) :
    stopWeight kind + stopPotential (Function.update budget kind (budget kind - 1)) ≤ stopPotential budget := by
  unfold stopWeight stopPotential
  by_cases send : kind = .inl .send
  · subst send
    simp only [ite_true, Function.update_self]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    omega
  · by_cases raw : kind = .inl .raw
    · subst raw
      simp only [ite_true, Function.update_self, reduceCtorEq, Sum.inl.injEq, ite_false]
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
      omega
    · by_cases finish : kind = .inr 5
      · subst finish
        simp only [ite_true, Function.update_self, reduceCtorEq, ite_false]
        rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        omega
      · simp only [send, raw, finish, ite_false]
        rw [Function.update_of_ne (Ne.symm send), Function.update_of_ne (Ne.symm raw), Function.update_of_ne (Ne.symm finish)]
        omega

/-- The world weight of a scheduler query is at most the stop weight of its certified kind. -/
theorem weight_classify {ι : Type} {baseSpec : OracleSpec ι} {S B : Nat}
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain) :
    worldWeight (extra := PqxdhPrivateKemSource.SelectorSpec baseSpec) query ≤ stopWeight (classify query) := by
  rcases query with ((request | request) | request) | request
  · rcases request with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (hash | hkdf)))
    all_goals simp [worldWeight, kdfWeight, classify, stopWeight, RawCtxProtocolBudgets.sourceKind]
  · simp [worldWeight]
  · simp [worldWeight]
  · simp [worldWeight, classify, stopWeight]

end Budget

section BuilderLog
open ratchet.refined
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhRefinement RawCtxGenericRoleStorage
variable {Kernel M P Consumed σ : Type} (calls : RawCtxChainOwner.Calls Kernel (StateT (σ × Log) ProbComp))
  (aux : QueryImpl AuxSpec (StateT (σ × Log) ProbComp))
  (sendLog : ∀ kernel context, LogBound 1 (calls.send kernel context)) (auxLog : ∀ query, LogBound 0 (aux query))

include sendLog auxLog in
/-- The first-send tail of the builder adds at most one log entry. -/
theorem after_log (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : Kernel)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P Consumed) :
    LogBound 1 (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state) := by
  unfold PqxdhInitialGenericPublication.afterInitialization
  refine log_mono (log_bind (first := 1) (second := 0) _ _ (sendLog _ _) fun sent => ?_) (by omega)
  obtain ⟨advanced, encrypted⟩ := sent
  refine log_mono (log_bind (first := 0) (second := 0) _ _ (auxLog _) fun _ => ?_) (by omega)
  cases encrypted with
  | none => exact log_pure _
  | some encrypted =>
    refine log_mono (log_bind (first := 0) (second := 0) _ _ (auxLog _) fun serialized => ?_) (by omega)
    cases serialized <;> exact log_pure _

include sendLog auxLog in
/-- The Ready builder adds at most one log entry. -/
theorem ready_log (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (kernel : Kernel)
    (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready) (metadata : P)
    (state : PqxdhInitialGenericPublication.State Kernel M P Consumed) :
    LogBound 1 (PqxdhInitialGenericBuilder.readyBuild source calls aux (.ok kernel) binding ready metadata state) := by
  unfold PqxdhInitialGenericBuilder.readyBuild PqxdhInitialGenericBuilder.usedBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => exact log_mono (log_pure _) (by omega)
  | div => exact log_mono (log_pure _) (by omega)
  | ok result =>
    cases result with
    | Err error => exact log_mono (log_pure _) (by omega)
    | Ok key =>
      simp only [PqxdhInitialGenericBuilder.continueRust]
      cases prepared : PqxdhRegistrationInputs.prepare state.control (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
          ⟨state.server.identity, state.identityKeyId⟩
          (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
      | fail error => exact log_mono (log_pure _) (by omega)
      | div => exact log_mono (log_pure _) (by omega)
      | ok value =>
        cases value with
        | Err error => exact log_mono (log_pure _) (by omega)
        | Ok candidate =>
          unfold PqxdhInitialGenericBuilder.candidate
          refine log_mono (log_bind (first := 0) (second := 1) _ _ (auxLog _) fun valid => ?_) (by omega)
          split
          · exact log_mono (log_pure _) (by omega)
          · refine log_mono (log_bind (first := 0) (second := 1) _ _ (auxLog _) fun reserved => ?_) (by omega)
            split
            · exact log_mono (log_pure _) (by omega)
            · simp only [PqxdhInitialGenericBuilder.continueRust]
              split
              · exact log_mono (log_pure _) (by omega)
              · split
                · refine log_mono (log_bind (first := 0) (second := 1) _ _ (auxLog _) fun allocated => ?_) (by omega)
                  split
                  · exact log_mono (log_pure _) (by omega)
                  · cases candidate.key_id_binding with
                    | fail error => exact log_mono (log_pure _) (by omega)
                    | div => exact log_mono (log_pure _) (by omega)
                    | ok bound =>
                      simp only
                      exact log_map _ _ (after_log calls aux sendLog auxLog _ _ _ _ _)
                · exact log_mono (log_pure _) (by omega)

end BuilderLog

section StartFacts
open ratchet.refined
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {M P I D K : Type} {S B : Nat}

/-- The zero-state constructor installs the requested send chain. -/
theorem new_send {Send Receive Material : Type} (send : Send) (receive : Receive) (kernel : RefinedRatchet Send Receive Material)
    (created : RefinedRatchet.new Material send receive = ok kernel) : kernel.send_chain = send := by
  simp only [RefinedRatchet.new, RefinedRatchet.from_counters] at created
  cases counters : control.RatchetState.from_counters 0#u64 0#u64 with
  | ok state =>
    cases slots : empty_material_slots Material with
    | ok empty =>
      simp only [counters, slots, bind_tc_ok, RustM.ok.injEq] at created
      rw [← created]
    | fail error => simp [counters, slots] at created
    | div => simp [counters, slots] at created
  | fail error => simp [counters] at created
  | div => simp [counters] at created

/-- The finish kernel on the selected message has the hidden send chain. -/
theorem hidden_send (other : RootOutput) : (hiddenKernel other).send_chain = .hidden := by
  change (hiddenBase other).send_chain = _
  exact new_send _ _ _ (new_total .hidden (.known (RawCtxFreshChainCut.concreteChain other))).choose_spec

/-- The tagged Server kernel of the initializer has a known send chain. -/
theorem server_known (other : RootOutput) : KnownSend (serverKernel other) := by
  unfold KnownSend
  have sent : (serverBase other).send_chain = .known (RawCtxFreshChainCut.concreteChain other) :=
    new_send _ _ _ (new_total (.known (RawCtxFreshChainCut.concreteChain other)) .hidden).choose_spec
  change isHidden (serverBase other).send_chain = false
  rw [sent]
  rfl

/-- The selected root of a Beacon owner for the 64-byte initializer response `other ++ target` is `target`. -/
theorem beacon_root (source : FixedHkdfSha512NoSaltSource) (other target : RootOutput) (b : Fin B) :
    PqxdhInitialSourceExperiment.root source (List.Vector.replicate 32 0)
      (RawCtxSelectedInitialConstructor.response64 (other ++ target)) (.beacon b : RawCtxProtocolReveals.Owner S B) = target := by
  have chain := congrArg RefinedRatchet.send_chain (marked_kernel (List.Vector.replicate 32 0) other target)
  have rhs : (mapKernel target (hiddenKernel other)).send_chain = RawCtxFreshChainCut.concreteChain target := by
    change reveal target (hiddenKernel other).send_chain = _
    rw [hidden_send]
    rfl
  rw [rhs] at chain
  change RawCtxSelectedQueryTrace.rootVector (PqxdhInitialRootAudit.kernel (List.Vector.replicate 32 0,
    RawCtxSelectedInitialConstructor.response64 (other ++ target))).refined.send_chain = target
  change (PqxdhInitialRootAudit.kernel (List.Vector.replicate 32 0,
    RawCtxSelectedInitialConstructor.response64 (other ++ target))).refined.send_chain = _ at chain
  rw [chain]
  exact RawCtxSelectedQueryTrace.rootVector_concrete target

/-- Every Server peer of the all-known tagged image of a front has a known send chain. -/
theorem front_servers (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (index : Fin S) (kid : Std.U64)
    (peer : Peer TKernel P) (found : ((frontOf front).roles.1 index).server.peers kid = some peer) : KnownSend peer.kernel := by
  simp only [frontOf, mapRoles, mapServer, Option.map_eq_some_iff] at found
  obtain ⟨original, _, rfl⟩ := found
  rfl

/-- Every established Beacon of the all-known tagged image of a front has a known send chain. -/
theorem front_beacons (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (index : Fin B) :
    ∀ control associated kernel, ((frontOf front).roles.2 index).beacon.phase = .established control associated kernel →
      KnownSend kernel := by
  intro control associated kernel found
  simp only [frontOf, mapRoles, mapBeacon] at found
  cases phase : (front.roles.1.2 index).beacon.phase <;> simp only [phase, mapPhase, reduceCtorEq] at found
  obtain ⟨-, -, rfl⟩ := found
  rfl

end StartFacts
section PostTriple
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initialC initialW : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (other : RootOutput)
    (first : Fin B) (Markable : K → Prop)

/-- Relational form of `post_bound`: the concrete source post and the tagged world are coupled so that the restricted repetition event of the concrete run implies that the selected value is logged by the tagged world. -/
theorem post_triple {Result : Type} (target : RootOutput)
    (marked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true →
      ∀ start : RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache), ∀ result ∈ support
        ((PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialC selector aux
          (.inr (.inr (.inl secrets)))).run start),
        result.1.map PqxdhSelectedMessageBeacon.knownKernel = some (mapKernel target (hiddenKernel other)) ∧
          strip result.2.1 = strip start.1 ∧ result.2.2 = start.2)
    (unmarked : ∀ secrets, PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = false → initialC secrets = initialW secrets)
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application initialW selector aux (.inl query))
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true → Markable kem)
    (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (start : Concrete M P I D K A N RootOracle.QueryCache S B) (tagged : TState M P I D K A N RootOracle.QueryCache S B)
    (represents : Represents target start tagged) (good : GoodState first Markable tagged) :
    RelTriple ((simulateQ (PqxdhFirstRecordNonceStop.sourceObserved (extra := extra) pre application initialC selector aux source writer
        prior none key target nonce next sender route decode) client).run start)
      ((simulateQ (world source writer prior key nonce next sender route decode pre application initialW selector aux
        (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other))
        client).run tagged)
      (fun left right => RawCtxSelectedSourceSendInputs.RepeatedInput target left.2.1 ∧
        PqxdhFirstBeaconRecordIntegrity.Undisclosed target [] [] left.2.2 → Exposed target right.2) := by
  refine relTriple_post_mono (post_coupled source writer prior key nonce next sender route decode pre application initialC selector
    aux initialW (taggedFinishOp source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage
      other) target (GoodState first Markable)
    (good_step source writer prior key nonce next sender route decode pre application initialW selector aux fixed selectedMessage other
      first Markable markable)
    (fun index raw left right leftRepresents _ _ _ => finish_step source writer prior key nonce next sender route decode pre application
      selector aux fixed selectedMessage other initialC initialW target marked unmarked index raw left right leftRepresents)
    (finish_keeps source writer prior key nonce next decode pre application initialW selector aux fixed selectedMessage other target)
    client start tagged represents good) ?_
  intro left right held holds
  obtain ⟨repeated, undisclosed⟩ := holds
  rcases held with disclosed | exposed | ⟨_, leftRepresents, rightGood⟩
  · exact absurd disclosed (undisclosed _ (List.mem_singleton_self _))
  · exact exposed
  · by_contra fresh
    have once : hiddenCount right.2.seals ≤ 1 := by
      have := rightGood.once
      omega
    exact repeated_impossible target left.2.1 right.2.seals right.2.shared.2 leftRepresents.2.2.2.2 rightGood.logged once fresh
      repeated

end PostTriple

section TaggedStart
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily RawCtxSelectedMessageDriver
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
  (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The tagged first Server builder adds at most one log entry. -/
theorem build_log (other : RootOutput) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (tagged : TFront M P I D K S B) :
    LogBound 1 (taggedBuild (X := X) (extra := extra) source writer prior key nonce next sender pre application initial selector aux other
      index metadata ready tagged) :=
  log_map _ _ (ready_log _ _ (send_log source writer prior key nonce next) (fun _ => log_keep _) source _ _ _ _ _)

/-- A tagged front whose Server peers and established Beacons all have known send chains and whose Beacons other than the first cannot be marked. -/
structure StartFront (first : Fin B) (Markable : K → Prop) (tagged : TFront M P I D K S B) : Prop where
  servers : ∀ index kid peer, (tagged.roles.1 index).server.peers kid = some peer → KnownSend peer.kernel
  beacons : ∀ index control associated kernel, (tagged.roles.2 index).beacon.phase = .established control associated kernel →
    KnownSend kernel
  unmarkable : ∀ index, index ≠ first → ∀ control prekey oneTime kem,
    (tagged.roles.2 index).beacon.phase = .initSent control prekey oneTime kem → ¬ Markable kem

/-- After the tagged first Server builder from a start front, the tagged world starts in its invariant. -/
theorem build_good (other : RootOutput) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (first : Fin B) (Markable : K → Prop) (tagged : TFront M P I D K S B) (valid : StartFront first Markable tagged)
    (state : RawCtxSharedPrimitive.SharedState (Local A N C) × Log)
    (built : (RustM (Option PqxdhServerRegistrationPublication.Response) × TFront M P I D K S B) ×
      (RawCtxSharedPrimitive.SharedState (Local A N C) × Log))
    (supported : built ∈ support ((taggedBuild (X := X) (extra := extra) source writer prior key nonce next sender pre application
      initial selector aux other index metadata ready tagged).run state)) :
    GoodState first Markable (⟨[], built.1.2, built.2⟩ : TState M P I D K A N C S B) := by
  change built ∈ support ((tReinstall index (tConsume index ready tagged) <$> PqxdhInitialGenericBuilder.readyBuild source
    (taggedCalls source writer prior key nonce next)
    (fun query => keepLog (PqxdhSelectedFirstRecord.serverAux (X := X) (extra := extra) pre application initial selector aux query))
    (.ok (serverKernel other)) ⟨(tServer sender index (tConsume index ready tagged)).server.identity,
      (tServer sender index (tConsume index ready tagged)).identityKeyId⟩ ready metadata
    (tServer sender index (tConsume index ready tagged))).run state) at supported
  rw [StateT.run_map, support_map] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  have known := ready_known (taggedCalls source writer prior key nonce next)
    (fun query => keepLog (PqxdhSelectedFirstRecord.serverAux (X := X) (extra := extra) pre application initial selector aux query))
    (send_known source writer prior key nonce next) source (serverKernel other) (server_known other) _ ready metadata
    (tServer sender index (tConsume index ready tagged)) (fun kid peer found => valid.servers index kid peer found) state inner
    innerSupported
  have beaconsSame : ((tReinstall index (tConsume index ready tagged) inner.1).2.roles.2) = tagged.roles.2 := by
    cases inner.1 <;> rfl
  refine ⟨?_, ?_, ?_, ?_, logged_nil _⟩
  · intro position kid peer found
    change ((tReinstall index (tConsume index ready tagged) inner.1).2.roles.1 position).server.peers kid = some peer at found
    cases result : inner.1 with
    | ok value =>
      rw [result] at found
      simp only [tReinstall, tInstall] at found
      by_cases same : position = index
      · subst same
        simp only [Function.update_self] at found
        exact known value result kid peer found
      · simp only [Function.update_of_ne same] at found
        exact valid.servers position kid peer found
    | fail error =>
      rw [result] at found
      exact valid.servers position kid peer found
    | div =>
      rw [result] at found
      exact valid.servers position kid peer found
  · intro position _ control associated kernel found
    change ((tReinstall index (tConsume index ready tagged) inner.1).2.roles.2 position).beacon.phase = _ at found
    rw [beaconsSame] at found
    exact valid.beacons position control associated kernel found
  · intro position different control prekey oneTime kem found
    change ((tReinstall index (tConsume index ready tagged) inner.1).2.roles.2 position).beacon.phase = _ at found
    rw [beaconsSame] at found
    exact valid.unmarkable position different control prekey oneTime kem found
  · have hidden : firstHidden first (tReinstall index (tConsume index ready tagged) inner.1).2.roles = 0 := by
      unfold firstHidden
      rw [beaconsSame]
      split
      · rename_i control associated kernel phase
        rw [valid.beacons first control associated kernel phase]
        rfl
      · rfl
    have markable : firstMarkable first Markable (tReinstall index (tConsume index ready tagged) inner.1).2.roles ≤ 1 := by
      unfold firstMarkable
      split
      · split <;> omega
      · omega
    change hiddenCount [] + firstHidden first _ + firstMarkable first Markable _ ≤ 1
    rw [hidden]
    simp only [hiddenCount, List.countP_nil]
    omega

end TaggedStart

section TaggedGame
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
open PqxdhSelectedPostCompiler (Optional)
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A Boolean output of a bound computation is at most a logged-value event of another bound computation, given a coupling of the unmapped computations under which the output implies the event. -/
theorem bind_event_le {α β γ δ : Type} (first : ProbComp α) (rest : α → ProbComp β) (other : ProbComp γ) (later : γ → ProbComp δ)
    (output : β → Bool) (log : δ → Log) (target : RootOutput)
    (coupled : RelTriple (first >>= rest) (other >>= later) (fun left right => output left = true → target ∈ log right)) :
    𝒟[first >>= fun value => output <$> rest value] {true} ≤ Pr[fun values => target ∈ values | other >>= fun value => log <$> later value] := by
  have left : (first >>= fun value => output <$> rest value) = output <$> (first >>= rest) := by rw [map_bind]
  have right : (other >>= fun value => log <$> later value) = log <$> (other >>= later) := by rw [map_bind]
  rw [left, right, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
  exact probEvent_le_of_relTriple coupled fun _ _ held holds => held holds

variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))

/-- The Server auxiliary callbacks of the builder do not use the initializer callback. -/
theorem server_aux_initial (initial initial' : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply) :
    PqxdhSelectedFirstRecord.serverAux (X := X) pre application initial selector aux =
      PqxdhSelectedFirstRecord.serverAux (X := X) pre application initial' selector aux := by
  funext request
  rfl

/-- The tagged first Server builder does not use the initializer callback. -/
theorem build_initial (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (sender : M → Std.U64)
    (initial initial' : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (other : RootOutput) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready) :
    taggedBuild (X := X) (extra := extra) (I := I) (D := D) (K := K) (B := B) source writer prior key nonce next sender pre application
        initial selector aux other index metadata ready =
      taggedBuild source writer prior key nonce next sender pre application initial' selector aux other index metadata ready := by
  unfold taggedBuild
  rw [server_aux_initial pre application selector aux initial initial']

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store)

/-- The target-free initializer callback: the retained initializer with the selected half of the response replaced by zero bytes. -/
noncomputable def initialFree (other : RootOutput) :
    PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply :=
  initialLocal source selectedMessage (List.Vector.replicate 32 0)
    (RawCtxSelectedInitialConstructor.response64 (other ++ (List.Vector.replicate 32 0 : RootOutput)))

/-- The target-free tagged run of the source stop game with opposite initializer half `other`: the tagged first Server builder on the all-known image of the prepared front, then the tagged world on the post client; it returns the final derivation log. Neither the selected half of the initializer response nor any value derived from it is an argument. -/
noncomputable def taggedRun (other key : RootOutput) (nonce : NonceOutput) (next : RootOutput) : ProbComp Log := do
  let built ← (taggedBuild (X := X) (extra := extra) source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender pre application
    (initialFree source selectedMessage other) selector aux other index metadata ready (frontOf (PqxdhSelectedFirstRecord.initialFront before))).run
    (PqxdhSelectedFirstRecord.initialShared shared privateState cache store, [])
  (fun result => result.2.shared.2) <$> (simulateQ (world source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender route decode
    pre application (initialFree source selectedMessage other) selector aux
    (taggedFinishOp source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next decode pre application
      (initialFree source selectedMessage other) selector aux source selectedMessage other))
    (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run ⟨[], built.1.2, built.2⟩

/-- The source-only restricted repetition run of a Beacon owner, with initializer response `other ++ target`, is at most the probability that `target` is in the final log of the target-free tagged run. The premises are the preparation fact of the actual callbacks (a marked preparation has a markable KEM handle) and the start-front fact (only the first Beacon can be marked), discharged for the actual game separately. -/
theorem stop_tagged (other target key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b first : Fin B) (Markable : K → Prop)
    (markable : ∀ control identity prekey oneTime kem raw state, ∀ result ∈ support ((simulateQ (fun query =>
      PqxdhSelectedInitialOwnerCompiler.sourceExternal (X := X) pre application (initialFree source selectedMessage other) selector aux
        (.inl query)) (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark source selectedMessage pending.root = true → Markable kem)
    (valid : StartFront first Markable (frontOf (PqxdhSelectedFirstRecord.initialFront before))) :
    𝒟[PqxdhFirstRecordStopBound.sourceStopRun pre application
        (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
        selector aux source writer (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)) sender
        route decode index metadata ready post before (.beacon b) shared privateState cache store key nonce next [] []] {true} ≤
      Pr[fun log => target ∈ log | taggedRun pre application selector aux source writer selectedMessage sender route decode index metadata
        ready post before shared privateState cache store other key nonce next] := by
  unfold PqxdhFirstRecordStopBound.sourceStopRun PqxdhFirstBeaconRecordIntegrity.firstBuild taggedRun
  rw [beacon_root]
  refine bind_event_le _ _ _ _ _ _ target ?_
  rw [← build_initial pre application selector aux source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender
    (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
    (initialFree source selectedMessage other) other index metadata ready]
  refine relTriple_bind (support_right (build_coupled source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender pre application
    (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
    selector aux target other index metadata ready (PqxdhSelectedFirstRecord.initialFront before) (frontOf (PqxdhSelectedFirstRecord.initialFront before)) (front_rep target _)
    (PqxdhSelectedFirstRecord.initialShared shared privateState cache store) (PqxdhSelectedFirstRecord.initialShared shared privateState cache store, []) ⟨rfl, rfl⟩
    (List.not_mem_nil))) ?_
  intro left right held
  obtain ⟨held, rightSupported⟩ := held
  have good := build_good source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender pre application
    (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
    selector aux other index metadata ready first Markable _ valid _ right rightSupported
  rcases held with bad | ⟨⟨sameReply, sameFront⟩, near⟩
  · refine relTriple_post_mono (product_coupling (P := fun _ => True) (fun _ _ => trivial)
      (run_absorbing _ (Exposed target) (exposed_absorbing source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender route
        decode pre application selector aux (initialFree source selectedMessage other) _ target
        (finish_keeps source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next decode pre application
          (initialFree source selectedMessage other) selector aux source selectedMessage other target)) _ _ bad)) ?_
    intro _ _ held _
    exact held.2
  · rw [sameReply]
    refine relTriple_post_mono (post_triple source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender route decode pre application
      (initialLocal source selectedMessage (List.Vector.replicate 32 0) (RawCtxSelectedInitialConstructor.response64 (other ++ target)))
      (initialFree source selectedMessage other) selector aux source selectedMessage other first Markable target
      (fun secrets selected start result supported => initial_marked pre application selector aux source selectedMessage other target
        secrets selected start result supported)
      (fun secrets unmarkedMark => initial_unmarked source selectedMessage _ _ _ _ secrets unmarkedMark)
      markable _ ([], (left.1.2, left.2)) ⟨[], right.1.2, right.2⟩
      ⟨sameFront.1, sameFront.2.1, sameFront.2.2, near, rfl⟩ good) ?_
    intro _ _ held holds
    exact held (of_decide_eq_true holds)

end TaggedGame

section RunLog
open ratchet.refined OracleComp.ProgramLogic.Relational
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame RawCtxSelectedParentTable PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open PqxdhSelectedPostCompiler (Optional)
open PqxdhPhase2SourceSchedulerBounds (Kind classify)

/-- The optional translation of a client keeps every predicate query bound of the client. -/
theorem optional_bound {κ α : Type} {spec : OracleSpec κ} (p : κ → Prop) [DecidablePred p] (client : OracleComp spec α)
    (budget : Nat) (bounded : client.IsQueryBoundP p budget) :
    (RawCtxSelectedFamilyNonceCoupling.optionalClient client).IsQueryBoundP p budget := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure value => simp [RawCtxSelectedFamilyNonceCoupling.optionalClient]
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [RawCtxSelectedFamilyNonceCoupling.optionalClient, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
      Option.elimM, RawCtxSelectedFamilyNonceCoupling.optionalRequests, OptionT.run_mk]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨bounded.1, fun reply => ?_⟩
    cases reply with
    | none => simp
    | some value => exact ih value _ (bounded.2 value)

variable {ι M P I D K X Response A N : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl (PqxdhPrivateKemSource.SelectorSpec baseSpec) (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store)

/-- Every final log of the target-free tagged run has at most one entry from the builder plus the derivation potential of the post query budget. -/
theorem run_log (budget : Kind → Nat)
    (bounded : ∀ reply kind, (post reply).IsQueryBoundP (fun query => classify (baseSpec := baseSpec) query = kind) (budget kind))
    (other key : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    ∀ log ∈ support (taggedRun pre application selector aux source writer selectedMessage sender route decode index metadata ready post
      before shared privateState cache store other key nonce next), log.length ≤ 1 + stopPotential budget := by
  intro log supported
  unfold taggedRun at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨built, builtSupported, rest⟩ := supported
  rw [support_map] at rest
  obtain ⟨result, resultSupported, rfl⟩ := rest
  have first := build_log source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next sender pre application
    (initialFree source selectedMessage other) selector aux other index metadata ready _ _ built builtSupported
  have second := weighted_growth _ (fun state : TState M P I D K A N RootOracle.QueryCache S B => state.shared.2.length) classify
    stopWeight stopPotential
    (fun query state result supported => (world_growth source writer (PqxdhJointKdf.productionStream source.crypto) key nonce next
      sender route decode pre application (initialFree source selectedMessage other) selector aux source selectedMessage other query
      state result supported).trans (Nat.add_le_add_left (weight_classify query) _))
    stop_drop _ budget (fun kind => optional_bound _ _ _ (bounded built.1.1 kind)) _ result resultSupported
  simp only [List.length_nil] at first
  change result.2.shared.2.length ≤ built.2.2.length + stopPotential budget at second
  change result.2.shared.2.length ≤ 1 + stopPotential budget
  omega

end RunLog

section Sampling
open PqxdhSecretInputKdf

/-- A pointwise bound on the `true` mass of two continuations over the support of a common first computation bounds the `true` mass of the binds. -/
theorem bind_le_support {α : Type} (first : ProbComp α) (left right : α → ProbComp Bool)
    (le : ∀ value ∈ support first, 𝒟[left value] {true} ≤ 𝒟[right value] {true}) :
    𝒟[first >>= left] {true} ≤ 𝒟[first >>= right] {true} := by
  simp only [evalDist_apply_singleton] at le ⊢
  simp only [probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases supported : value ∈ support first
  · gcongr
    exact le value supported
  · rw [probOutput_eq_zero_of_not_mem_support supported, zero_mul, zero_mul]

/-- A uniform 32-byte value drawn before a computation that does not depend on it lies in the computation's final log with probability at most the log-length bound divided by `2^256`. -/
theorem delayed_bound (run : ProbComp Log) (budget : Nat) (bounded : ∀ log ∈ support run, log.length ≤ budget) :
    Pr[= true | $ᵗ RootOutput >>= fun target => (fun log => decide (target ∈ log)) <$> run] ≤ (budget : ℝ≥0∞) / 2 ^ 256 := by
  have swapped := evalSPMF_sample_comm_vcvioLegacy ($ᵗ RootOutput) run (fun target log => (pure (decide (target ∈ log)) : ProbComp Bool))
  have shape : ($ᵗ RootOutput >>= fun target => (fun log => decide (target ∈ log)) <$> run) =
      ($ᵗ RootOutput >>= fun target => run >>= fun log => pure (decide (target ∈ log))) := by
    simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [shape, probOutput_def, swapped, ← probOutput_def, ← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun log supported => ?_
  have uniform : Pr[(· = true) | $ᵗ RootOutput >>= fun target => (pure (decide (target ∈ log)) : ProbComp Bool)] =
      Pr[fun target => target ∈ log | $ᵗ RootOutput] := by
    rw [bind_pure_comp, probEvent_map]
    congr 1
    funext target
    simp only [Function.comp_apply, decide_eq_true_eq]
  rw [uniform]
  exact (RawCtxSelectedInputCandidates.uniform_candidates_vcvioLegacy log).trans
    (ENNReal.div_le_div_right (by exact_mod_cast bounded log supported) _)

end Sampling

section Discharge
open PqxdhBeaconPhase2Shared PqxdhJointKdfGame
open PqxdhGeneratedBeaconState (KemHandle)

/-- Under a preparation interface that never answers the challenge marker at existing KEM handles, a marked successful preparation holds a generated KEM handle. -/
theorem existing_markable {σ I D K X Response : Type}
    (pre : QueryImpl (Spec I D (KemHandle K) X Response PqxdhPhase2DecapsulationRouting.Shared) (StateT σ ProbComp))
    (never : NeverChallenge pre) (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message) :
    ∀ control identity prekey oneTime (handle : KemHandle K) raw state,
      ∀ result ∈ support ((simulateQ pre (prepare control identity prekey oneTime handle raw)).run state),
      ∀ pending, result.1 = some pending → PqxdhInitialSelectedOrigin.mark fixed selectedMessage pending.root = true →
        ¬ PqxdhFirstRecordStopBound.ExistingKem handle := by
  intro control identity prekey oneTime handle raw state result supported pending found marked existing
  cases handle with
  | existing prior =>
    have unmarked := lifted_unmarked pre never fixed selectedMessage control identity prekey oneTime prior raw state result supported
      pending found
    rw [unmarked] at marked
    cases marked
  | generated _ _ => exact existing

/-- The all-known tagged image of a prepared front in which only slot zero may hold a generated KEM handle is a start front for slot zero and the markable handles that are not existing. -/
theorem start_front {M P I D K : Type} {S B : Nat} (before : PqxdhInitialOriginPostPath.Front M P I D (KemHandle K) S (B + 1))
    (onlyFirst : PqxdhFirstRecordStopBound.OnlyFirst (fun position => (before.roles.1.2 position).beacon.phase)) :
    StartFront 0 (fun handle => ¬ PqxdhFirstRecordStopBound.ExistingKem handle) (frontOf (PqxdhSelectedFirstRecord.initialFront before)) := by
  refine ⟨front_servers _, front_beacons _, ?_⟩
  intro position nonzero control prekey oneTime handle found existing
  have retains : PqxdhFirstRecordStopBound.Retains
      ((frontOf (PqxdhSelectedFirstRecord.initialFront before)).roles.2 position).beacon.phase :=
    PqxdhFirstRecordStopBound.map_retains _ _ (PqxdhFirstRecordStopBound.map_retains _ _
      (PqxdhFirstRecordStopBound.map_retains _ _ (onlyFirst position nonzero)))
  rw [found] at retains
  exact existing retains

end Discharge

section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity (emptyStore firstBeacon)
open PqxdhPhase2SourceSchedulerBounds (Kind classify)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- A pending prepared input keeps the requested selected owner. -/
theorem input_selected (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A)
      (S := S) (B := B) (setup := setup))
    (prepared : PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      selected number ancestors disclosed = .inr input) :
    input.selected = selected ∧ ∃ choice, input.post = post choice := by
  unfold PqxdhInitialPreparedSourceInput.input at prepared
  split at prepared
  · cases prepared
  · injection prepared with same
    subst same
    exact ⟨rfl, _, rfl⟩

/-- The final log of the target-free tagged run of one prepared context: empty for a completed preparation. -/
noncomputable def taggedLog (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (other key : RootOutput) (nonce : NonceOutput) (chain : RootOutput) : ProbComp Log :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure []
  | .inr input => taggedRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage (env0).senderId (env0).route (env0).decode input.index input.metadata
      { input.ready with root := zeroRoot } input.post input.before input.shared input.privateState input.cache emptyStore
      other key nonce chain

/-- The target-free tagged stop game: the samples of `sourceStopGame`, with the 64-byte initializer block split into its opposite half (an argument of the tagged run) and its selected half (tested against the final log only). -/
noncomputable def taggedGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  (fun log => decide (RawCtxSelectedInitialSampler.initialOther initialBlock ∈ log)) <$>
    taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context (first32 initialBlock) key nonce chain

/-- The `true` mass of a decided membership test is the membership probability. -/
theorem decide_mass (value : RootOutput) (run : ProbComp Log) :
    𝒟[(fun log => decide (value ∈ log)) <$> run] {true} = Pr[fun log => value ∈ log | run] := by
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  congr 1
  funext log
  simp only [Function.comp_apply, decide_eq_true_eq]

/-- The source-only restricted repetition game of the first record of Beacon `b` is at most the target-free tagged stop game. -/
theorem source_tagged (b : Fin (B + 1)) :
    𝒟[PqxdhFirstRecordStopBound.sourceStopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)]
      {true} ≤
    𝒟[taggedGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} := by
  unfold PqxdhFirstRecordStopBound.sourceStopGame taggedGame
  refine bind_le_support _ _ _ fun context supported => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun initialBlock => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun nonce => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun chain => ?_
  refine PqxdhFirstRecordStopBound.bind_le _ _ _ fun key => ?_
  unfold PqxdhFirstRecordStopBound.sourceStopObserve taggedLog
  cases prepared : PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed with
  | inl _ => simp
  | inr input =>
    obtain ⟨selected, _⟩ := input_selected setup env callbacks baseImpl kem attachedVerify primitives program post context _ _ _ _ input
      prepared
    have onlyFirst := PqxdhFirstRecordStopBound.front_only setup env callbacks baseImpl kem attachedVerify primitives program post
      (firstBeacon b) context supported input prepared
    simp only
    rw [selected, decide_mass]
    have split := RawCtxSelectedInitialConstructor.split_reconstruct initialBlock
    generalize first32 initialBlock = other at split ⊢
    generalize RawCtxSelectedInitialSampler.initialOther initialBlock = value at split ⊢
    subst split
    exact stop_tagged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ other value key nonce chain b 0 (fun handle => ¬ ExistingKem handle)
      (existing_markable (liftedPreparation
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
          context.secretKey context.ciphertext)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
          context.secretKey context.ciphertext)
        (initialFree (env0).source input.selectedMessage other)
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks))
        (lifted_unchallenged attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem context.secretKey context.ciphertext
          _ _ _ _) (env0).source input.selectedMessage)
      (start_front input.before onlyFirst)

/-- The target-free tagged stop game is at most the log-length bound divided by `2^256`: the selected half of the initializer block is uniform and independent of the tagged run, and every final log has at most one builder entry plus the derivation potential of the post query budget. -/
theorem tagged_game_bound (budget : Kind → Nat)
    (bounded : ∀ choice response, PqxdhPhase2SourceSchedulerBounds.Bounded (post choice response) budget) (target : Target S (B + 1)) :
    𝒟[taggedGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} ≤
      ((1 + stopPotential budget : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  unfold taggedGame
  rw [evalDist_apply_singleton, probOutput_def]
  have split : ∀ context, 𝒮[$ᵗ HmacBlock >>= fun initialBlock => $ᵗ NonceOutput >>= fun nonce => $ᵗ RootOutput >>= fun chain =>
      $ᵗ RootOutput >>= fun key => (fun log => decide (RawCtxSelectedInitialSampler.initialOther initialBlock ∈ log)) <$>
        taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context (first32 initialBlock) key
          nonce chain] =
      𝒮[$ᵗ RootOutput >>= fun other => $ᵗ RootOutput >>= fun value => $ᵗ NonceOutput >>= fun nonce => $ᵗ RootOutput >>= fun chain =>
        $ᵗ RootOutput >>= fun key => (fun log => decide (value ∈ log)) <$>
          taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context other key nonce chain] :=
    fun context => RawCtxSelectedInitialSecond.second_observed_vcvioLegacy (fun other value => $ᵗ NonceOutput >>= fun nonce =>
      $ᵗ RootOutput >>= fun chain => $ᵗ RootOutput >>= fun key => (fun log => decide (value ∈ log)) <$>
        taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context other key nonce chain)
  have equal := congrArg (fun distribution => distribution true) (evalSPMF_bind_congr' (PqxdhCorrelatedExtractFamily.prepare baseImpl
    kem (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)) split)
  refine (le_of_eq equal).trans ?_
  change Pr[= true | _] ≤ _
  rw [← probEvent_eq_eq_probOutput]
  refine probEvent_bind_le_of_forall_le fun context _ => ?_
  refine probEvent_bind_le_of_forall_le fun other _ => ?_
  rw [probEvent_eq_eq_probOutput]
  have shape : ($ᵗ RootOutput >>= fun value => $ᵗ NonceOutput >>= fun nonce => $ᵗ RootOutput >>= fun chain =>
      $ᵗ RootOutput >>= fun key => (fun log => decide (value ∈ log)) <$>
        taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context other key nonce chain) =
      ($ᵗ RootOutput >>= fun value => (fun log => decide (value ∈ log)) <$> ($ᵗ NonceOutput >>= fun nonce =>
        $ᵗ RootOutput >>= fun chain => $ᵗ RootOutput >>= fun key =>
          taggedLog setup env callbacks baseImpl kem attachedVerify primitives program post target context other key nonce chain)) := by
    simp only [map_bind]
  rw [shape]
  refine delayed_bound _ _ fun log supported => ?_
  simp only [mem_support_bind_iff] at supported
  obtain ⟨nonce, _, chain, _, key, _, supported⟩ := supported
  unfold taggedLog at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp
  · rename_i input prepared
    obtain ⟨_, choice, same⟩ := input_selected setup env callbacks baseImpl kem attachedVerify primitives program post context _ _ _ _
      input prepared
    exact run_log _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ budget (fun reply kind => same ▸ bounded choice reply kind) other key nonce chain
      log supported

/-- The derivation potential of a post query budget, spelled out. -/
theorem potential_bound (budget : Kind → Nat) :
    1 + stopPotential budget = 1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) := by
  unfold stopPotential
  omega

/-- The source-only restricted repetition game of the first record of Beacon `b` is at most `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`, for every post whose every continuation is bounded by the query budget (`qSend` sends, `qRaw` raw receives and `qFinish` attempted finishes). -/
theorem source_stop_bound (budget : Kind → Nat)
    (bounded : ∀ choice response, PqxdhPhase2SourceSchedulerBounds.Bounded (post choice response) budget) (b : Fin (B + 1)) :
    𝒟[PqxdhFirstRecordStopBound.sourceStopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)]
      {true} ≤ ((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [← potential_bound]
  exact (source_tagged setup env callbacks baseImpl kem attachedVerify primitives program post b).trans
    (tagged_game_bound setup env callbacks baseImpl kem attachedVerify primitives program post budget bounded (firstBeacon b))

/-- The restricted stop game of the first record of Beacon `b` is at most `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`, for every post whose every continuation is bounded by the query budget. -/
theorem stop_bound (budget : Kind → Nat)
    (bounded : ∀ choice response, PqxdhPhase2SourceSchedulerBounds.Bounded (post choice response) budget) (b : Fin (B + 1)) :
    𝒟[PqxdhFirstBeaconRecordIntegrity.stopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)]
      {true} ≤ ((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  (PqxdhFirstRecordStopBound.stopGame_le setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)).trans
    (source_stop_bound setup env callbacks baseImpl kem attachedVerify primitives program post budget bounded b)

end Prepared

section Instances
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity (firstBeacon forgeryPost certificate stopGame)
open PqxdhFirstBeaconRecordCanonical (canonicalPost canonicalCertificate)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The restricted stop game of the forgery proxy is at most `(1 + qSend + 51 (qRaw + qFinish)) / 2^256` with the certificate's post budget. -/
theorem forgery_stop_bound (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0) (b : Fin (B + 1)) :
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) (firstBeacon b)]
      {true} ≤ ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  stop_bound setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) c.postBudget
    (certificate env0 baseImpl kem program post0 c).postBound b

/-- The restricted stop game of the canonical proxy is at most `(1 + qSend + 51 (qRaw + qFinish)) / 2^256` with the certificate's post budget. -/
theorem canonical_stop_bound (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0) (b : Fin (B + 1)) :
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)]
      {true} ≤ ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  stop_bound setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) c.postBudget
    (canonicalCertificate env0 baseImpl kem program post0 c).postBound b

end Instances

section Integrity
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
open PqxdhFirstBeaconRecordCanonical (canonicalPost canonicalCertificate ReadWritable)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First Beacon record integrity for the canonical forgery event with the restricted stop term bounded: the HB-112 actual game with the canonical proxy, minus its constant-`false` continuation, is at most the target and completed-branch losses, the CTX loss, `2^-256` twice and `(1 + qSend + 51 (qRaw + qFinish)) / 2^256`, where `qSend`, `qRaw` and `qFinish` are the certificate's post budgets for sends, raw receives and attempted finishes. The premises are exactly those of `first_beacon_record_integrity_canonical`: the inherited correctness conditions, the hash budget `PrepareHashBudget`, the numeric query bound `small` and the message-model premise `ReadWritable`. -/
theorem first_beacon_record_integrity_stop
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program
      (canonicalPost env0 program post0) qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96)
    (writable : ReadWritable env.recordWriter env.decode) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (canonicalPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (canonicalPost env0 program post0)
        (canonicalCertificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0)
      hmac fallback ordinaryFallback +
    (ctxLoss setup env callbacks baseImpl kem attachedVerify primitives program (canonicalPost env0 program post0) (firstBeacon b)
      ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c))
      (1 + postTotal setup env callbacks baseImpl kem program c)).toReal +
    1 / 2 ^ 256 + 1 / 2 ^ 256 +
    ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 := by
  have base := PqxdhFirstBeaconRecordCanonical.first_beacon_record_integrity_canonical setup env callbacks baseImpl kem attachedVerify
    primitives program post0 b c compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude prepareHash small
    writable
  have stop := canonical_stop_bound setup env callbacks baseImpl kem attachedVerify primitives program post0 c b
  have real := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)) stop
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at real
  linarith

end Integrity
end BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_initSent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_initSent

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.settled_trans

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.frontend_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.frontend_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_phase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_settled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_initSent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.observed_initSent

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_simulation

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_state_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_state_simulation

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.lifted_unchallenged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.lifted_unchallenged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.lifted_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.lifted_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.product_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.product_coupling

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.run_absorbing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.run_absorbing

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbed_left' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbed_left

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbed_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbed_right

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.coupled_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.coupled_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.coupled_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.coupled_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.open_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.open_table

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.seal_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.seal_table

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_arguments

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.sealing_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.sealing_arguments

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_maps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_maps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.sealing_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.sealing_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.public_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.public_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.keep_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.keep_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_absorbing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_absorbing

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_public

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.receive_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_symbolic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_symbolic

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.compose_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.compose_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.native_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.native_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.backend_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.backend_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.native_family_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.native_family_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.program_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_keeps_log' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_keeps_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.keep_log_keeps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.keep_log_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_near' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_near

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.seals_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.seals_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.record_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.selected_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.selected_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.skipped_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.skipped_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reveal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reveal_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_note' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_note

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reveal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reveal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_restore

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.selector_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.selector_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.support_right

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.disclosed_absorbing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.disclosed_absorbing

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.exposed_absorbing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.exposed_absorbing

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.two_le_countP' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.two_le_countP

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.repeated_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.repeated_impossible

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.new_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.new_total

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.marked_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.marked_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_restores' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.local_restores

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_restores' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.simulate_restores

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_near' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_near

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.raw_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.raw_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.restores_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.prepare_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.prepare_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_labels

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_stage

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.grows_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.state_pure_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.state_pure_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.state_map_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.state_map_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.initial_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.chains_differ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.chains_differ

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.separate_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.separate_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.begin_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.begin_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.resume_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.resume_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.cached_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.cached_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.future_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.future_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_begin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.program_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.program_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.execute_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.execute_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_single

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_nil

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.owner_effect

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_effect

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_effect

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.family_effect

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.hidden_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.hidden_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.logged_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_count

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_family

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_receive_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_receive_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_send_logs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_send_logs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_public_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_public_keeps

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_record

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reaches_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.opening_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_result

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.known_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_effect

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.good_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.absorbs_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_upto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_upto

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_upto' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.pure_upto

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.publish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.publish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_absorbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_absorbs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reserve_absorbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reserve_absorbs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.candidate_absorbs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.candidate_absorbs

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.candidate_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.candidate_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.used_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.used_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_inverse

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_inverse

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_rep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_rep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.consume_rep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.consume_rep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_rep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_rep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reinstall_rep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.reinstall_rep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_coupled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_coupled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.publish_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.publish_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.predicate_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.predicate_growth

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.weighted_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.weighted_growth

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.inject_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.inject_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.label_growth

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.labels_growth

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.receive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.receive_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.public_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.public_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.step_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_labels' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.log_labels

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.send_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stage_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.finish_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.world_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.world_growth

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_drop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.weight_classify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.weight_classify

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.after_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.ready_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.new_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.new_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.hidden_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.hidden_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_known

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.beacon_root

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_servers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_servers

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_beacons' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.front_beacons

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_triple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.post_triple

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_good

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_event_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_event_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_aux_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.server_aux_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.build_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.optional_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.optional_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.run_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.run_log

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_le_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.bind_le_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.delayed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.delayed_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.existing_markable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.existing_markable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.start_front' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.start_front

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.input_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.input_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.decide_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.decide_mass

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_tagged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_game_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.tagged_game_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.potential_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.potential_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_stop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.source_stop_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.stop_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.forgery_stop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.forgery_stop_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.canonical_stop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.canonical_stop_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged.first_beacon_record_integrity_stop
