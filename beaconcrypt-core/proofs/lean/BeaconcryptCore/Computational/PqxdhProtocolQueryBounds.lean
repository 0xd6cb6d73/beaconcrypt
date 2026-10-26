import BeaconcryptCore.Computational.PqxdhProtocolExperiment
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
Twenty statements account for the complete native scheduler compiler, accepted and rejected continuations, original three-signature source prefix, every logical decapsulation attempt and actual source evaluation. The compiled selector costs Q+U+64(S+R+H) query calls; Q counts all forwarded selector calls and the remaining term counts native uniform calls. Interpreting selector/base services is charged separately in actual_uniform_ledger. The native builder costs at most 64+5*qAux uniform requests, with one-call caps on all nine callback classes and an explicit bound on each of five auxiliary handlers. Both continuation branches include the whole subsequent source schedule. Uniform calls are not entropy bits or general byte/runtime costs; fixed local HKDF, AEAD, writing, copying and allocation remain actual computation. These resource bounds assert no evolving-key independence, global freshness or security for arbitrary native metadata.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhProtocolQueryBounds
open PqxdhProtocolSelector

variable {ι : Type} {baseSpec : OracleSpec ι}
variable {M P I D K A : Type} {S B : Nat}

/-- All coins of the compiled native program are counted as actual selector requests. -/
theorem coins_total {Result : Type} (work : ProbComp Result) (budget : Nat)
    (bounded : work.IsTotalQueryBound budget) :
    (coins (baseSpec := baseSpec) work).IsTotalQueryBound budget := by
  induction work using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      change OracleComp.IsTotalQueryBound (do
        let answer ← ((PqxdhPrivateKemSource.SelectorSpec baseSpec).query (.inr (.inl (.inl query))) :
          OracleComp (PqxdhPrivateKemSource.SelectorSpec baseSpec) _)
        coins (next answer)) budget
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer (budget - 1) (bounded.2 answer)⟩

abbrev Budget := RawCtxRevealBudgets.Budget × Nat

def permitted : (Spec baseSpec S B).Domain → Budget → Prop
  | .inl request, budget => RawCtxRevealBudgets.permitted request budget.1
  | .inr _, budget => 0 < budget.2

def remaining : (Spec baseSpec S B).Domain → Budget → Budget
  | .inl request, budget => (RawCtxRevealBudgets.remaining request budget.1, budget.2)
  | .inr _, budget => (budget.1, budget.2 - 1)

def Bounded {Result : Type} (program : OracleComp (Spec baseSpec S B) Result) (budget : Budget) : Prop :=
  IsQueryBound program budget (permitted (baseSpec := baseSpec)) (remaining (baseSpec := baseSpec))

def compilerCost : (Spec baseSpec S B).Domain → Nat
  | .inl request => RawCtxRevealBudgets.weight (RawCtxServerServiceBounds.uniformWeight 0) 0 request
  | .inr _ => 1

def compilerBill (budget : Budget) : Nat :=
  RawCtxRevealBudgets.bill (RawCtxServerServiceBounds.uniformWeight 0) 0 budget.1 + budget.2

/-- The interleaved caller spends each native or selector coordinate, including rejection and repeated reveals. -/
theorem compiler_bill_step (query : (Spec baseSpec S B).Domain) (budget : Budget)
    (positive : permitted query budget) :
    compilerCost query + compilerBill (remaining query budget) = compilerBill budget := by
  cases query with
  | inl request =>
      simpa only [compilerCost, compilerBill, remaining, Nat.add_assoc] using
        congrArg (fun value => value + budget.2)
          (RawCtxRevealBudgets.bill_step (RawCtxServerServiceBounds.uniformWeight 0) 0 request budget.1 positive)
  | inr request =>
      have spent : budget.2 - 1 + 1 = budget.2 := Nat.sub_add_cancel positive
      simp only [compilerCost, compilerBill, remaining]
      omega

/-- Actual source handler costs survive the extra registration controls and consumed history. -/
theorem source_uniform_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode query).run state).IsTotalQueryBound
      (RawCtxRevealBudgets.weight (RawCtxServerServiceBounds.uniformWeight 0) 0 query) := by
  simpa only [PqxdhRegistrationProtocolState.sourceImpl, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxRevealBudgets.source_uniform_step source writer S B senderId route decode query
        (PqxdhRegistrationProtocolState.project state)

/-- Compiling native work does not hide its uniform requests in an opaque ambient operation. -/
theorem compiler_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (Spec baseSpec S B).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((compiler source writer senderId route decode query).run state).IsTotalQueryBound (compilerCost query) := by
  cases query with
  | inl request =>
      exact coins_total _ _ (source_uniform_step source writer senderId route decode request state)
  | inr request =>
      simp [compiler, StateT.run, bind_pure_comp, IsTotalQueryBound, compilerCost]

/-- The complete adaptive selector counts native coins and every forwarded selector request. -/
theorem compiler_total {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (Spec baseSpec S B) Result) (budget : Budget) (bounded : Bounded client budget)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((simulateQ (compiler source writer senderId route decode) client).run state).IsTotalQueryBound
      (compilerBill budget) := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := compilerBill)
    (stepBudget := fun query _ => compilerCost query)
    (fun first rest => isTotalQueryBound_bind first rest)
    (fun query _ state _ => compiler_step source writer senderId route decode query state)
    (fun query budget positive => compiler_bill_step query budget positive) state

/-- The compiled request bill includes all Q selector calls and U+64(S+R+H) native coins. -/
theorem compiler_bill (budget : Budget) : compilerBill budget =
    budget.2 + budget.1.1 .coin + 64 * (budget.1.1 .send + budget.1.1 .raw + budget.1.1 .hash) := by
  simp only [compilerBill, RawCtxRevealBudgets.bill, RawCtxServerServiceBounds.uniform_bill,
    Nat.zero_mul, Nat.add_zero]
  omega

/-- Selection retains that exact bill, without exposing the compiler's private state. -/
theorem selected_total {Context : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (program : Program baseSpec Context S B)
    (initial : PqxdhRegistrationProtocolState.State M P I D K A S B)
    (transcript : PqxdhEd25519EufCma.Phase1PublicTranscript Context) (budget : Budget)
    (bounded : Bounded (program.main transcript) budget) :
    ((selected source writer senderId route decode program initial).main transcript).IsTotalQueryBound
      (budget.2 + budget.1.1 .coin + 64 * (budget.1.1 .send + budget.1.1 .raw + budget.1.1 .hash)) := by
  simpa only [selected, IsTotalQueryBound, isQueryBound_map_iff, compiler_bill] using
    compiler_total source writer senderId route decode (program.main transcript) budget bounded initial

open PqxdhAcceptedRegistration PqxdhServerRegistrationPublication

/-- Uniform cost of the real callback classes; each auxiliary callback has an explicit supplied cap. -/
def nativeUniformCost (qAux : Nat) : NativeKind → Nat
  | .hash => 64
  | .kdf | .aead | .frameWriter => 0
  | .identity | .peerReserve | .plaintextReserve | .erase | .phase2Writer => qAux

/-- The actual native send callbacks use no new coins except up to 64 for their shared commitment miss. -/
theorem native_uniform_step
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qAux : Nat) (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (query : NativeSpec.Domain) (primitive : RawCtxSharedPrimitive.SharedState A) :
    ((PqxdhRegistrationProtocolState.registrationImpl source writer aux query).run primitive).IsTotalQueryBound
      (nativeUniformCost qAux (nativeKind query)) := by
  cases query with
  | inr request =>
      cases request <;> exact auxBound _ primitive
  | inl request =>
      have bound := RawCtxMixedShared.shared_uniform source.crypto writer (RawCtxSourceHkdf.kdfImpl source) 0
        (RawCtxSourceHkdf.kdf_uniform source) (RawCtxMixedOwner.sendLift request) 1
        (if nativeKind (.inl request) = .hash then 1 else 0)
        (by
          rcases request with request | (request | (request | request))
          all_goals apply (isQueryBoundP_query_iff (spec := RawCtxMixedOwner.NativeSpec)
            (p := fun query => RawCtxMixedOwner.callKind query = .kdf) _ _).2
          all_goals simp [RawCtxMixedOwner.callKind])
        (by
          rcases request with request | (request | (request | request))
          all_goals apply (isQueryBoundP_query_iff (spec := RawCtxMixedOwner.NativeSpec)
            (p := fun query => RawCtxMixedOwner.callKind query = .hash) _ _).2
          all_goals simp [RawCtxMixedOwner.callKind, nativeKind]) primitive
      change ((simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source))
        (RawCtxMixedOwner.sendLift request)).run primitive).IsTotalQueryBound _
      convert bound using 1
      rcases request with request | (request | (request | request))
      all_goals simp [nativeUniformCost, nativeKind]

/-- The nine-class callback ledger sums to one commitment miss and five explicitly costed auxiliary calls. -/
theorem native_uniform_bill (qAux : Nat) : (∑ kind, nativeUniformCost qAux kind) = 64 + 5 * qAux := by
  have enumeration : (Finset.univ : Finset NativeKind) =
      {.kdf, .aead, .hash, .frameWriter, .identity, .peerReserve, .plaintextReserve, .erase, .phase2Writer} := by decide
  simp [enumeration, nativeUniformCost]
  omega

/-- The reached registration builder pays all actual native uniform costs before any continuation. -/
theorem build_uniform
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (qAux : Nat) (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (senderId : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((PqxdhRegistrationProtocolState.build source writer aux senderId index metadata ready).run state).IsTotalQueryBound
      (64 + 5 * qAux) := by
  simp only [PqxdhRegistrationProtocolState.build, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  have bound := buildReady_weighted (PqxdhRegistrationProtocolState.registrationImpl source writer aux)
    (fun _ => True) (nativeUniformCost qAux)
    (fun query primitive => (native_uniform_step source writer aux qAux auxBound query primitive).isQueryBoundP)
    source (PqxdhRegistrationProtocolState.input senderId index metadata
      (PqxdhRegistrationProtocolState.consume index ready state)).binding ready metadata
    (PqxdhRegistrationProtocolState.input senderId index metadata
      (PqxdhRegistrationProtocolState.consume index ready state)).state state.primitive
  simpa only [native_uniform_bill, IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true,
    StateT.run, PqxdhRegistrationProtocolState.consume] using bound

/-- The same reached source scheduler keeps the full uniform ledger when registration controls are retained. -/
theorem schedule_uniform {Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (budget : RawCtxRevealBudgets.Budget)
    (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    ((simulateQ (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode) client).run state).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  rw [PqxdhRegistrationProtocolState.source_schedule]
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    RawCtxRevealBudgets.schedule_uniform source writer S B senderId route decode client budget bounded
      (PqxdhRegistrationProtocolState.project state)

/-- The native continuation lift preserves every internal coin call. -/
theorem continuation_coins_total {Result : Type} (work : ProbComp Result) (budget : Nat)
    (bounded : work.IsTotalQueryBound budget) :
    (PqxdhProtocolRegistration.coins (baseSpec := baseSpec) work).IsTotalQueryBound budget := by
  induction work using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      change OracleComp.IsTotalQueryBound (do
        let answer ← ((PqxdhPrivateAcceptedRoot.CorrelatedSpec baseSpec).query
          (.inl (.inr (.inl (.inl (.inl query))))) :
            OracleComp (PqxdhPrivateAcceptedRoot.CorrelatedSpec baseSpec) _)
        PqxdhProtocolRegistration.coins (next answer)) budget
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer (budget - 1) (bounded.2 answer)⟩

/-- A selective class excludes private coins only under its explicit routing predicate. -/
theorem continuation_coins_excluded {Result : Type}
    (predicate : (PqxdhPrivateAcceptedRoot.CorrelatedSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inr (.inl (.inl (.inl coin))))))
    (work : ProbComp Result) :
    (PqxdhProtocolRegistration.coins (baseSpec := baseSpec) work).IsQueryBoundP predicate 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      change OracleComp.IsQueryBoundP (do
        let answer ← ((PqxdhPrivateAcceptedRoot.CorrelatedSpec baseSpec).query
          (.inl (.inr (.inl (.inl (.inl query))))) :
            OracleComp (PqxdhPrivateAcceptedRoot.CorrelatedSpec baseSpec) _)
        PqxdhProtocolRegistration.coins (next answer)) predicate 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨by simp [excluded query], fun answer => by simpa only [ite_eq_right (excluded query)] using ih answer⟩

open PqxdhCorrelatedRootQueryBounds PqxdhPrivateRootQueryBounds PqxdhChallengeSecretQueryBounds

/-- Coin-only native execution retains its uniform cap and provably issues no identity/base/decapsulation/private-root requests. -/
theorem coins_observer_bounds {Result : Type} (work : ProbComp Result) (budget : Nat)
    (bounded : work.IsTotalQueryBound budget) :
    ObserverBounds (PqxdhProtocolRegistration.coins (baseSpec := baseSpec) work) 0 0 budget 0 0 0 := by
  constructor
  · exact continuation_coins_excluded _ (by intro coin; simp [SourceClass]) work
  · exact continuation_coins_excluded _ (by intro coin; simp [SourceClass]) work
  · exact (continuation_coins_total work budget bounded).isQueryBoundP
  · exact continuation_coins_excluded _ (by intro coin; simp [LocalClass, PublicClass, PqxdhKemIndCca.IsMlKemBaseQuery]) work
  · exact continuation_coins_excluded _ (by intro coin; simp [LocalClass, PublicClass, PqxdhKemIndCca.IsMlKemLogicalDecapsulationQuery]) work
  · exact continuation_coins_excluded _ (by intro coin; simp [LocalClass, IsPrivateRoot]) work

open PqxdhProtocolExperiment

/-- Every possible native builder result continues with its reached state and the same explicit post-schedule budget. -/
theorem accepted_observer_bounds (env : Environment baseSpec M P I D K A S B)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B) (post : Post program.Selection S B)
    (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat) (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (output : PqxdhProtocolRegistration.Output (M := M) (P := P) (I := I) (D := D) (K := K)
      (A := A) (S := S) (B := B) setup program.Selection)
    (ready : PqxdhPrivateAcceptedRoot.Ready) :
    ObserverBounds ((env.observer setup program post).accepted output ready) 0 0
      ((64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) 0 0 0 := by
  rw [Environment.observer, Environment.plan, PqxdhProtocolRegistration.accepted_run]
  apply coins_observer_bounds
  apply isTotalQueryBound_bind (build_uniform env.parameters.source env.writer env.aux qAux auxBound
    env.senderId env.index env.metadata ready (PqxdhProtocolRegistration.reached env.initial output))
  intro result
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
    schedule_uniform env.parameters.source env.writer env.senderId env.route env.decode
      (post (PqxdhProtocolRegistration.choice output) result.1) budget (postBound _ _) result.2

/-- Early registration rejection resumes the same scheduler; the common continuation cap also covers its shorter path. -/
theorem completed_observer_bounds (env : Environment baseSpec M P I D K A S B)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B) (post : Post program.Selection S B)
    (budget : RawCtxRevealBudgets.Budget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) budget)
    (qAux : Nat)
    (output : PqxdhProtocolRegistration.Output (M := M) (P := P) (I := I) (D := D) (K := K)
      (A := A) (S := S) (B := B) setup program.Selection)
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) :
    ObserverBounds ((env.observer setup program post).completed output execution) 0 0
      ((64 + 5 * qAux) + (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))) 0 0 0 := by
  apply coins_observer_bounds
  apply IsTotalQueryBound.mono (n₁ := budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash))
  · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      schedule_uniform env.parameters.source env.writer env.senderId env.route env.decode
        (post (PqxdhProtocolRegistration.choice output) (.ok none)) budget (postBound _ _)
        (PqxdhProtocolRegistration.reached env.initial output)
  · omega

open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateSourceCoins PqxdhPrivateKemSource
open PqxdhKemIndCca PqxdhPrivateKemQueryBounds
open PqxdhJointPhase1AcceptanceComposition PqxdhInitializerSecrecy PqxdhDynamicIdentityRouting

/-- The complete original source prefix makes at most three signing calls. -/
theorem prefix_sign_bound {KemSK : Type} (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B)
    (noSign : ∀ transcript, (program.main transcript).IsQueryBoundP (SelectorClass (SelectorSource (baseSpec := baseSpec) IsSigning)) 0) :
    (PqxdhPrivatePhase1Prefix.program baseImpl kem setup (env.selector program)).IsQueryBoundP
      (fun query => IsSigning (translated query)) 3 := by
  exact PqxdhPrivatePhase1Prefix.program_sign_bound baseImpl kem setup (env.selector program)
    (fun transcript => selected_source_bound env.parameters.source env.writer env.senderId env.route env.decode
      program env.initial IsSigning transcript 0 (noSign transcript))

/-- Forwarded selective services retain their original cap whenever that class explicitly excludes private native coins. -/
theorem selected_class_bound {Context : Type} (env : Environment baseSpec M P I D K A S B)
    (program : Program baseSpec Context S B) (transcript : Phase1PublicTranscript Context)
    (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inr (.inl (.inl coin))))
    (q : Nat) (bounded : (program.main transcript).IsQueryBoundP (SelectorClass predicate) q) :
    ((env.selector program).main transcript).IsQueryBoundP predicate q := by
  simpa only [Environment.selector, selected, isQueryBoundP_map_iff] using
    compiler_bound env.parameters.source env.writer env.senderId env.route env.decode predicate excluded
      (program.main transcript) q bounded env.initial

/-- Every logical decapsulation attempt, before or after a record operation in the selector, spends the original qD budget. -/
theorem selected_decap_bound {Context : Type} (env : Environment baseSpec M P I D K A S B)
    (program : Program baseSpec Context S B) (transcript : Phase1PublicTranscript Context)
    (qD : Nat) (bounded : (program.main transcript).IsQueryBoundP
      (SelectorClass (PqxdhPrivateRootQueryBounds.SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)) qD) :
    ((env.selector program).main transcript).IsQueryBoundP
      (PqxdhPrivateRootQueryBounds.SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qD := by
  exact selected_class_bound env program transcript _
    (by intro coin; simp [PqxdhPrivateRootQueryBounds.SelectorCCA, IsMlKemLogicalDecapsulationQuery]) qD bounded

/-- Full source evaluation charges generated keys, every retained selector service, native response work and all continued record/public/reveal coins. -/
theorem actual_uniform_ledger {KemSK : Type} (env : Environment baseSpec M P I D K A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (program : Program baseSpec setup.Context S B) (post : Post program.Selection S B)
    (prefixBudget : Budget) (postBudget : RawCtxRevealBudgets.Budget)
    (prefixBound : ∀ transcript, Bounded (program.main transcript) prefixBudget)
    (postBound : ∀ choice response, RawCtxRevealBudgets.Bounded (post choice response) postBudget)
    (qPrekey qKeygen qOneTime qBase qDecap qSource qB qD qAux uEphemeral uNative bEphemeral bNative : Nat)
    (prekeyBound : ∀ identity, (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (noCreate : ∀ transcript, (program.main transcript).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) PqxdhPrivatePhase1Prefix.Creating)) 0)
    (sourceCoins : ∀ transcript, (program.main transcript).IsQueryBoundP
      (SelectorClass (SelectorSource (baseSpec := baseSpec) SourceUniform)) qSource)
    (bases : ∀ transcript, (program.main transcript).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery)) qB)
    (decaps : ∀ transcript, (program.main transcript).IsQueryBoundP
      (SelectorClass (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)) qD)
    (auxBound : ∀ query primitive, ((env.aux query).run primitive).IsTotalQueryBound qAux)
    (ephemeralUniform : (ccaAmbient env.parameters.ephemeralGen).IsQueryBoundP IsMlKemUniformQuery uEphemeral)
    (nativeUniform : ∀ target, (ccaAmbient (env.parameters.native.encaps target)).IsQueryBoundP IsMlKemUniformQuery uNative)
    (ephemeralBase : (ccaAmbient env.parameters.ephemeralGen).IsQueryBoundP IsMlKemBaseQuery bEphemeral)
    (nativeBase : ∀ target, (ccaAmbient (env.parameters.native.encaps target)).IsQueryBoundP IsMlKemBaseQuery bNative) :
    (env.actual baseImpl kem attachedVerify primitives setup program post).IsTotalQueryBound
      ((32 + ((qPrekey + (qKeygen + qOneTime)) +
        (qSource + compilerBill prefixBudget + qBase * qB + qDecap * qD))) +
        ((uEphemeral + (uNative + ((64 + 5 * qAux) +
          (postBudget.1 .coin + 64 * (postBudget.1 .send + postBudget.1 .raw + postBudget.1 .hash))))) +
          qBase * (bEphemeral + bNative))) := by
  have afterBound := PqxdhPrivateAcceptedRootBounds.nativeNext_observer_bounds kem env.parameters attachedVerify primitives setup
    (env.observer setup program post) uEphemeral uNative bEphemeral bNative 0 0
    ((64 + 5 * qAux) + (postBudget.1 .coin + 64 * (postBudget.1 .send + postBudget.1 .raw + postBudget.1 .hash))) 0 0 0
    ephemeralUniform nativeUniform ephemeralBase nativeBase
    (completed_observer_bounds env setup program post postBudget postBound qAux)
    (accepted_observer_bounds env setup program post postBudget postBound qAux auxBound)
  have beforeCoins : ∀ transcript, ((env.selector program).main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) (compilerBill prefixBudget) := by
    intro transcript
    have total := selected_total env.parameters.source env.writer env.senderId env.route env.decode
      program env.initial transcript prefixBudget (prefixBound transcript)
    rw [← compiler_bill] at total
    exact total.isQueryBoundP
  simpa only [Environment.actual, Nat.mul_zero, Nat.zero_add, Nat.add_zero] using
    PqxdhPrivateAcceptedRootBounds.actualGame_uniform_from_calls baseImpl kem env.parameters attachedVerify primitives setup
      (env.selector program) (env.observer setup program post) qPrekey qKeygen qOneTime qBase qDecap 0 qSource
      (compilerBill prefixBudget) qB qD _ _ 0 prekeyBound keygenBound oneTimeBound baseBound decapBound
      (fun transcript => selected_source_bound env.parameters.source env.writer env.senderId env.route env.decode
        program env.initial _ transcript 0 (noCreate transcript))
      (fun transcript => selected_source_bound env.parameters.source env.writer env.senderId env.route env.decode
        program env.initial _ transcript qSource (sourceCoins transcript))
      beforeCoins
      (fun transcript => selected_class_bound env program transcript _
        (by intro coin; simp [SelectorCCA, IsMlKemBaseQuery]) qB (bases transcript))
      (fun transcript => selected_decap_bound env program transcript qD (decaps transcript))
      (fun prepared => (afterBound prepared).1) (fun prepared => (afterBound prepared).2.1)
      (fun prepared => (afterBound prepared).2.2)

end BeaconcryptCore.Computational.PqxdhProtocolQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.coins_total' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.coins_total

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_bill_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_bill_step

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.source_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.source_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_step

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_total

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.compiler_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_total

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.native_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.native_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.native_uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.native_uniform_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.build_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.schedule_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.continuation_coins_total' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.continuation_coins_total

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.continuation_coins_excluded' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.continuation_coins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.coins_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.coins_observer_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.accepted_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.accepted_observer_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.completed_observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.completed_observer_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.prefix_sign_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.prefix_sign_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_decap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.selected_decap_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.actual_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhProtocolQueryBounds.actual_uniform_ledger
