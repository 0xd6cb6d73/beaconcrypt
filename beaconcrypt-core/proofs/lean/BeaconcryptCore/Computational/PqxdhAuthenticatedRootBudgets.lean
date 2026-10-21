import BeaconcryptCore.Computational.PqxdhAuthenticatedRootPrepareBounds
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootComposition
import BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootErrorResources

/-!
A transparent resource certificate contains only the actual local callback, source caller and primitive generator budgets. The protocol preparation, adaptive target continuation, initial root and every later private finish are bounded from these source interfaces. The final authenticated-root statement consumes that derived root cap, with no whole-protocol root or continuation budget premise.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPrivateAcceptedRoot
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhChallengeSecretQueryBounds PqxdhAuthenticatedRootPrepareBounds
open PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid PqxdhSecretInputKdf
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Three resource coordinates at the ordinary CCA interface. -/
structure Triple where
  uniform : Nat
  base : Nat
  decapsulation : Nat

/-- Only source callers, actual local callbacks and primitive generators are certified; all compiled protocol caps are derived below. -/
structure Certificate {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1)) where
  qLocal : Nat
  localBound : ∀ query state, ((env.localImpl query).run state).IsTotalQueryBound qLocal
  qAux : Nat
  auxBound : ∀ query state, ((env.aux query).run state).IsTotalQueryBound qAux
  qWrite : Nat
  writerBound : ∀ fields state, ((env.phase1Writer fields).run state).IsTotalQueryBound qWrite
  preBudget : PqxdhPhase2SourceSchedulerBounds.Budget
  preBound : ∀ reply, PqxdhPhase2SourceSchedulerBounds.Bounded (program.main reply) preBudget
  postBudget : PqxdhPhase2SourceSchedulerBounds.Budget
  postBound : ∀ choice response, PqxdhPhase2SourceSchedulerBounds.Bounded (post choice response) postBudget
  noSign : ∀ reply, (program.main reply).IsQueryBoundP
    (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0
  noCreate : ∀ reply, (program.main reply).IsQueryBoundP
    (PqxdhPhase2SourceSchedulerBounds.ForwardedSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0
  prekey : Triple
  prekeyBound : ∀ identity, Caps (ccaAmbient (setup.prekey identity)) prekey.uniform prekey.base prekey.decapsulation
  oneTime : Triple
  oneTimeBound : ∀ identity before key, Caps (ccaAmbient (setup.oneTime identity before key))
    oneTime.uniform oneTime.base oneTime.decapsulation
  ephemeral : Triple
  ephemeralBound : Caps (ccaAmbient env.ephemeralGen) ephemeral.uniform ephemeral.base ephemeral.decapsulation
  nativeEncapsulation : Triple
  nativeBound : ∀ key, Caps (ccaAmbient (env.native.encaps key))
    nativeEncapsulation.uniform nativeEncapsulation.base nativeEncapsulation.decapsulation
  totalEncapsulation : Triple
  totalBound : ∀ key, Caps (ccaAmbient (kem.encaps key))
    totalEncapsulation.uniform totalEncapsulation.base totalEncapsulation.decapsulation
  qKeygen : Nat
  keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen
  qEncap : Nat
  encapsBound : ∀ key, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps key)).IsTotalQueryBound qEncap
  qBase : Nat
  baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase
  qDecap : Nat
  decapsBound : ∀ secret ciphertext,
    (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap

variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))

namespace Certificate
variable {env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B}
    {baseImpl : QueryImpl baseSpec ProbComp} {kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)}
    {program : Program baseSpec setup.Context S (B + 1)}
    {post : Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : Certificate env baseImpl kem program post)

def driverCost : Nat := c.qWrite + PqxdhPhase2SourceSchedulerBounds.bill c.qLocal c.preBudget

def commonCost : Nat := PqxdhAuthenticatedRootCommonBounds.commonBill c.qLocal c.qAux c.postBudget

def uPre : Nat := (32 + (c.prekey.uniform + (c.oneTime.uniform + 2 * c.driverCost))) +
  (c.ephemeral.uniform + (max c.nativeEncapsulation.uniform c.totalEncapsulation.uniform + 34 * c.commonCost))

def bPre : Nat := (c.prekey.base + (c.oneTime.base + c.driverCost)) +
  (c.ephemeral.base + (max c.nativeEncapsulation.base c.totalEncapsulation.base + c.commonCost))

def dPre : Nat := (c.prekey.decapsulation + (c.oneTime.decapsulation + c.driverCost)) +
  (c.ephemeral.decapsulation + (max c.nativeEncapsulation.decapsulation c.totalEncapsulation.decapsulation + c.commonCost))

def uPost : Nat := (64 + 5 * c.qAux) + PqxdhPhase2PostSchedulerBounds.bill c.qLocal .uniform c.postBudget

def bPost : Nat := c.postBudget (.inr 3)

def dPost : Nat := c.postBudget (.inr 4) + c.postBudget (.inr 5)

def privatePost : Nat := c.postBudget (.inr 5)

def qRoot : Nat := 1 + c.privatePost
def uReduction : Nat := c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) +
  (c.uPost + c.qBase * c.bPost + c.qDecap * (c.dPost + c.privatePost))
end Certificate

variable (c : Certificate env baseImpl kem program post)

/-- The executable preparation cap follows from the source prefix and all common and rejected continuations. -/
theorem prepare_bounds (key : TargetKemPublicKey) :
    Caps ((protocol env kem attachedVerify primitives program post).prepare key) c.uPre c.bPre c.dPre := by
  exact PqxdhAuthenticatedRootPrepareBounds.prepare_caps env program post attachedVerify primitives
    c.qLocal c.localBound c.postBudget c.postBound c.qAux c.auxBound kem c.qWrite c.writerBound
    c.preBudget c.preBound c.noSign c.noCreate
    c.prekey.uniform c.prekey.base c.prekey.decapsulation c.oneTime.uniform c.oneTime.base c.oneTime.decapsulation
    c.prekeyBound c.oneTimeBound
    c.ephemeral.uniform c.ephemeral.base c.ephemeral.decapsulation
    c.nativeEncapsulation.uniform c.nativeEncapsulation.base c.nativeEncapsulation.decapsulation
    c.totalEncapsulation.uniform c.totalEncapsulation.base c.totalEncapsulation.decapsulation
    c.ephemeralBound c.nativeBound c.totalBound key

/-- Real native builder coins remain public uniform requests and cannot issue a private-root or selected-key request. -/
theorem localCoins_bounds {Result : Type} (client : ProbComp Result) (q : Nat)
    (bounded : client.IsTotalQueryBound q) :
    PostBounds (localCoins (baseSpec := baseSpec) client) q 0 0 0 := by
  refine ⟨PqxdhCorrelatedRootQueryBounds.localCoins_uniform client q bounded, ?_, ?_, ?_⟩
  all_goals apply PqxdhCorrelatedRootQueryBounds.localCoins_excluded
  all_goals intro coin; simp [PublicClass, IsPrivateRoot, IsMlKemBaseQuery, IsMlKemLogicalDecapsulationQuery]

/-- The original registration builder precedes the full adaptive target schedule, adding its actual coins and no private root request. -/
theorem targetAccepted_bounds
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : Ready) :
    PostBounds (targetAccepted env attachedVerify primitives program post prepared ready)
      c.uPost c.bPost c.dPost c.privatePost := by
  have builder := localCoins_bounds (baseSpec := baseSpec) _ _
    (PqxdhProtocolQueryBounds.build_uniform env.source env.recordWriter env.aux c.qAux c.auxBound
      env.senderId env.index env.metadata ready prepared.1.context.selection.2)
  have tail := fun (result : RustM (Option PqxdhServerRegistrationPublication.Response) ×
    PqxdhGeneratedBeaconState.State setup M P I K A S (B + 1)) => PqxdhPhase2PostSchedulerBounds.fullPostBounds attachedVerify primitives 1
    env.source env.localImpl c.qLocal c.localBound env.recordWriter env.senderId env.route env.decode
    ready.ciphertext (post prepared.1.context.selection.1 result.1) c.postBudget (c.postBound _ _)
    (result.2, prepared.2)
  refine ⟨isQueryBoundP_bind builder.uniforms (fun result _ => ?_), ?_, ?_, ?_⟩
  · exact (isQueryBoundP_map_iff _ Prod.fst _).2 (tail result).uniforms
  · simpa only [Nat.zero_add, targetAccepted, Certificate.bPost] using isQueryBoundP_bind builder.bases (fun result _ =>
      (isQueryBoundP_map_iff _ Prod.fst _).2 (tail result).bases)
  · simpa only [Nat.zero_add, targetAccepted, Certificate.dPost] using isQueryBoundP_bind builder.decaps (fun result _ =>
      (isQueryBoundP_map_iff _ Prod.fst _).2 (tail result).decaps)
  · simpa only [Nat.zero_add, targetAccepted, Certificate.privatePost] using isQueryBoundP_bind builder.privateRoots (fun result _ =>
      (isQueryBoundP_map_iff _ Prod.fst _).2 (tail result).privateRoots)

/-- Completed, rejected and pending modes all satisfy the same derived continuation contract, for every optional initial root. -/
theorem resume_bounds (key : PqxdhKemIndCca.MlKem768PublicKey) (ciphertext : MlKem768Ciphertext)
    (state : (protocol env kem attachedVerify primitives program post).State) (initial : Option RootOutput) :
    PostBounds ((protocol env kem attachedVerify primitives program post).resume key ciphertext state initial)
      c.uPost c.bPost c.dPost c.privatePost := by
  cases state with
  | completed decision => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
  | pending prepared ephemeral =>
    cases initial with
    | none => exact ⟨by trivial, by trivial, by trivial, by trivial⟩
    | some value => exact targetAccepted_bounds env baseImpl kem attachedVerify primitives program post c prepared _

/-- Every whole-protocol field of the existing sampler contract is derived from the transparent source certificate. -/
theorem sampler_bounds :
    SamplerBounds baseImpl kem (protocol env kem attachedVerify primitives program post)
      c.qKeygen c.qEncap c.qBase c.qDecap c.uPre c.bPre c.dPre c.uPost c.bPost c.dPost c.privatePost := by
  exact ⟨c.keygenBound, c.encapsBound, c.baseBound, c.decapsBound,
    fun key => let bounded := prepare_bounds env baseImpl kem attachedVerify primitives program post c key
      ⟨bounded.uniforms, bounded.bases, bounded.decaps⟩,
    fun key ciphertext state initial => resume_bounds env baseImpl kem attachedVerify primitives program post c
      key ciphertext state initial⟩

/-- The consistent root-family reduction has a proved cap of one initial request plus every caller-bounded finish attempt. -/
theorem root_reduction_bounds :
    let client := rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)
    client.IsQueryBoundP PqxdhCorrelatedExpandQueryBounds.IsCoin c.uReduction ∧ client.IsQueryBoundP IsRoot c.qRoot := by
  exact PqxdhCorrelatedExpandQueryBounds.reduction_bounds env.source baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (sampler_bounds env baseImpl kem attachedVerify primitives program post c)

/-- The displayed ordinary one-key reduction pays both public decapsulation and the conservative private-attempt allowance. -/
theorem cca_reduction_bounds :
    (PqxdhChallengeSecretRouting.reduction env.source kem (protocol env kem attachedVerify primitives program post)).MakesAtMostQueries c.uPre c.bPre c.dPre c.uPost c.bPost (c.dPost + c.privatePost) := by
  let bounded := sampler_bounds env baseImpl kem attachedVerify primitives program post c
  exact PqxdhChallengeSecretQueryBounds.reduction_bounds env.source kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ bounded.prepare bounded.resume

/-- Both fixed CCA worlds retain their unused shared-secret sample; the fair challenger also pays its hidden-bit draw. The typed source wrapper is separately named and charged. -/
theorem cca_uniform_ledger :
    let p := protocol env kem attachedVerify primitives program post
    (∀ bit, (simulateQ (kemAmbientImpl baseImpl)
      (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p) bit)).IsTotalQueryBound (c.uReduction + 32)) ∧
    (simulateQ (kemAmbientImpl baseImpl)
      (PqxdhChallengeSecretRouting.nativeMain env.source kem (runtimeOfImpl (kemAmbientImpl baseImpl)) p)).IsTotalQueryBound (c.uReduction + 32) ∧
    (PqxdhPrivateRootGameBudgets.oneKeyFairProgram baseImpl kem
      (PqxdhChallengeSecretRouting.reduction env.source kem p)).IsTotalQueryBound (c.uReduction + 33) ∧
    (simulateQ (kemAmbientImpl baseImpl) (PqxdhChallengeSecretRouting.sourceMain env.source kem p)).IsTotalQueryBound c.uReduction := by
  let bounded := sampler_bounds env baseImpl kem attachedVerify primitives program post c
  refine ⟨fun bit => ?_, ?_, ?_, ?_⟩
  · simpa only [Certificate.uReduction, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      PqxdhChallengeSecretQueryBounds.fixed_world_uniform_bound env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
        bounded.keygen bounded.encaps bounded.base bounded.decaps bounded.prepare bounded.resume bit
  · simpa only [Certificate.uReduction, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      PqxdhChallengeSecretQueryBounds.native_uniform_bound env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded
  · apply (PqxdhChallengeSecretQueryBounds.fair_uniform_bound env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded).mono
    dsimp only [Certificate.uReduction]
    omega
  · simpa only [Certificate.uReduction, Nat.add_assoc] using
      PqxdhChallengeSecretQueryBounds.source_uniform_bound env.source baseImpl kem
        (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _ bounded

/-- The exact Extract-family reduction has the same interpreted source coin bill and initial-plus-finish family cap. -/
theorem extract_reduction_bounds (hmac : HmacSha512) :
    let client := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
      (protocol env kem attachedVerify primitives program post)
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsCoin c.uReduction ∧
    client.IsQueryBoundP PqxdhCorrelatedExtractQueryBounds.IsFamily c.qRoot := by
  exact PqxdhCorrelatedExtractQueryBounds.reduction_bounds env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (sampler_bounds env baseImpl kem attachedVerify primitives program post c)

/-- Real Extract pays its one hidden 32-byte input sample; random Extract pays at most 64 draws per distinct family request and reuses cached answers. -/
theorem extract_uniform_ledger (hmac : HmacSha512) :
    let client := PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem
      (protocol env kem attachedVerify primitives program post)
    (PqxdhCorrelatedExtractFamily.realGame hmac client).IsTotalQueryBound (32 + c.uReduction) ∧
    (PqxdhCorrelatedExtractFamily.randomGame client).IsTotalQueryBound (c.uReduction + 64 * c.qRoot) := by
  exact PqxdhCorrelatedExtractQueryBounds.reduction_uniform_ledger env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (sampler_bounds env baseImpl kem attachedVerify primitives program post c)

/-- Consistent expanded and uniform root families retain their own exact output sampling, and both indexed HMAC challengers retain their separate 64-draw allowance. -/
theorem root_and_hmac_uniform_ledger (hmac : HmacSha512) :
    let client := rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)
    client.IsQueryBoundP IsRoot c.qRoot ∧
    (expandedGame hmac client).IsTotalQueryBound (c.uReduction + 64 * c.qRoot) ∧
    (uniformGame client).IsTotalQueryBound (c.uReduction + 32 * c.qRoot) ∧
    ∀ index,
      (hmacPrfRealGame hmac (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + c.uReduction + 64 * c.qRoot) ∧
      (hmacPrfRandomGame (indexedReduction hmac client index)).IsTotalQueryBound
        (64 + c.uReduction + 64 * c.qRoot) := by
  exact PqxdhCorrelatedExpandQueryBounds.source_uniform_ledger env.source hmac baseImpl kem
    (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
    (sampler_bounds env baseImpl kem attachedVerify primitives program post c)

/-- Each constructed ordinary HMAC reduction makes at most one challenge query and pays for every simulated other family input. -/
theorem indexed_hmac_bounds (hmac : HmacSha512) (index : Nat) :
    let client := rootReduction env.source baseImpl kem (protocol env kem attachedVerify primitives program post)
    (indexedReduction hmac client index).IsQueryBoundP PqxdhSecretInputInitializer.IsHmacUniformQuery (c.uReduction + 64 * c.qRoot) ∧
    (indexedReduction hmac client index).IsQueryBoundP IsHmacChallengeQuery 1 := by
  have bounded := root_reduction_bounds env baseImpl kem attachedVerify primitives program post c
  exact PqxdhCorrelatedExpandQueryBounds.indexed_bounds hmac _ index _ _ bounded.1 bounded.2

/-- The displayed ordinary correctness-error probability uses one actual key generation, encapsulation and decapsulation, each with its certified evaluated cost. -/
theorem error_uniform_bound :
    (simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)).IsTotalQueryBound
      (c.qKeygen + c.qEncap + c.qDecap) := by
  exact PqxdhAuthenticatedRootErrorResources.error_uniform baseImpl kem _ _ _
    c.keygenBound c.encapsBound c.decapsBound

/-- The source-shaped authenticated-root bound and reached native Server representation use only the derived one-plus-finish cap; no whole-protocol root bound is assumed. -/
theorem authenticated_native_root_bound
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem env.native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : FunctionalDecapsulation kem)
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect env.source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (secretIdentity : M → Pqxdh.Bytes)
    (initialMatch : PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity
      env.senderId env.index env.server env.initial) :
    let p := protocol env kem attachedVerify primitives program post
    ((actual env baseImpl kem attachedVerify primitives program post).boolDistAdvantage
      (uniformGame (rootReduction env.source baseImpl kem p)) ≤
      (PqxdhJointIdentity.advantage primitives
        (PqxdhGeneratedPhase1Prefix.privateReduction primitives baseImpl kem setup
          (driver env.toDriverEnvironment program) fallback ordinaryFallback)).toReal +
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (PqxdhKemCorrectnessError.errorExperiment kem)}[x = true].toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction env.source kem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction env.source hmac baseImpl kem p) +
      ∑ index ∈ Finset.range c.qRoot,
        (hmacPrfRealGame hmac (indexedReduction hmac (rootReduction env.source baseImpl kem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac (rootReduction env.source baseImpl kem p) index))) ∧
    ∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun attachedVerify primitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl kem setup (driver env.toDriverEnvironment program))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields env.source.crypto secretIdentity env.senderId env.index
          env.server output.context.selection.2 := by
  exact PqxdhAuthenticatedRootComposition.authenticated_native_root_bound env baseImpl kem attachedVerify primitives program post
    compatible adapter functional hmac sourceCorrect c.noSign c.noCreate fallback ordinaryFallback c.qRoot
    (root_reduction_bounds env baseImpl kem attachedVerify primitives program post c).2 secretIdentity initialMatch

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.prepare_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.prepare_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.localCoins_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.localCoins_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.targetAccepted_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.targetAccepted_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.resume_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.resume_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.sampler_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.sampler_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.root_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.root_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.cca_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.cca_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.cca_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.cca_uniform_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.extract_reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.extract_reduction_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.extract_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.extract_uniform_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.root_and_hmac_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.root_and_hmac_uniform_ledger

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.indexed_hmac_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.indexed_hmac_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.error_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.error_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound
