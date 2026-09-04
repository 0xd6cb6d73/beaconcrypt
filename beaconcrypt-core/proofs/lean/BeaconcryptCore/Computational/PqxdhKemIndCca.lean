import BeaconcryptCore.Model.Pqxdh.Primitives
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# One-key ML-KEM-768 IND-CCA bridge for BeaconCrypt PQXDH

This module gives the honest ML-KEM leg used by one PQXDH establishment an exact computational endpoint. Public keys, ciphertexts, and shared secrets have the production widths 1184, 1088, and 32 bytes. The decapsulation-key type and the KEM operations remain opaque.

The source-facing adversary sees an explicit public transcript containing the selected public key, challenge ciphertext, and an arbitrary caller context. It never receives the shared secret as a transcript field: the real or uniform candidate is passed directly to its private post-challenge continuation. The real and random branches both run one key generation, one honest encapsulation, and one ghost uniform-secret draw. This makes the branch distance exactly the standard VCVio `KEMScheme.IND_CCA_Advantage`, with coefficient one.

Query accounting separates the pre/post clients' public uniform queries, arbitrary base-oracle queries, and logical decapsulation queries. These caps do not count ambient-oracle work internal to opaque key generation, encapsulation, or decapsulation. A post-challenge query at the exact challenge ciphertext is blocked and invokes no primitive decapsulation; every unequal ciphertext is forwarded once. The hidden challenge bit and ghost random shared secret are runtime draws rather than adversary queries.

No ML-KEM algorithm, implementation, public-key injectivity, cross-key binding, or cross-key shared-secret uniqueness property is proved here. Honest recipient agreement remains the separately named generic KEM correctness assumption.
-/

open OracleSpec OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhKemIndCca

/-- The exact 1184-byte production ML-KEM-768 public-key shape. -/
abbrev MlKem768PublicKey := List.Vector UInt8 1184

/-- The exact 1088-byte production ML-KEM-768 ciphertext shape. -/
abbrev MlKem768Ciphertext := List.Vector UInt8 1088

/-- The exact 32-byte production ML-KEM shared-secret shape. -/
abbrev MlKemSharedSecret := List.Vector UInt8 32

/-- Public challenge data passed to the source-shaped post-challenge continuation; the candidate shared secret is deliberately absent. -/
structure MlKemChallengeTranscript (Context : Type) where
  publicKey : MlKem768PublicKey
  ciphertext : MlKem768Ciphertext
  context : Context

variable {ι : Type} {baseSpec : OracleSpec ι} {SK : Type}

/-- An opaque KEM at the exact ML-KEM-768 public-output widths, over public-uniform and arbitrary base effects. -/
abbrev MlKemScheme := KEMScheme (OracleComp (unifSpec + baseSpec))
  MlKemSharedSecret MlKem768PublicKey SK MlKem768Ciphertext

/-- A one-key, two-phase source adversary whose post phase receives the candidate secret privately rather than through its public transcript. -/
structure OneKeyAdversary (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)) where
  Context : Type
  preChallenge : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec Context
  postChallenge : MlKemChallengeTranscript Context → MlKemSharedSecret →
    OracleComp kem.IND_CCA_oracleSpec Bool

/-- Package the source-shaped phases as VCVio's generic one-key IND-CCA adversary. -/
def OneKeyAdversary.toINDCCA
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem) : kem.IND_CCA_Adversary where
  State := MlKem768PublicKey × adversary.Context
  preChallenge pk := do
    let context ← adversary.preChallenge pk
    return (pk, context)
  postChallenge state cStar kStar :=
    adversary.postChallenge ⟨state.1, cStar, state.2⟩ kStar

/-- Shared key-generation and unrestricted pre-challenge prefix of both fixed branches. -/
def oneKeyPrefix
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (adversary : OneKeyAdversary kem) :
    OracleComp (unifSpec + baseSpec)
      (MlKem768PublicKey × SK × adversary.Context) := do
  let (pk, sk) ← kem.keygen
  let context ← simulateQ (kem.IND_CCA_preChallengeImpl sk)
    (adversary.preChallenge pk)
  return (pk, sk, context)

/-- Honest encapsulation, branch-independent ghost sample, and challenge-blocked post phase. -/
def oneKeyFinish
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (adversary : OneKeyAdversary kem)
    (preState : MlKem768PublicKey × SK × adversary.Context) (b : Bool) :
    OracleComp (unifSpec + baseSpec) Bool := do
  let pk := preState.1
  let sk := preState.2.1
  let context := preState.2.2
  let (cStar, kReal) ← kem.encaps pk
  let kRand ← runtime.liftProbComp ($ᵗ MlKemSharedSecret)
  simulateQ (kem.IND_CCA_postChallengeImpl sk cStar)
    (adversary.postChallenge ⟨pk, cStar, context⟩ (if b then kReal else kRand))

/-- The source-shaped fixed-bit branch before runtime interpretation. -/
def oneKeyBranchMain
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (adversary : OneKeyAdversary kem) (b : Bool) :
    OracleComp (unifSpec + baseSpec) Bool := do
  let preState ← oneKeyPrefix kem adversary
  oneKeyFinish kem runtime adversary preState b

/-- Runtime distribution of a fixed source branch; `true` supplies the encapsulated secret and `false` supplies an independent uniform secret. -/
def oneKeyBranch
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (adversary : OneKeyAdversary kem) (b : Bool) : SPMF Bool :=
  runtime.evalDist (oneKeyBranchMain kem runtime adversary b)

/-- A fair hidden-bit game with a shared prefix has exactly the distance of its two fixed branches, provided both branches are total. -/
theorem boolBias_sharedPrefix_eq_branchDist
    {α : Type} (coin : SPMF Bool) (preState : SPMF α)
    (finish : α → Bool → SPMF Bool)
    (hcoinTrue : Pr[= true | coin] = 1 / 2)
    (hcoinFalse : Pr[= false | coin] = 1 / 2)
    (hreal : Pr[= true | preState >>= fun state => finish state true] +
      Pr[= false | preState >>= fun state => finish state true] = 1)
    (hrandom : Pr[= true | preState >>= fun state => finish state false] +
      Pr[= false | preState >>= fun state => finish state false] = 1) :
    (do
      let state ← preState
      let b ← coin
      let z ← finish state b
      pure (b == z)).boolBiasAdvantage =
    (preState >>= fun state => finish state true).boolDistAdvantage
      (preState >>= fun state => finish state false) := by
  let game : SPMF Bool := do
    let state ← preState
    let b ← coin
    let z ← finish state b
    pure (b == z)
  let real : SPMF Bool := preState >>= fun state => finish state true
  let random : SPMF Bool := preState >>= fun state => finish state false
  let branchGame : SPMF Bool :=
    coin >>= fun b =>
      (ite (b = true) real random) >>= fun z => pure (b == z)
  have hgame : ∀ output : Bool,
      Pr[= output | game] = Pr[= output | branchGame] := by
    intro output
    calc
      Pr[= output | game] = Pr[= output | do
        let state ← preState
        let b ← coin
        let z ← finish state b
        pure (b == z)] := rfl
      _ = Pr[= output | do
            let b ← coin
            let state ← preState
            let z ← finish state b
            pure (b == z)] :=
              probOutput_bind_bind_swap preState coin
                (fun state b => finish state b >>= fun z => pure (b == z)) output
      _ = Pr[= output | branchGame] := by
        apply probOutput_bind_congr' coin output
        intro b
        cases b <;> simp [real, random]
  change game.boolBiasAdvantage = _
  rw [show game.boolBiasAdvantage = branchGame.boolBiasAdvantage by
    unfold SPMF.boolBiasAdvantage
    rw [hgame true, hgame false]]
  change branchGame.boolBiasAdvantage = real.boolDistAdvantage random
  exact SPMF.boolBiasAdvantage_eq_boolDistAdvantage_coin_branch coin real random
    hcoinTrue hcoinFalse hreal hrandom

/-- The one-key source branch distance is exactly one generic KEM IND-CCA advantage, with coefficient one. -/
theorem oneKey_indCCAAdvantage_eq_branchDist
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (adversary : OneKeyAdversary kem)
    (heval_pure : ∀ {α : Type} (a : α),
      runtime.evalDist (pure a : OracleComp (unifSpec + baseSpec) α) = pure a)
    (heval_bind : ∀ {α β : Type} (mx : OracleComp (unifSpec + baseSpec) α)
      (f : α → OracleComp (unifSpec + baseSpec) β),
      runtime.evalDist (mx >>= f) =
        runtime.evalDist mx >>= fun a => runtime.evalDist (f a))
    (heval_liftProbComp : ∀ {α : Type} (pc : ProbComp α),
      runtime.evalDist (runtime.liftProbComp pc) = 𝒟[pc])
    (hno_fail : ∀ (mx : OracleComp (unifSpec + baseSpec) Bool),
      Pr[= true | runtime.evalDist mx] + Pr[= false | runtime.evalDist mx] = 1) :
    kem.IND_CCA_Advantage runtime adversary.toINDCCA =
      SPMF.boolDistAdvantage
        (oneKeyBranch kem runtime adversary true)
        (oneKeyBranch kem runtime adversary false) := by
  let coin : SPMF Bool := 𝒟[$ᵗ Bool]
  let keygen : SPMF (MlKem768PublicKey × SK) := runtime.evalDist kem.keygen
  let pre (pksk : MlKem768PublicKey × SK) : SPMF adversary.Context :=
    runtime.evalDist (simulateQ (kem.IND_CCA_preChallengeImpl pksk.2)
      (adversary.preChallenge pksk.1))
  let finish (pksk : MlKem768PublicKey × SK) (context : adversary.Context)
      (b : Bool) : SPMF Bool := do
    let encapsulation ← runtime.evalDist (kem.encaps pksk.1)
    let kRand ← 𝒟[$ᵗ MlKemSharedSecret]
    runtime.evalDist (simulateQ
      (kem.IND_CCA_postChallengeImpl pksk.2 encapsulation.1)
      (adversary.postChallenge ⟨pksk.1, encapsulation.1, context⟩
        (if b then encapsulation.2 else kRand)))
  let preState : SPMF ((MlKem768PublicKey × SK) × adversary.Context) := do
    let pksk ← keygen
    let context ← pre pksk
    return (pksk, context)
  have hgame : kem.IND_CCA_Game runtime adversary.toINDCCA = (do
      let state ← preState
      let b ← coin
      let z ← finish state.1 state.2 b
      pure (b == z)) := by
    simp only [KEMScheme.IND_CCA_Game, OneKeyAdversary.toINDCCA,
      coin, keygen, pre, finish, preState, heval_bind, heval_pure, heval_liftProbComp,
      simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  have hbranch (b : Bool) : oneKeyBranch kem runtime adversary b = (do
      let state ← preState
      finish state.1 state.2 b) := by
    simp only [oneKeyBranch, oneKeyBranchMain, oneKeyPrefix, oneKeyFinish,
      keygen, pre, finish, preState, heval_bind, heval_liftProbComp,
      bind_assoc, pure_bind]
  have hrealTotal :
      Pr[= true | do let state ← preState; finish state.1 state.2 true] +
        Pr[= false | do let state ← preState; finish state.1 state.2 true] = 1 := by
    rw [← hbranch true]
    exact hno_fail _
  have hrandomTotal :
      Pr[= true | do let state ← preState; finish state.1 state.2 false] +
        Pr[= false | do let state ← preState; finish state.1 state.2 false] = 1 := by
    rw [← hbranch false]
    exact hno_fail _
  unfold KEMScheme.IND_CCA_Advantage
  rw [hgame, hbranch true, hbranch false]
  exact boolBias_sharedPrefix_eq_branchDist coin preState
    (fun state b => finish state.1 state.2 b)
    (by simp [coin, Fintype.card_bool]) (by simp [coin, Fintype.card_bool])
    hrealTotal hrandomTotal

/-- Public-uniform, arbitrary-base, and logical-decapsulation query surface exposed to the two source phases. -/
abbrev MlKemCCAOracleSpec (baseSpec : OracleSpec ι) :=
  (unifSpec + baseSpec) +
    (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)

/-- Predicate selecting only public-uniform queries from the combined CCA surface. -/
def IsMlKemUniformQuery {ι : Type} :
    ((unifSpec.Domain ⊕ ι) ⊕ MlKem768Ciphertext) → Prop
  | .inl (.inl _) => True
  | _ => False

/-- Predicate selecting only arbitrary base-oracle queries from the combined CCA surface. -/
def IsMlKemBaseQuery {ι : Type} :
    ((unifSpec.Domain ⊕ ι) ⊕ MlKem768Ciphertext) → Prop
  | .inl (.inr _) => True
  | _ => False

/-- Predicate selecting every logical decapsulation request, including a blocked challenge-ciphertext attempt. -/
def IsMlKemLogicalDecapsulationQuery {ι : Type} :
    ((unifSpec.Domain ⊕ ι) ⊕ MlKem768Ciphertext) → Prop
  | .inr _ => True
  | _ => False

/-- Predicate selecting only decapsulation requests unequal to the exact challenge ciphertext. -/
def IsMlKemUnblockedDecapsulationQuery
    {ι : Type} (cStar : MlKem768Ciphertext) :
    ((unifSpec.Domain ⊕ ι) ⊕ MlKem768Ciphertext) → Prop
  | .inr c => c ≠ cStar
  | _ => False

noncomputable instance instDecidablePredIsMlKemUniformQuery :
    DecidablePred (@IsMlKemUniformQuery ι) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsMlKemBaseQuery :
    DecidablePred (@IsMlKemBaseQuery ι) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsMlKemLogicalDecapsulationQuery :
    DecidablePred (@IsMlKemLogicalDecapsulationQuery ι) :=
  Classical.decPred _

noncomputable instance instDecidablePredIsMlKemUnblockedDecapsulationQuery
    (cStar : MlKem768Ciphertext) :
    DecidablePred (@IsMlKemUnblockedDecapsulationQuery ι cStar) :=
  Classical.decPred _

/-- Separate pre/post client caps for uniform, base, and logical decapsulation queries; opaque KEM-internal oracle work is outside these caps. -/
def OneKeyAdversary.MakesAtMostQueries
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    (qUPre qBPre qDPre qUPost qBPost qDPost : ℕ) : Prop :=
  (∀ pk,
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemUniformQuery qUPre ∧
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemBaseQuery qBPre ∧
    (adversary.preChallenge pk).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPre) ∧
  (∀ transcript kStar,
    (adversary.postChallenge transcript kStar).IsQueryBoundP
      IsMlKemUniformQuery qUPost ∧
    (adversary.postChallenge transcript kStar).IsQueryBoundP
      IsMlKemBaseQuery qBPost ∧
    (adversary.postChallenge transcript kStar).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPost)

/-- The corresponding separate caps on a packaged generic IND-CCA adversary. -/
def INDCCAAdversaryMakesAtMostQueries
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : kem.IND_CCA_Adversary)
    (qUPre qBPre qDPre qUPost qBPost qDPost : ℕ) : Prop :=
  (∀ pk,
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemUniformQuery qUPre ∧
    (adversary.preChallenge pk).IsQueryBoundP IsMlKemBaseQuery qBPre ∧
    (adversary.preChallenge pk).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPre) ∧
  (∀ state cStar kStar,
    (adversary.postChallenge state cStar kStar).IsQueryBoundP
      IsMlKemUniformQuery qUPost ∧
    (adversary.postChallenge state cStar kStar).IsQueryBoundP
      IsMlKemBaseQuery qBPost ∧
    (adversary.postChallenge state cStar kStar).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDPost)

theorem OneKeyAdversary.toINDCCA_pre_queryBound_iff
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop)
    [DecidablePred predicate]
    (pk : MlKem768PublicKey) (q : ℕ) :
    (adversary.toINDCCA.preChallenge pk).IsQueryBoundP predicate q ↔
      (adversary.preChallenge pk).IsQueryBoundP predicate q := by
  simp [OneKeyAdversary.toINDCCA,
    OracleComp.isQueryBoundP_map_iff]

theorem OneKeyAdversary.toINDCCA_post_queryBound_iff
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop)
    [DecidablePred predicate]
    (state : (adversary.toINDCCA).State)
    (cStar : MlKem768Ciphertext) (kStar : MlKemSharedSecret) (q : ℕ) :
    (adversary.toINDCCA.postChallenge state cStar kStar).IsQueryBoundP
        predicate q ↔
      (adversary.postChallenge ⟨state.1, cStar, state.2⟩ kStar).IsQueryBoundP
        predicate q := by
  rfl

/-- Packaging the source phases adds no query in any of the three classes. -/
theorem OneKeyAdversary.toINDCCA_makesAtMostQueries_iff
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    (qUPre qBPre qDPre qUPost qBPost qDPost : ℕ) :
    INDCCAAdversaryMakesAtMostQueries adversary.toINDCCA
        qUPre qBPre qDPre qUPost qBPost qDPost ↔
      adversary.MakesAtMostQueries
        qUPre qBPre qDPre qUPost qBPost qDPost := by
  constructor
  · intro hbounds
    constructor
    · intro pk
      simpa only [adversary.toINDCCA_pre_queryBound_iff] using hbounds.1 pk
    · intro transcript kStar
      rcases transcript with ⟨pk, cStar, context⟩
      simpa only [adversary.toINDCCA_post_queryBound_iff] using
        hbounds.2 (pk, context) cStar kStar
  · intro hbounds
    constructor
    · intro pk
      simpa only [adversary.toINDCCA_pre_queryBound_iff] using hbounds.1 pk
    · intro state cStar kStar
      simpa only [adversary.toINDCCA_post_queryBound_iff] using
        hbounds.2 ⟨state.1, cStar, state.2⟩ kStar

/-- The number of primitive-forwardable decapsulation requests is bounded by the logical interface count. -/
theorem unblockedDecapsulationQueryBound_of_logical
    {alpha : Type} {computation : OracleComp (MlKemCCAOracleSpec baseSpec) alpha}
    {q : ℕ} (cStar : MlKem768Ciphertext)
    (hbound : computation.IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery q) :
    computation.IsQueryBoundP
      (IsMlKemUnblockedDecapsulationQuery cStar) q := by
  exact hbound.of_imp (fun query hquery => by
    rcases query with query | ciphertext
    · simp [IsMlKemUnblockedDecapsulationQuery] at hquery
    · simp [IsMlKemLogicalDecapsulationQuery])

theorem OneKeyAdversary.post_unblockedDecapsulationQueryBound
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost : ℕ}
    (hbounds : adversary.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost)
    (transcript : MlKemChallengeTranscript adversary.Context)
    (kStar : MlKemSharedSecret) :
    (adversary.postChallenge transcript kStar).IsQueryBoundP
      (IsMlKemUnblockedDecapsulationQuery transcript.ciphertext) qDPost := by
  exact unblockedDecapsulationQueryBound_of_logical transcript.ciphertext
    (hbounds.2 transcript kStar).2.2

/-- Raw structural composition of the two source clients for additive client-interface accounting; this is not either simulated IND-CCA experiment and counts no opaque KEM-internal work. -/
def OneKeyAdversary.logicalClientMain
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    (pk : MlKem768PublicKey) (cStar : MlKem768Ciphertext)
    (kStar : MlKemSharedSecret) : OracleComp kem.IND_CCA_oracleSpec Bool := do
  let context ← adversary.preChallenge pk
  adversary.postChallenge ⟨pk, cStar, context⟩ kStar

theorem OneKeyAdversary.logicalClient_uniformQueryBound
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost : ℕ}
    (hbounds : adversary.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost)
    (pk : MlKem768PublicKey) (cStar : MlKem768Ciphertext)
    (kStar : MlKemSharedSecret) :
    (adversary.logicalClientMain pk cStar kStar).IsQueryBoundP
      IsMlKemUniformQuery (qUPre + qUPost) := by
  unfold logicalClientMain
  exact OracleComp.isQueryBoundP_bind (hbounds.1 pk).1
    (fun context _ => (hbounds.2 ⟨pk, cStar, context⟩ kStar).1)

theorem OneKeyAdversary.logicalClient_baseQueryBound
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost : ℕ}
    (hbounds : adversary.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost)
    (pk : MlKem768PublicKey) (cStar : MlKem768Ciphertext)
    (kStar : MlKemSharedSecret) :
    (adversary.logicalClientMain pk cStar kStar).IsQueryBoundP
      IsMlKemBaseQuery (qBPre + qBPost) := by
  unfold logicalClientMain
  exact OracleComp.isQueryBoundP_bind (hbounds.1 pk).2.1
    (fun context _ => (hbounds.2 ⟨pk, cStar, context⟩ kStar).2.1)

theorem OneKeyAdversary.logicalClient_decapsulationQueryBound
    {kem : MlKemScheme (baseSpec := baseSpec) (SK := SK)}
    (adversary : OneKeyAdversary kem)
    {qUPre qBPre qDPre qUPost qBPost qDPost : ℕ}
    (hbounds : adversary.MakesAtMostQueries
      qUPre qBPre qDPre qUPost qBPost qDPost)
    (pk : MlKem768PublicKey) (cStar : MlKem768Ciphertext)
    (kStar : MlKemSharedSecret) :
    (adversary.logicalClientMain pk cStar kStar).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery (qDPre + qDPost) := by
  unfold logicalClientMain
  exact OracleComp.isQueryBoundP_bind (hbounds.1 pk).2.2
    (fun context _ => (hbounds.2 ⟨pk, cStar, context⟩ kStar).2.2)

/-- Before the challenge, every logical decapsulation request is forwarded directly. -/
theorem indCCA_preChallengeImpl_decapsulation
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (ciphertext : MlKem768Ciphertext) :
    kem.IND_CCA_preChallengeImpl sk (.inr ciphertext) =
      kem.decaps sk ciphertext := by
  rfl

/-- After the challenge, the exact challenge ciphertext returns `none` without invoking `kem.decaps`. -/
theorem indCCA_postChallengeImpl_challenge
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar : MlKem768Ciphertext) :
    kem.IND_CCA_postChallengeImpl sk cStar (.inr cStar) =
      pure none := by
  unfold KEMScheme.IND_CCA_postChallengeImpl
  change (if cStar = cStar then
      (pure none : OracleComp (unifSpec + baseSpec)
        (Option MlKemSharedSecret))
    else kem.decaps sk cStar) = pure none
  simp

/-- After the challenge, every unequal ciphertext is forwarded exactly once to `kem.decaps`. -/
theorem indCCA_postChallengeImpl_nonchallenge
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (sk : SK) (cStar ciphertext : MlKem768Ciphertext)
    (hne : ciphertext ≠ cStar) :
    kem.IND_CCA_postChallengeImpl sk cStar (.inr ciphertext) =
      kem.decaps sk ciphertext := by
  unfold KEMScheme.IND_CCA_postChallengeImpl
  change (if ciphertext = cStar then
      (pure none : OracleComp (unifSpec + baseSpec)
        (Option MlKemSharedSecret))
    else kem.decaps sk ciphertext) = kem.decaps sk ciphertext
  simp [hne]

/-- The separate honest-recipient experiment using one key generation, one encapsulation, and one direct decapsulation. -/
def mlKem768RecipientCorrectnessExp
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec))) : SPMF Bool :=
  runtime.evalDist do
    let (pk, sk) ← kem.keygen
    let (cStar, kReal) ← kem.encaps pk
    let recovered ← kem.decaps sk cStar
    return decide (recovered = some kReal)

/-- Named recipient-agreement assumption; definitionally VCVio's generic KEM perfect correctness. -/
def MlKem768RecipientCorrectness
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec))) : Prop :=
  Pr[= true | mlKem768RecipientCorrectnessExp kem runtime] = 1

theorem mlKem768RecipientCorrectness_iff_perfectlyCorrect
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec))) :
    MlKem768RecipientCorrectness kem runtime ↔
      kem.PerfectlyCorrect runtime := by
  rfl

/-- Probability-one recipient correctness identifies every supported direct honest decapsulation with the encapsulator's secret. -/
theorem mlKem768RecipientCorrectness_recovered_eq
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (runtime : ProbCompRuntime (OracleComp (unifSpec + baseSpec)))
    (heval_pure : ∀ {α : Type} (a : α),
      runtime.evalDist (pure a : OracleComp (unifSpec + baseSpec) α) = pure a)
    (heval_bind : ∀ {α β : Type} (mx : OracleComp (unifSpec + baseSpec) α)
      (f : α → OracleComp (unifSpec + baseSpec) β),
      runtime.evalDist (mx >>= f) =
        runtime.evalDist mx >>= fun a => runtime.evalDist (f a))
    (hcorrect : MlKem768RecipientCorrectness kem runtime)
    {pk : MlKem768PublicKey} {sk : SK}
    (hkeygen : (pk, sk) ∈ support (runtime.evalDist kem.keygen))
    {cStar : MlKem768Ciphertext} {kReal : MlKemSharedSecret}
    (hencaps : (cStar, kReal) ∈ support (runtime.evalDist (kem.encaps pk)))
    {recovered : Option MlKemSharedSecret}
    (hdecaps : recovered ∈ support (runtime.evalDist (kem.decaps sk cStar))) :
    recovered = some kReal := by
  have hmem : decide (recovered = some kReal) ∈
      support (runtime.evalDist kem.CorrectExp) := by
    simp only [KEMScheme.CorrectExp, heval_bind, heval_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff, decide_eq_decide,
      exists_prop, Prod.exists]
    exact ⟨pk, sk, hkeygen, cStar, kReal, hencaps, recovered, hdecaps, Iff.rfl⟩
  simpa [MlKem768RecipientCorrectness, mlKem768RecipientCorrectnessExp,
    ((probOutput_eq_one_iff
      (mx := runtime.evalDist kem.CorrectExp) (x := true)).mp hcorrect).2] using hmem

/--
info: 'BeaconcryptCore.Computational.PqxdhKemIndCca.oneKey_indCCAAdvantage_eq_branchDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms oneKey_indCCAAdvantage_eq_branchDist

/--
info: 'BeaconcryptCore.Computational.PqxdhKemIndCca.mlKem768RecipientCorrectness_recovered_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms mlKem768RecipientCorrectness_recovered_eq

end BeaconcryptCore.Computational.PqxdhKemIndCca
