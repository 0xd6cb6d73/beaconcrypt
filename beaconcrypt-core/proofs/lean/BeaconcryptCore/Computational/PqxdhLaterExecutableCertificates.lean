import BeaconcryptCore.Computational.PqxdhLaterSavedSampler
import BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds

/-! Structural certificates are carried by the original shared-ROM sampler for all syntactic replies; the enclosing executable continuation does not test an undecidable semantic condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates
open RawCtxForwardAnnotation RawCtxForwardCoverage RawCtxForwardScan RawCtxForwardTags
open AdaptiveCtxSharedHash

/-- The actual shared-ROM scanner returns only descriptor certificates already present in its original annotated source syntax, under arbitrary oracle replies. -/
theorem shared_scan_all {ι Local Tag Result : Type} {base : OracleSpec ι}
    (privateQuery : base.Domain → Bool) (selected : base.Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → privateQuery query = true)
    (impl : QueryImpl base (StateT Local (OracleComp HashSpec))) (predicate : Tag → Prop)
    (client : OracleComp (Spec Tag base) Result)
    (covered : Covered privateQuery client) (valid : All predicate client)
    (state reached : Local) (tag : Tag)
    (supported : Cut.pending tag reached ∈ support
      (RawCtxSharedPrefixScan.scan privateQuery selected selection impl client covered state)) : predicate tag := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [RawCtxSharedPrefixScan.scan] at supported
      cases supported
  | query_bind query next ih =>
      change Cut.pending tag reached ∈ support
        (if chosen : selected query.2 state = true then pure (.pending (query.1.get (covered.1.trans (selection query.2 state chosen))) state)
          else (impl query.2).run state >>= fun answer =>
            RawCtxSharedPrefixScan.scan privateQuery selected selection impl (next answer.1) (covered.2 answer.1) answer.2) at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact valid.1 _ (Option.some_get _).symm
      · simp only [mem_support_bind_iff] at supported
        obtain ⟨answer, _, later⟩ := supported
        exact ih answer.1 (covered.2 answer.1) (valid.2 answer.1) answer.2 later

open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => PqxdhPreparedSharedPrefix.environment original callbacks
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Pending" => PqxdhSharedParentCollect.Pending (PqxdhPrivateKemSource.SelectorSpec baseSpec) M P
    (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)

/-- The literal shared prefix supplies its saved continuation certificate for every syntactically supported result, without a condition on random-oracle replies. -/
theorem prefix_fits (start : Input) (output : HmacBlock) (depth qPost : Nat)
    (bounded : ∀ reply, (start.post reply).IsTotalQueryBound qPost)
    (pending : Pending)
    (supported : Cut.pending pending.1 pending.2 ∈ support
      (PqxdhPreparedSharedPrefix.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)) :
    PqxdhInitialOriginCertificates.Fits qPost pending.1 := by
  unfold PqxdhPreparedSharedPrefix.run PqxdhNativeSharedPrefix.carried at supported
  apply shared_scan_all _ _ _ _ _ _ _ _ _ _ _ supported
  exact PqxdhInitialOriginCertificates.program_fits (env).source _ _ (env).senderId (env).route (env).decode
    _ _ _ _ _ qPost bounded _ _

/-- The complete/cached branches keep their original Boolean; a syntactic pending output must come from the certified missing-parent branch. -/
theorem prepared_fits (start : Input) (output : HmacBlock) (depth qPost : Nat)
    (bounded : ∀ reply, (start.post reply).IsTotalQueryBound qPost)
    (pending : Pending)
    (supported : Sum.inr pending ∈ support
      (PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)) :
    PqxdhInitialOriginCertificates.Fits qPost pending.1 := by
  unfold PqxdhPreparedSharedParent.run at supported
  simp only [mem_support_bind_iff] at supported
  obtain ⟨cut, reached, supported⟩ := supported
  cases cut with
  | complete result state =>
      simp only [PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect, mem_support_pure_iff] at supported
      cases supported
  | pending context state =>
      simp only [PqxdhPreparedSharedParent.collect, PqxdhSharedParentCollect.collect] at supported
      split at supported
      · simp only [mem_support_pure_iff, Sum.inr.injEq] at supported
        subst pending
        exact prefix_fits original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth qPost bounded _ reached
      · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
        obtain ⟨_, _, impossible⟩ := supported
        cases impossible

local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)

def PacketFits (qPost : Nat) : LocalPacket → Prop
  | .inl _ => True
  | .inr (_, .inl _) => True
  | .inr (_, .inr pending) => PqxdhInitialOriginCertificates.Fits qPost pending.1

/-- Dropping the unused earlier cache and retaining the input record preserves the exact descriptor certificate. -/
theorem input_fits (start : Input) (output : HmacBlock) (depth qPost : Nat)
    (bounded : ∀ reply, (start.post reply).IsTotalQueryBound qPost)
    (result : LocalPacket)
    (supported : result ∈ support
      (PqxdhSharedParentInput.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)) :
    PacketFits qPost result := by
  simp only [PqxdhSharedParentInput.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨value, reached, rfl⟩ := supported
  cases value with
  | inl decision => trivial
  | inr pending => exact prepared_fits original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth qPost bounded pending reached

variable (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
local notation "env0" => PqxdhSourceSharedPreparation.environment setup original callbacks ∅
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK
local notation "input" => PqxdhSourceSharedInput.input setup original callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed

/-- Every possible prepared input carries the same original all-reply post budget, independently of cryptographic oracle answers. -/
theorem input_post (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (packet : Packet) (start : Input) (same : input packet = .inr start) :
    ∀ reply, (start.post reply).IsTotalQueryBound
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision => cases same
  | pending prepared ephemeral =>
      cases same
      exact PqxdhInitialPreparedSourceCaps.post_total env0 baseImpl kem program post c _

/-- The actual preparation installs the original source cap before any completed, cached or pending parent branch is chosen. -/
theorem after_fits (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (packet : Packet) (output : HmacBlock) (depth : Nat) (result : LocalPacket)
    (supported : result ∈ support (PqxdhLaterSharedParent.after setup original callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed packet output depth)) :
    PacketFits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) result := by
  unfold PqxdhLaterSharedParent.after at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported
    subst result
    trivial
  · rename_i start same
    exact input_fits env0 callbacks baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext
      start output depth _
      (input_post original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c packet start same)
      result supported

/-- Every pending result of the complete enriched sampler has a syntactic continuation certificate. All common decisions and all parent/material draws remain unchanged. -/
theorem run_fits (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat)
    (result : PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (supported : result ∈ support (PqxdhLaterSavedSampler.run setup original callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth)) :
    PacketFits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) result.2.1.1.1 := by
  simp only [PqxdhLaterSavedSampler.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, localPacket, reached, parent, _, nonce, _, chain, _, rfl⟩ := supported
  exact after_fits original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c packet output depth localPacket reached

local notation "Carrier" => PqxdhLaterSavedSampler.Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)

abbrev Certified (qPost : Nat) := { result : Carrier // PacketFits qPost result.2.1.1.1 }

/-- Attach the source's structural certificate while executing exactly the original sampler. There is no runtime branch on the proof. -/
noncomputable def certified (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat) : OracleComp HashSpec (Certified (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c)) :=
  (fun result => ⟨result.1, run_fits original callbacks baseImpl kem attachedVerify primitives program post
    selected number ancestors disclosed c depth result.1 result.2⟩) <$>
    MonadAttach.attach (PqxdhLaterSavedSampler.run setup original callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth)

/-- Erasing certificates is a literal oracle-program equality, preserving every query, source draw and original complete/cached result. -/
theorem certified_erase (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    Subtype.val <$> certified original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth =
      PqxdhLaterSavedSampler.run setup original callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth := by
  unfold certified Certified
  rw [Functor.map_map]
  exact
    (WeaklyLawfulMonadAttach.map_attach (m := OracleComp HashSpec)
      (x := PqxdhLaterSavedSampler.run setup original callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth))

/-- Proof attachment changes no complete query ledger of the actual sampler. -/
theorem certified_budget {Budget : Type}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (budget : Budget) (canQuery : HashSpec.Domain → Budget → Prop) (cost : HashSpec.Domain → Budget → Budget) :
    (certified original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth).IsQueryBound budget canQuery cost ↔
    (PqxdhLaterSharedMessagePrefix.run setup original callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth).IsQueryBound budget canQuery cost := by
  rw [← PqxdhLaterSavedSampler.run_budget setup original callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed depth budget canQuery cost,
    ← certified_erase original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth,
    isQueryBound_map_iff]

/-- The certified executable prefix erases to the same complete original material sampler with its actual reached ROM cache. -/
theorem certified_source (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat) :
    (fun result => PqxdhLaterSharedMessagePrefix.restore setup result.1.val.2 result.2) <$>
      (simulateQ hashImpl (certified original callbacks baseImpl kem attachedVerify primitives program post
        selected number ancestors disclosed c depth)).run ∅ =
    PqxdhErasedParentMaterial.prepare original.source original.recordWriter original.senderId original.route original.decode depth
      (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed) := by
  rw [← PqxdhLaterSavedSampler.source setup original callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed depth,
    ← certified_erase original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

/-- Every evaluated certificate output projects to a supported output of the identical original richer sampler. -/
theorem evaluated_support (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (depth : Nat)
    (result : Certified (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X)
      (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)
      (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) × CtxRomAuth.CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ hashImpl
      (certified original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth)).run ∅)) :
    (result.1.val, result.2) ∈ support ((simulateQ hashImpl
      (PqxdhLaterSavedSampler.run setup original callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth)).run ∅) := by
  rw [← certified_erase original callbacks baseImpl kem attachedVerify primitives program post selected number ancestors disclosed c depth,
    simulateQ_map, StateT.run_map, support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.shared_scan_all' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.shared_scan_all
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.prefix_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.prefix_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.prepared_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.prepared_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.input_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.input_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.input_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.input_post
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.after_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.after_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.run_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.run_fits
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_budget
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.certified_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.evaluated_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates.evaluated_support
