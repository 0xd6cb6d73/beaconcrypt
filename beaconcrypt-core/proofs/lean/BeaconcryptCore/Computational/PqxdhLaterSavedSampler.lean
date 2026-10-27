import BeaconcryptCore.Computational.PqxdhLaterPreparedSaved

/-! The CTX-stage private continuation retains the source-generated callback parameters until use. Projection erases this extra carrier back to the unchanged executed sampler; the earlier KEM reduction receives no new interface or secret. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterSavedSampler
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids PqxdhCorrelatedExpand
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "Packet" => PqxdhSourceSharedPreparation.Packet
  (PqxdhSourceSharedPreparation.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) KemSK

local notation "LocalPacket" => PqxdhSharedParentInput.LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "input" => PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed

local notation "LocalContext" => PqxdhLaterSharedMessagePrefix.LocalContext (setup := setup) (M := M) (P := P)
  (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B)
local notation "prior" => PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed

abbrev Carrier := (KemSK × MlKem768Ciphertext) × LocalContext

noncomputable def run (depth : Nat) : OracleComp HashSpec (Carrier (setup := setup) (M := M) (P := P)
    (I := I) (K := K) (X := X) (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B)) := do
  let packet ← PqxdhSourceSharedPreparation.prepare setup env callbacks program post attachedVerify primitives baseImpl kem
  let output ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  let localPacket ← PqxdhLaterSharedParent.after setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed packet output depth
  let parent ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ FullOutput)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  pure ((packet.secretKey, packet.ciphertext),
    (((localPacket, fromOutput (PqxdhLaterSharedMessagePrefix.address setup localPacket) parent), nextChain parent), nonce, chain))

/-- Erasing the private callback parameters yields exactly the same full executed prefix, including all common/cached outcomes and every source draw. -/
theorem run_erase (depth : Nat) :
    Prod.snd <$> run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth =
      PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth := by
  simp only [run, PqxdhLaterSharedMessagePrefix.run, PqxdhLaterSharedParent.run, map_bind, map_pure, bind_assoc]

/-- The original parent sampler installs the exact source callbacks captured by the carried generation parameters, on every possible reply path. -/
theorem after_callbacks (packet : Packet) (output : HmacBlock) (depth : Nat) (result : LocalPacket)
    (supported : result ∈ support (PqxdhLaterSharedParent.after setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed packet output depth)) :
    match result with
    | .inl _ => True
    | .inr (start, _) => start.1.other =
        PqxdhInitialPreparedSourceInput.other env0 baseImpl kem attachedVerify primitives packet.secretKey packet.ciphertext := by
  unfold PqxdhLaterSharedParent.after at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported
    subst result
    trivial
  · simp only [PqxdhSharedParentInput.run, mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨value, _, rfl⟩ := supported
    rfl

/-- The richer runtime carrier retains the exact callback parameters of its own original source generation; there is no reconstruction from opaque callback functions. -/
theorem run_callbacks (depth : Nat)
    (result : Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X)
      (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B))
    (supported : result ∈ support (run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth)) :
    match result.2.1.1.1 with
    | .inl _ => True
    | .inr (start, _) => start.1.other =
        PqxdhInitialPreparedSourceInput.other env0 baseImpl kem attachedVerify primitives result.1.1 result.1.2 := by
  simp only [run, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨packet, _, output, _, localPacket, reached, parent, _, nonce, _, chain, _, rfl⟩ := supported
  cases localPacket <;> exact after_callbacks setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed packet output depth _ reached

/-- The private carrier's actual ROM evaluation erases to the unchanged material sampler, preserving the complete reached cache. -/
theorem source (depth : Nat) :
    (fun result => PqxdhLaterSharedMessagePrefix.restore setup result.1.2 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅ =
      PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth prior := by
  rw [← PqxdhLaterSharedMessagePrefix.source setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed depth,
    ← run_erase setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth]
  simp only [simulateQ_map, StateT.run_map, Functor.map_map]

/-- The original later-record event is unchanged under the entire enriched preparation and final selected-key draw; common and cached decisions are still evaluated verbatim. -/
theorem original_event (depth : Nat) :
    (do
      let result ← (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅
      let key ← $ᵗ RootOutput
      PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
        (PqxdhLaterSharedMessagePrefix.restore setup result.1.2 result.2) key) =
      PqxdhErasedParentMaterial.ideal env.source env.recordWriter env.senderId env.route env.decode depth prior := by
  unfold PqxdhErasedParentMaterial.ideal
  rw [← source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth]
  simp only [bind_map_left]

/-- Every actual pending descriptor comes with the original Post cap, source parser provenance, literal parent address and source-generated callback parameters. -/
theorem pending_scope (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat)
    (result : Carrier (setup := setup) (M := M) (P := P) (I := I) (K := K) (X := X)
      (Response := Response) (A := A) (KemSK := KemSK) (S := S) (B := B) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth)).run ∅))
    (start : Input × HmacBlock)
    (pending : PqxdhSharedParentCollect.Pending (SelectorSpec baseSpec) M P (IdentityHandle I) (DhPair setup)
      (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (shape : result.1.2.1.1.1 = .inr (start, .inr pending)) :
    PqxdhInitialOriginCertificates.Fits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) pending.1 ∧
    PqxdhInitialDescriptorScope.Valid env.decode pending.1 ∧
    result.1.2.1.1.2.address = PqxdhInitialBuilderContext.address pending.1.original ∧
    start.1.other = PqxdhInitialPreparedSourceInput.other env0 baseImpl kem attachedVerify primitives result.1.1.1 result.1.1.2 := by
  have erased : (result.1.2, result.2) ∈ support ((simulateQ hashImpl
      (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅) := by
    rw [← run_erase setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth]
    simp only [simulateQ_map, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  have scopeFacts := PqxdhLaterPreparedSaved.executed_scope setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed c depth (result.1.2, result.2) erased
  have syntactic : result.1 ∈ support (run setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth) := by
    apply support_simulateQ_run'_subset hashImpl _ ∅
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  have actual := run_callbacks setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed
    depth result.1 syntactic
  simp only [shape] at actual
  simp only [PqxdhLaterSharedMessagePrefix.restore, PqxdhSharedParentInput.restore, shape,
    PqxdhSharedParentCollect.restore, PqxdhLaterSavedSupport.PacketFits,
    PqxdhPreparedDescriptorScope.PacketValid, PqxdhErasedParentSample.address] at scopeFacts
  exact ⟨scopeFacts.1, scopeFacts.2.1, scopeFacts.2.2, actual⟩

/-- Carrying the source callback parameters preserves every complete source-interface query budget, rather than declaring their generation or later local work free. -/
theorem run_budget {Budget : Type} (depth : Nat) (budget : Budget)
    (canQuery : HashSpec.Domain → Budget → Prop) (cost : HashSpec.Domain → Budget → Budget) :
    (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth).IsQueryBound budget canQuery cost ↔
      (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth).IsQueryBound budget canQuery cost := by
  rw [← run_erase setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth,
    isQueryBound_map_iff]

end BeaconcryptCore.Computational.PqxdhLaterSavedSampler

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.after_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.after_callbacks
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_callbacks
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.original_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.original_event
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.pending_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.pending_scope
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedSampler.run_budget
