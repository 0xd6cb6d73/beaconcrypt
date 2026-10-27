import BeaconcryptCore.Computational.PqxdhLaterSharedParent
import BeaconcryptCore.Computational.PqxdhErasedParentMaterial
import BeaconcryptCore.Computational.RawCtxPrefixKeyOrder

/-!
The concrete root-free source input is produced by the complete executed preparation. Its executable form keeps a cache placeholder; evaluation restores exactly the shared cache reached by the original source. This representation does not sample or install a cache and retains original common outcomes, private interpreter state, owner selection and complete source continuation.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhOrderedChainHybrids
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

abbrev LocalContext := ((LocalPacket × Entry) × RootOutput) × NonceOutput × RootOutput
local notation "prior" => PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed

def address (packet : LocalPacket) := PqxdhErasedParentSample.address (PqxdhSharedParentInput.restore packet ∅)

/-- Exact parent addresses depend on the saved native request, never on the commitment cache reached by its interpreter. -/
theorem address_cache (packet : LocalPacket) (cache : CtxRO.QueryCache) :
    address setup packet = PqxdhErasedParentSample.address (PqxdhSharedParentInput.restore packet cache) := by
  rcases packet with common | ⟨start, common | pending⟩ <;> rfl

noncomputable def run (depth : Nat) : OracleComp HashSpec (LocalContext (setup := setup) (M := M) (P := P)
    (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B)) := do
  let packet ← PqxdhLaterSharedParent.run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth
  let parent ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ FullOutput)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  pure (((packet, fromOutput (address setup packet) parent), nextChain parent), nonce, chain)

def restore (context : LocalContext (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)) (cache : CtxRO.QueryCache) :=
  (((PqxdhSharedParentInput.restore context.1.1.1 cache, context.1.1.2), context.1.2), context.2)

/-- The complete actual later-message prefix, including every parent cache-hit continuation, runs through the same ordinary empty ROM and retains the original parent76/nonce12/chain32 sampler. -/
theorem source (depth : Nat) :
    (fun result => restore setup result.1 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅ =
    PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth prior := by
  simp only [run, simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete, bind_map_left]
  rw [PqxdhErasedParentMaterial.prepare_normalized,
    ← PqxdhLaterSharedParent.source setup env callbacks program post attachedVerify primitives baseImpl kem
      selected number ancestors disclosed depth]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  apply bind_congr
  intro parent
  apply bind_congr
  intro nonce
  apply bind_congr
  intro chain
  simp only [simulateQ_pure, StateT.run_pure, map_pure, restore]
  rw [address_cache setup result.1 result.2]

/-- The same actual later prefix retains the ordinary challenger's full public hash-query history. -/
theorem shared_source (depth : Nat) :
    (fun result => restore setup result.1 result.2.1) <$>
      (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth)).run (∅, []) =
    PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth prior := by
  rw [← source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth,
    ← AdaptiveCtxSharedTarget.cache_schedule _ (∅, [])]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- The selected message key commutes across the whole actually executed later prefix. The unchanged native observer remains a mathematical key-taking endpoint for the subsequent secret-free CTX compiler. -/
theorem key_order (depth : Nat) (real : Bool) (decodeRaw : AdaptiveCtxReceive.RawDecoder) :
    𝒟[PqxdhErasedParentMaterial.ideal env.source env.recordWriter env.senderId env.route env.decode depth prior] =
    𝒟[(do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decodeRaw env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth))).run
          AdaptiveCtxDynamicKnownKeys.initialSource
      PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
        (restore setup result.1 result.2.cache) key)] := by
  unfold PqxdhErasedParentMaterial.ideal
  rw [← shared_source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth]
  simp only [bind_map_left]
  exact (RawCtxPrefixKeyOrder.complete real decodeRaw env.source.crypto
    (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed depth)
    (fun key context state => PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
      (restore setup context state.cache) key)).evalDist_eq

/-- The named adaptive later-record endpoint consumes the full source-derived ordinary-ROM prefix, preserving the actual cached/missing mixture and original final publication/freshness event. -/
theorem adaptive_endpoint {Choice : Type} [DecidableEq Choice]
    (adaptivePost : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (targets : Choice → PqxdhAdaptiveAcceptedResult.Target S (B + 1)) (choice : Choice)
    (depth : Nat) (real : Bool) (decodeRaw : AdaptiveCtxReceive.RawDecoder) :
    𝒟[PqxdhAdaptiveMessageKeySource.laterIdeal env0 baseImpl kem attachedVerify primitives program adaptivePost targets choice depth] =
    𝒟[(do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decodeRaw env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (run setup env callbacks program (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
            attachedVerify primitives baseImpl kem (targets choice).owner (targets choice).number
            (targets choice).ancestors (targets choice).disclosed depth))).run AdaptiveCtxDynamicKnownKeys.initialSource
      PqxdhErasedParentMaterial.observe env.source env.recordWriter env.senderId env.route env.decode
        (restore setup result.1 result.2.cache) key)] := by
  have erased := PqxdhErasedParentMaterial.ideal_source env.source env.recordWriter env.senderId env.route env.decode depth
    (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program
      (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
      (targets choice).owner (targets choice).number (targets choice).ancestors (targets choice).disclosed)
  have endpoint : PqxdhAdaptiveMessageKeySource.laterIdeal env0 baseImpl kem attachedVerify primitives program adaptivePost targets choice depth =
      PqxdhErasedParentMaterial.ideal env.source env.recordWriter env.senderId env.route env.decode depth
        (PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program
          (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
          (targets choice).owner (targets choice).number (targets choice).ancestors (targets choice).disclosed) := by
    simpa only [PqxdhAdaptiveMessageKeySource.laterIdeal, PqxdhAdaptiveMessageKeySource.laterPrepare,
      PqxdhAdaptiveMessageKeySource.laterObserve, bind_assoc, pure_bind,
      PqxdhSourceSharedPreparation.environment, PqxdhPreparedSharedPrefix.environment] using erased
  rw [endpoint]
  exact key_order setup env callbacks program (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
    attachedVerify primitives baseImpl kem (targets choice).owner (targets choice).number
    (targets choice).ancestors (targets choice).disclosed depth real decodeRaw

end BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.address_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.address_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.shared_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.key_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.key_order

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.adaptive_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix.adaptive_endpoint
