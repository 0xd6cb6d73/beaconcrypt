import BeaconcryptCore.Computational.PqxdhSourceSharedInput
import BeaconcryptCore.Computational.RawCtxPrefixKeyOrder

/-! The first selected record's whole actual preparation executes from one empty shared ROM before its selected message-key draw. Full64, nonce12 and nextchain32 draws retain their source correlations and order; the proof commutes the selected key only across this complete evaluated key-free prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhInitializerSecrecy
open CtxRomAuth AdaptiveCtxSharedHash PqxdhSecretInputKdf PqxdhFullSecretInputKdf
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
local notation "Context" => PqxdhAdaptiveMessageKeySource.FirstContext (M := M) (P := P) (I := I) (K := K) (X := X)
  (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "prior" => PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed

noncomputable def run : OracleComp HashSpec Context := do
  let context ← PqxdhSourceSharedInput.run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed
  let initial ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ HmacBlock)
  let nonce ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ NonceOutput)
  let chain ← simulateQ RawCtxSelectiveSharedRom.coins ($ᵗ RootOutput)
  pure (context, initial, nonce, chain)

def restore (context : Context) (cache : CtxRO.QueryCache) : Context :=
  (PqxdhSourceSharedInput.restore setup context.1 cache, context.2)

/-- The complete source-derived first-record preparation retains its actual reached ROM cache, source input and all three independent non-message-key outputs. -/
theorem source :
    (fun result => restore setup result.1 result.2) <$>
      (simulateQ hashImpl (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed)).run ∅ =
    (do
      let context ← prior
      let initial ← $ᵗ HmacBlock
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      pure (context, initial, nonce, chain)) := by
  simp only [run, simulateQ_bind, StateT.run_bind, map_bind, RawCtxSelectiveSharedRom.coins_complete, bind_map_left]
  rw [← PqxdhSourceSharedInput.source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  apply bind_congr
  intro initial
  apply bind_congr
  intro nonce
  apply bind_congr
  intro chain
  simp only [simulateQ_pure, StateT.run_pure, map_pure, restore]

/-- The same first-record source preparation can retain the full public hash-query log of the ordinary challenger without altering any source input or decision. -/
theorem shared_source :
    (fun result => restore setup result.1 result.2.1) <$>
      (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed)).run (∅, []) =
    (do
      let context ← prior
      let initial ← $ᵗ HmacBlock
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      pure (context, initial, nonce, chain)) := by
  rw [← source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed,
    ← AdaptiveCtxSharedTarget.cache_schedule _ (∅, [])]
  simp only [Functor.map_map, Prod.map_def, id_eq]

/-- Early challenge-key sampling preserves the entire original first-record source continuation after executing every prior hash against the ordinary empty ROM. The continuation is still the mathematical native key-taking observer; a secret-free CTX suffix is a separate consumer. -/
theorem key_order (real : Bool) (decodeRaw : AdaptiveCtxReceive.RawDecoder) :
    𝒟[(do
      let context ← (do
        let input ← prior
        let initial ← $ᵗ HmacBlock
        let nonce ← $ᵗ NonceOutput
        let chain ← $ᵗ RootOutput
        pure (input, initial, nonce, chain))
      let key ← $ᵗ RootOutput
      PqxdhAdaptiveMessageKeySource.firstObserve env0 context key)] =
    𝒟[(do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decodeRaw env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed))).run
          AdaptiveCtxDynamicKnownKeys.initialSource
      PqxdhAdaptiveMessageKeySource.firstObserve env0 (restore setup result.1 result.2.cache) key)] := by
  rw [← shared_source setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed]
  simp only [bind_map_left]
  apply evalDist_eq_of_evalSPMF_eq
  exact RawCtxPrefixKeyOrder.complete_vcvioLegacy real decodeRaw env.source.crypto
    (run setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed)
    (fun key context state => PqxdhAdaptiveMessageKeySource.firstObserve env0 (restore setup context state.cache) key)

/-- The named adaptive first-record endpoint consumes this actual same-ROM preparation without a final event-equivalence premise. The pending CTX suffix still has to simulate the displayed original native observer. -/
theorem adaptive_endpoint {Choice : Type} [DecidableEq Choice]
    (adaptivePost : PqxdhAdaptiveTargetPost.Post Choice program.Selection baseSpec S (B + 1))
    (targets : Choice → PqxdhAdaptiveAcceptedResult.Target S (B + 1)) (choice : Choice)
    (real : Bool) (decodeRaw : AdaptiveCtxReceive.RawDecoder) :
    𝒟[PqxdhAdaptiveMessageKeySource.firstIdeal env0 baseImpl kem attachedVerify primitives program adaptivePost targets choice] =
    𝒟[(do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl real decodeRaw env.source.crypto key)
        (simulateQ RawCtxSourceSharedRom.forward
          (run setup env callbacks program (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
            attachedVerify primitives baseImpl kem (targets choice).owner (targets choice).number
            (targets choice).ancestors (targets choice).disclosed))).run AdaptiveCtxDynamicKnownKeys.initialSource
      PqxdhAdaptiveMessageKeySource.firstObserve env0 (restore setup result.1 result.2.cache) key)] := by
  simpa only [PqxdhAdaptiveMessageKeySource.firstIdeal, PqxdhAdaptiveMessageKeySource.firstPrepare] using
    key_order setup env callbacks program (PqxdhAdaptiveTargetPost.mapPost adaptivePost (PqxdhAdaptiveTargetPost.choose choice))
      attachedVerify primitives baseImpl kem (targets choice).owner (targets choice).number
      (targets choice).ancestors (targets choice).disclosed real decodeRaw

end BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.shared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.shared_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.key_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.key_order

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.adaptive_endpoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstSharedMessagePrefix.adaptive_endpoint
