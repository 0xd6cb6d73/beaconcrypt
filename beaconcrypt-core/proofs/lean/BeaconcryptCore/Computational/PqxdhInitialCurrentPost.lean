import BeaconcryptCore.Computational.PqxdhInitialGenericPost
import BeaconcryptCore.Computational.PqxdhInitialGenericBeaconNative
import BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon

/-!
The exact current initializer observer is factored into its original record interpreter, private identity/CCA selector and fused Beacon owner. This decomposition preserves the complete source distribution and identity/shared state in the response-only initializer monad. It is the concrete source instance of the generic whole post schedule, not a separate adversary interface.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCurrentPost
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhPhase2SourceAux PqxdhPhase1AcceptanceOracle
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

noncomputable def records (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (PqxdhPhase2SourceScheduler.State M P I D K A S B) (OracleComp PqxdhInitialLabelCompiler.Spec)) :=
  fun query state => PqxdhInitialLabelCompiler.coins
    ((PqxdhInitialPrivateKdf.records fixed writer kdf sender route decode query).run state)

noncomputable def selector
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (SelectorSpec baseSpec) (StateT (BareState count) (OracleComp PqxdhInitialLabelCompiler.Spec)) :=
  fun query state => PqxdhInitialLabelCompiler.coins
    (simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
      (PqxdhPhase2PostScheduler.publicWork ((borrowedSelector attachedVerify primitives count query).run state)))

noncomputable def owner
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes)
    (before : RawCtxBeaconLifecycle.State (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K)) :=
  simulateQ (PqxdhInitialPrivateBeacon.compiler attachedVerify primitives count fixed kdf localImpl baseImpl kem secret challenge)
    (PqxdhInitialFusedOwner.owner decode raw before)

/-- The decomposed whole scheduler is exactly the original current private-KDF target, including its complete private identity interpreter and source optional replies. -/
theorem source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    PqxdhInitialGenericPost.nativePost (P := P) (S := S) (B := B)
      (records fixed writer kdf sender route decode)
      (selector attachedVerify primitives count baseImpl kem secret challenge)
      (owner attachedVerify primitives count fixed kdf localImpl baseImpl kem secret challenge decode) =
      PqxdhInitialPrivateBeacon.target attachedVerify primitives count fixed kdf localImpl writer sender route decode baseImpl kem secret challenge := by
  funext query state
  rcases query with (query | query) | query
  case inl.inl =>
    simp only [PqxdhInitialGenericPost.nativePost, records, PqxdhInitialPrivateBeacon.target,
      StateT.run, PqxdhInitialLabelCompiler.coins, OracleComp.liftComp_map]
  case inl.inr =>
    simp only [PqxdhInitialGenericPost.nativePost, selector, PqxdhInitialPrivateBeacon.target,
      PqxdhPhase2PostScheduler.target, PqxdhPhase2PostScheduler.publicWork,
      StateT.run, PqxdhInitialLabelCompiler.coins, simulateQ_map, OracleComp.liftComp_map]
  case inr =>
    cases query
    rfl

/-- Every original adaptive post continuation has the same complete evaluated distribution in this concrete source decomposition. -/
theorem program
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (simulateQ (PqxdhInitialGenericPost.nativePost (records fixed writer kdf sender route decode)
      (selector attachedVerify primitives count baseImpl kem secret challenge)
      (owner attachedVerify primitives count fixed kdf localImpl baseImpl kem secret challenge decode)) client).run state =
      (simulateQ (PqxdhInitialPrivateBeacon.target attachedVerify primitives count fixed kdf localImpl writer sender route decode
        baseImpl kem secret challenge) client).run state := by
  rw [source]

end BeaconcryptCore.Computational.PqxdhInitialCurrentPost

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentPost.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentPost.source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCurrentPost.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCurrentPost.program
