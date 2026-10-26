import BeaconcryptCore.Computational.PqxdhInitialPrivateKdf
import BeaconcryptCore.Computational.PqxdhInitialLabelPost

/-!
Expose the same private record-KDF interpreter inside the actual Beacon registration receive, before AEAD opening and publication. Preparation, root/initializer requests, local callbacks, complete identity state and shared CTX cache retain their original order. The default fixed source law is proved from the actual raw callback.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhCorrelatedExpand PqxdhPhase2SourceAux
open PqxdhPhase1AcceptanceOracle PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

noncomputable def raw (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (SharedState A) ProbComp)) (count : Nat) :
    QueryImpl RawCtxSourceOpen.NativeSpec (StateT (SharedState A × BareState count) ProbComp) :=
  fun query state => (fun result => (result.1, (result.2, state.2))) <$>
    (RawCtxSharedPrimitive.nativeImpl fixed.crypto kdf query).run state.1

/-- The original public coin forwarding retains the complete local probabilistic computation. -/
theorem public_coins (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (work : ProbComp Result) :
    simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
      (PqxdhPhase2PostScheduler.publicWork (ccaCoins work)) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhPhase2PostScheduler.publicWork, ccaCoins, simulateQ_bind, simulateQ_spec_query]
      change ((liftM (unifSpec.query query) : ProbComp _) >>= fun answer =>
        simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
          (PqxdhPhase2PostScheduler.publicWork (ccaCoins (next answer)))) = _
      simp only [ih]

set_option backward.isDefEq.respectTransparency false in
/-- The default private interpreter is precisely the original Beacon raw-record callback, including the shared cache and retained identity state. -/
theorem raw_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : SharedState A × BareState count) :
    (PqxdhInitialRootFreeCallbacks.interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      (.inr (.inl query))).run state = (raw fixed (RawCtxSourceHkdf.kdfImpl fixed) count query).run state := by
  simp only [PqxdhInitialRootFreeCallbacks.interpreted, PqxdhInitialRootFreeCallbacks.work,
    PqxdhInitialRootFreeCallbacks.original, simulateQ_spec_query, PqxdhPhase2PostScheduler.handles,
    QueryImpl.compose, PqxdhPhase2SharedKemHandles.full, PqxdhBeaconPhase2Routed.handles,
    PqxdhBeaconPhase2Routed.sharedAux, StateT.run]
  have law := raw_complete (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl query state
  simp only [StateT.run] at law
  rw [law]
  exact public_coins baseImpl kem secret challenge _

noncomputable def compiler
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhInitialFusedCompiler.Spec I D K X Response)
      (StateT (SharedState A × BareState count) (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .inr (.inl (.inl query)) => fun state => PqxdhInitialLabelCompiler.coins ((raw fixed kdf count query).run state)
  | query => PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query

/-- The complete fused owner callback interpreter at the default private KDF is the existing source-derived compiler. Preparation, application and the private initializer capability are unchanged. -/
theorem compiler_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    compiler attachedVerify primitives count fixed (RawCtxSourceHkdf.kdfImpl fixed) localImpl baseImpl kem secret challenge =
      PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge := by
  funext query state
  cases query with
  | inl query => rfl
  | inr query => cases query with
    | inr secrets => rfl
    | inl query => cases query with
      | inr response => rfl
      | inl query =>
          simp only [compiler, PqxdhInitialFusedCompiler.compiler, raw_source]

noncomputable def finish
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .finish index raw => fun before => PqxdhPhase2PostScheduler.installed index before <$>
      (simulateQ (compiler attachedVerify primitives count fixed kdf localImpl baseImpl kem secret challenge)
        (PqxdhInitialFusedOwner.owner decode raw (before.1.roles.1.2 index))).run (before.1.primitive, before.2)


/-- The entire attempted Beacon completion specializes exactly to the original source-derived finish, retaining all live owner installation and shared/private state. -/
theorem finish_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) :
    finish (M := M) (P := P) (S := S) (B := B) attachedVerify primitives count fixed
      (RawCtxSourceHkdf.kdfImpl fixed) localImpl baseImpl kem secret challenge decode =
      PqxdhInitialLabelPost.finish attachedVerify primitives count fixed localImpl baseImpl kem secret challenge decode := by
  funext query state
  cases query with
  | finish index bytes => simp only [finish, PqxdhInitialLabelPost.finish, compiler_source]

noncomputable def target
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (SharedState A) ProbComp))
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhPhase2SourceScheduler.Spec baseSpec S B)
      (StateT (PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count)
        (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .inl (.inl query) => fun state => PqxdhInitialLabelCompiler.coins
      ((fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhInitialPrivateKdf.records fixed writer kdf sender route decode query).run state.1)
  | .inl (.inr query) => fun state => PqxdhInitialLabelCompiler.coins
      (simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
        ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge (.inl (.inr query))).run state))
  | .inr query => finish attachedVerify primitives count fixed kdf localImpl baseImpl kem secret challenge decode query


/-- The same private interpreter governs every original send/raw receive and attempted initialization in the actual adaptive scheduler. Its real specialization is the exact current post interface. -/
theorem target_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    target (P := P) (S := S) (B := B) attachedVerify primitives count fixed
      (RawCtxSourceHkdf.kdfImpl fixed) localImpl writer sender route decode baseImpl kem secret challenge =
      PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge := by
  funext query state
  cases query with
  | inr query => exact congrFun (congrFun (finish_source attachedVerify primitives count fixed localImpl baseImpl kem secret challenge decode) query) state
  | inl query => cases query with
    | inr query => rfl
    | inl query =>
        simp only [target, PqxdhInitialLabelPost.target, PqxdhPhase2PostScheduler.target,
          PqxdhInitialPrivateKdf.records_source, StateT.run, public_coins]

/-- The complete adaptive current post client specializes to the exact original labelled source schedule, for arbitrary replies, failures and final state. -/
theorem program_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    (simulateQ (target attachedVerify primitives count fixed (RawCtxSourceHkdf.kdfImpl fixed)
      localImpl writer sender route decode baseImpl kem secret challenge) client).run state =
      (simulateQ (PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl
        writer sender route decode baseImpl kem secret challenge) client).run state := by
  rw [target_source]

end BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.public_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.public_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.raw_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.compiler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.compiler_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.finish_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.target_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.target_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateBeacon.program_source
