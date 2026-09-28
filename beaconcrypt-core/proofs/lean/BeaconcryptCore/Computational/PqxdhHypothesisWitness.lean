import BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingSecrecy
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets

/-!
# One jointly satisfying instance of the authenticated-root hypothesis bundles

This module answers audit finding F6. It builds one concrete, deliberately insecure instance on which every hypothesis of the two headline statements is proved rather than assumed, and applies both theorems to it. `hb111_instance` instantiates `PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound` (HB-111) with both of its conjuncts, because the initial `RootFields` match is proved as well. `hb112_instance` instantiates `PqxdhAuthenticatedEvolvingSecrecy.bound` (HB-112) for the selected owner `.beacon 0`, record number `1` and empty ancestor and disclosure lists.

The instance uses the empty base oracle specification, one server and one generated beacon (`S = 1`, `B = 0`, so the beacon count `B + 1` is one), `Unit` for every auxiliary type, private key state and public context, a KEM with `Unit` secret keys whose key generation, encapsulation and decapsulation are constant and deterministic, identity primitives whose signatures never verify, an adversary program that makes no query and a post-challenge continuation that returns `false` without querying. Every certified resource budget is therefore zero.

The HKDF of the toy primitive bundle is built from a toy `HmacSha512` whose output is the first 64 bytes of `message ‖ key`, so it is not constant. HKDF first extracts with the 64-byte zero salt and then computes the first two RFC 5869 Expand blocks. For every output length up to 128 bytes this is exactly HKDF-Expand over that HMAC, which covers every production length (32, 64 and 76 bytes); longer outputs are zero-padded. `ProductionHkdfPrefixConsistent`, `SourceFullCorrect` and `SourceRootCorrect` are proved for this construction over an arbitrary HMAC, so they do not rely on the particular toy HMAC.

What this shows: the hypothesis bundles of HB-111 and HB-112, including `HonestKeyCompatibility`, `HasAttachedVerificationAdapter`, `FunctionalDecapsulation`, `SourceFullCorrect`, `SourceRootCorrect`, `RootFields`, the HKDF prefix law inside the source and every field of the resource certificate, are jointly satisfiable. Neither headline theorem is vacuously true because its premises are inconsistent.

What this does not show: nothing here concerns security. The toy primitives are insecure, and the right-hand sides of both bounds are not claimed to be small; for this instance they need not be. The instance runs only the trivial adversary, so it does not show that the premises are satisfiable by the production primitives or by an adversary that actually interacts with the protocol.

Neither headline statement reaches the KEM fields `kemPub`, `encap`, `decap` or `decap_encap` of `Pqxdh.Crypto`. Their KEM enters only through the separate `kem : MlKemScheme` parameter and the explicit correctness-error term. A definition-reachability check found none of these fields in either statement, so the perfectly correct toy KEM fields of `toyCrypto` are placeholders. `actual_withKem` and `rootActual_withKem` confirm this for the actual games of HB-112 and HB-111: replacing only the KEM fields and their laws in the source leaves each actual game definitionally unchanged, which `rfl` proves. The HB-112 ideal game is not covered. Its prepared prior enters types through support-indexed subtypes, so `rfl` fails there, and this module does not attempt a propositional transfer.

`hb111_instance` repeats the HB-111 statement verbatim. That statement uses the deprecated `Pr[= true | ...]` notation, so the deprecation linter is disabled for this one declaration.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhHypothesisWitness
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame

/-! ## Toy HMAC and the HKDF built from it -/

/-- Toy HMAC: the first 64 bytes of `message ‖ key`. It depends on both inputs and has no security. -/
def toyHmac : HmacSha512 where
  eval key message := ⟨(message ++ key.toList).take 64, by simp⟩

/-- Zero-salt Extract followed by the first two RFC 5869 Expand blocks over an arbitrary HMAC, zero-padded beyond 128 bytes. -/
def hkdfOf (hmac : HmacSha512) (input info : Pqxdh.Bytes) (length : Nat) : Pqxdh.Bytes :=
  let prk := extract hmac input
  let first := hmac.eval prk (info ++ [1])
  let second := hmac.eval prk (first.toList ++ info ++ [2])
  (first.toList ++ second.toList ++ List.replicate length 0).take length

/-- The constructed HKDF returns exactly the requested number of bytes. -/
theorem hkdfOf_length (hmac : HmacSha512) (input info : Pqxdh.Bytes) (length : Nat) :
    (hkdfOf hmac input info length).length = length := by
  simp [hkdfOf]
  omega

/-- Every output of at most 76 bytes is a prefix of the 76-byte output. -/
theorem hkdfOf_prefix (hmac : HmacSha512) (input info : Pqxdh.Bytes) (short : Nat) (le : short ≤ 76) :
    hkdfOf hmac input info short = (hkdfOf hmac input info 76).take short := by
  simp only [hkdfOf, List.take_take, Nat.min_eq_left le]
  have long : ∀ first second : HmacBlock, short ≤ (first.toList ++ second.toList).length := by
    intro first second
    simp only [List.length_append, List.Vector.toList_length]
    omega
  rw [List.take_append_of_le_length (long _ _), List.take_append_of_le_length (long _ _)]

/-- The 76-byte output is the complete two-block expansion of the extracted key. -/
theorem hkdfOf_full (hmac : HmacSha512) (domain : FixedHkdfDomain) (input : Pqxdh.Bytes) :
    hkdfOf hmac input domain.info 76 = (expandFull hmac domain (extract hmac input)).toList := by
  simp only [hkdfOf, expandFull, joinBlocks, noncePart, firstExpandInput, secondExpandInput]
  generalize hmac.eval (extract hmac input) (domain.info ++ [1]) = first
  generalize hmac.eval (extract hmac input) (first.toList ++ domain.info ++ [2]) = second
  rw [List.take_append_of_le_length (by simp), List.take_append, List.Vector.toList_append,
    List.Vector.toList_take]
  simp

/-- The 32-byte root output is the first half of the first Expand block at the root label. -/
theorem hkdfOf_root (hmac : HmacSha512) (input : Pqxdh.Bytes) :
    hkdfOf hmac input Pqxdh.INFO_PQ 32 = (expandRoot hmac (extract hmac input)).toList := by
  simp only [hkdfOf, expandRoot, first32, rootExpandInput]
  generalize hmac.eval (extract hmac input) (Pqxdh.INFO_PQ ++ [1]) = first
  rw [List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp),
    List.Vector.toList_take]

/-! ## Toy primitive bundle and source -/

/-- Constant public keys and key agreement, identity signatures and encryption, a perfectly correct constant KEM, and the HKDF built from `toyHmac`. It is insecure by design. -/
def toyCrypto : Pqxdh.Crypto where
  edPub _ := List.replicate 32 0
  sign _ message := message
  verify _ message := some message
  xsk secret := secret
  xpkConv _ := some (List.replicate 32 0)
  xpub _ := List.replicate 32 0
  x25519 _ _ := List.replicate 32 0
  kemPub _ := List.replicate 1184 0
  encap _ _ := ([], List.replicate 32 0)
  decap _ _ := some (List.replicate 32 0)
  hkdf := hkdfOf toyHmac
  aeadSeal _ _ _ plaintext := (plaintext, List.replicate 16 0)
  aeadOpen _ _ _ ciphertext _ := some ciphertext
  blake2b _ := List.replicate 64 0
  verify_sign _ _ := rfl
  conv_agree _ := rfl
  dh_comm _ _ := rfl
  decap_encap _ _ := rfl
  aead_open_seal _ _ _ _ := rfl
  edPub_length _ := by simp
  xpub_length _ := by simp
  x25519_length _ _ := by simp
  kemPub_length _ := List.length_replicate ..
  encap_ss_length _ _ := by simp
  decap_length _ _ _ equal := by
    cases equal
    simp
  hkdf_length := hkdfOf_length toyHmac
  aeadSeal_tag_length _ _ _ _ := by simp
  blake2b_length _ := by simp

/-- The toy HKDF satisfies the production 32/64/76-byte prefix contract. -/
theorem toy_prefixConsistent : PqxdhJointKdf.ProductionHkdfPrefixConsistent toyCrypto :=
  ⟨fun input => hkdfOf_prefix toyHmac input _ 32 (by omega),
    fun input => hkdfOf_prefix toyHmac input _ 64 (by omega)⟩

def toySource : FixedHkdfSha512NoSaltSource := ⟨toyCrypto, toy_prefixConsistent⟩

/-- Both production labels agree with the complete toy HMAC expansion. -/
theorem toy_full_correct : SourceFullCorrect toySource toyHmac := by
  intro domain input
  apply Subtype.ext
  exact hkdfOf_full toyHmac domain input

/-- The 32-byte root agrees with the toy HMAC Extract/Expand equation. -/
theorem toy_root_correct : SourceRootCorrect toySource toyHmac := by
  intro input
  exact hkdfOf_root toyHmac input

/-! ## Toy setup, KEM, environment, primitives and adversary -/

open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhGeneratedBeaconState

/-- The empty base oracle specification. -/
abbrev Base : OracleSpec PEmpty := []ₒ

def baseImpl : QueryImpl Base ProbComp := fun query => PEmpty.elim query

/-- Honest prekey and one-time generation return fixed zero public keys without any query. -/
def toySetup : StatefulPhase1Setup Base where
  PrivatePre := Unit
  PrivateOne := Unit
  Context := Unit
  prekey _ := pure ⟨List.Vector.replicate 32 0, ()⟩
  oneTime _ _ _ := pure ⟨List.Vector.replicate 32 0, ()⟩
  publicContext _ _ _ _ := ()

def zeroCiphertext : MlKem768Ciphertext := List.Vector.replicate 1088 0

def zeroShared : MlKemSharedSecret := List.Vector.replicate 32 0

def zeroKemKey : PqxdhKemIndCca.MlKem768PublicKey := List.Vector.replicate 1184 0

/-- A constant KEM with deterministic, always-successful decapsulation. -/
def toyKem : MlKemScheme (baseSpec := Base) (SK := Unit) where
  keygen := pure (zeroKemKey, ())
  encaps _ := pure (zeroCiphertext, zeroShared)
  decaps _ _ := pure (some zeroShared)

/-- The native encapsulation never rejects and agrees with `toyKem`. -/
def toyNative : PqxdhOptionalKemSource.SourceKemInterface Base :=
  ⟨fun _ => pure (some (zeroCiphertext, zeroShared))⟩

def zeroIdentity : RawCtxServerRouting.Identity := Std.Array.repeat 32#usize 0#u8

/-- Every local callback returns a fixed reply without any query. -/
def toyLocal : QueryImpl (PqxdhPhase2SourceAux.LocalSpec Unit (DhPair toySetup) Unit Unit Unit) (StateT Unit ProbComp)
  | .decode _ => pure none
  | .ciphertext _ => pure none
  | .ephemeral _ => pure none
  | .serverIdentity _ => pure none
  | .publicConversion _ => pure none
  | .privateConversion _ => pure none
  | .dhPair _ _ => pure none
  | .dhIdentity _ _ => pure none
  | .assignedId _ => pure 0#u64
  | .localDecapsulation _ _ => pure none
  | .application _ => pure none

/-- Every registration auxiliary callback returns a fixed reply without any query. -/
def toyAux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec
    (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp)
  | .checkIdentity _ => pure false
  | .reservePeer => pure false
  | .reservePlaintext _ => pure false
  | .erase _ => pure ()
  | .write _ => pure none

def toyServer : Pqxdh.ServerState := ⟨[], 0, 0, [], []⟩

/-- One server with a zero identity and no peers, and no prior beacon. -/
def toyInitial : InitialState toySetup Unit Unit Unit Unit Unit 1 0 where
  roles := ((fun _ => ⟨⟨zeroIdentity, fun _ => none, ()⟩, 0⟩, Fin.elim0), ⟨0, []⟩)
  controls _ := ⟨0#u64⟩
  consumed _ := []
  primitive := ((), ∅)

/-- The complete toy environment, with `S = 1` and `B = 0`. -/
def toyEnv : PqxdhAuthenticatedRootExperiment.Environment toySetup Unit Unit Unit Unit Unit Unit Unit 1 0 where
  source := toySource
  recordWriter _ := none
  phase1Writer _ := pure none
  senderId _ := 0#u64
  route _ := none
  decode _ := none
  binding := ⟨zeroIdentity, 0#u64⟩
  initial := toyInitial
  localImpl := toyLocal
  native := toyNative
  server := toyServer
  application := none
  ephemeralGen := pure (List.Vector.replicate 32 0)
  aux := toyAux
  index := 0
  metadata := ()

/-- Constant identity primitives; no signature verifies. -/
def toyPrimitives : Primitives where
  publicKeys _ := ⟨List.Vector.replicate 32 0, List.Vector.replicate 32 0⟩
  sign _ _ := List.Vector.replicate 64 0
  verify _ _ _ := false
  staticDh _ _ := none

def toyAttachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes :=
  openAttached toyPrimitives.verify

/-- The adversary program makes no query. -/
def toyProgram : Program Base toySetup.Context 1 1 where
  Selection := Unit
  main _ := pure (⟨[], [], [], []⟩, ())

/-- The post-challenge continuation returns `false` without any query. -/
def toyPost : Post (baseSpec := Base) toyProgram.Selection 1 1 := fun _ _ => pure false

/-! ## The hypotheses -/

/-- The native encapsulation agrees with `toyKem` on its generated key. -/
theorem toy_compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl toyKem toyEnv.native := by
  intro pair _
  simp [toyEnv, toyNative, toyKem]

/-- The attached verifier is the adapter of the detached verifier by definition. -/
theorem toy_adapter : HasAttachedVerificationAdapter toyAttachedVerify toyPrimitives.verify :=
  fun _ _ => rfl

def toyFunctional : PqxdhChallengeSecretRouting.FunctionalDecapsulation toyKem where
  result _ _ := some zeroShared
  exact _ _ := rfl

/-- Every field of the transparent resource certificate, with all budgets zero. -/
def toyCertificate : PqxdhAuthenticatedRootBudgets.Certificate toyEnv baseImpl toyKem toyProgram toyPost where
  qLocal := 0
  localBound query _ := by cases query <;> trivial
  qAux := 0
  auxBound query _ := by cases query <;> trivial
  qWrite := 0
  writerBound _ _ := trivial
  preBudget _ := 0
  preBound _ _ := trivial
  postBudget _ := 0
  postBound _ _ _ := trivial
  noSign _ := trivial
  noCreate _ := trivial
  prekey := ⟨0, 0, 0⟩
  prekeyBound _ := ⟨trivial, trivial, trivial⟩
  oneTime := ⟨0, 0, 0⟩
  oneTimeBound _ _ _ := ⟨trivial, trivial, trivial⟩
  ephemeral := ⟨0, 0, 0⟩
  ephemeralBound := ⟨trivial, trivial, trivial⟩
  nativeEncapsulation := ⟨0, 0, 0⟩
  nativeBound _ := ⟨trivial, trivial, trivial⟩
  totalEncapsulation := ⟨0, 0, 0⟩
  totalBound _ := ⟨trivial, trivial, trivial⟩
  qKeygen := 0
  keygenBound := trivial
  qEncap := 0
  encapsBound _ := trivial
  qBase := 0
  baseBound query := PEmpty.elim query
  qDecap := 0
  decapsBound _ _ := trivial

/-- The initial server state matches the native root fields read by registration. -/
theorem toy_root_fields :
    PqxdhProtocolServerInvariant.RootFields toyEnv.source.crypto (fun _ => toyServer.ikSk)
      toyEnv.senderId toyEnv.index toyEnv.server toyEnv.initial := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  decide

/-! ## Both headline theorems on the instance -/

def toySelected : RawCtxProtocolReveals.Owner 1 (0 + 1) := .beacon 0

def toyDynamicFallback : PqxdhDynamicIdentityRouting.DynamicForgery := ⟨0, ⟨[], List.Vector.replicate 64 0⟩⟩

def toyOrdinaryFallback : PqxdhJointIdentity.Forgery := ⟨[], List.Vector.replicate 64 0⟩

/-- HB-112 with every hypothesis proved: selected owner `.beacon 0`, record number `1`, no ancestors and no disclosures. -/
theorem hb112_instance :
    (PqxdhInitialRootEventSecrecy.actual toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives toyProgram toyPost
        toySelected 1#u64 [] []).boolDistAdvantage
      (PqxdhAuthenticatedEvolvingSecrecy.ideal toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives toyProgram
        toyPost toySelected 1#u64 [] []) ≤
    PqxdhAuthenticatedEvolvingSecrecy.loss toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives toyProgram toyPost
      toySelected 1#u64 [] [] toyCertificate toyHmac toyDynamicFallback toyOrdinaryFallback :=
  PqxdhAuthenticatedEvolvingSecrecy.bound toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives toyProgram toyPost
    toySelected 1#u64 [] [] toyCertificate (by decide) toy_compatible toy_adapter toyFunctional toyHmac
    toy_full_correct toyDynamicFallback toyOrdinaryFallback

set_option linter.deprecated false in
/-- HB-111 with every hypothesis proved, including the initial `RootFields` match, so both conjuncts hold. -/
theorem hb111_instance :
    let p := PqxdhAuthenticatedRootExperiment.protocol toyEnv toyKem toyAttachedVerify toyPrimitives toyProgram toyPost
    ((PqxdhAuthenticatedRootExperiment.actual toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives toyProgram
        toyPost).boolDistAdvantage
      (PqxdhCorrelatedExpandHybrid.uniformGame (PqxdhCorrelatedExpand.rootReduction toyEnv.source baseImpl toyKem p)) ≤
      (PqxdhJointIdentity.advantage toyPrimitives
        (PqxdhGeneratedPhase1Prefix.privateReduction toyPrimitives baseImpl toyKem toySetup
          (driver toyEnv.toDriverEnvironment toyProgram) toyDynamicFallback toyOrdinaryFallback)).toReal +
      Pr[= true | simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (PqxdhKemCorrectnessError.errorExperiment toyKem)].toReal +
      toyKem.IND_CCA_Advantage (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction toyEnv.source toyKem p).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage toyHmac
        (PqxdhCorrelatedExtractFamily.reduction toyEnv.source toyHmac baseImpl toyKem p) +
      ∑ index ∈ Finset.range toyCertificate.qRoot,
        (hmacPrfRealGame toyHmac (PqxdhCorrelatedExpandHybrid.indexedReduction toyHmac
            (PqxdhCorrelatedExpand.rootReduction toyEnv.source baseImpl toyKem p) index)).boolDistAdvantage
          (hmacPrfRandomGame (PqxdhCorrelatedExpandHybrid.indexedReduction toyHmac
            (PqxdhCorrelatedExpand.rootReduction toyEnv.source baseImpl toyKem p) index))) ∧
    ∀ result ∈ support (PqxdhPrivateSourceCoins.privateRun toyAttachedVerify toyPrimitives 1
      (PqxdhGeneratedPhase1Prefix.program baseImpl toyKem toySetup (driver toyEnv.toDriverEnvironment toyProgram))),
      ∃ output, result.1.map PqxdhPrivateRootSource.eraseOutput = some output ∧
        PqxdhProtocolServerInvariant.RootFields toyEnv.source.crypto (fun _ => toyServer.ikSk) toyEnv.senderId
          toyEnv.index toyEnv.server output.context.selection.2 :=
  PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound toyEnv baseImpl toyKem toyAttachedVerify toyPrimitives
    toyProgram toyPost toyCertificate toy_compatible toy_adapter toyFunctional toyHmac toy_root_correct
    toyDynamicFallback toyOrdinaryFallback (fun _ => toyServer.ikSk) toy_root_fields

/-! ## The actual games do not read the KEM fields of `Pqxdh.Crypto` -/

section KemFields
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
    {setup : StatefulPhase1Setup baseSpec}

/-- Replace exactly `kemPub`, `encap`, `decap` and their laws in a primitive bundle. -/
def withKem (c : Pqxdh.Crypto) (kemPub : Pqxdh.Bytes → Pqxdh.Bytes)
    (encap : Pqxdh.Bytes → Pqxdh.Bytes → Pqxdh.Bytes × Pqxdh.Bytes)
    (decap : Pqxdh.Bytes → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (decap_encap : ∀ sk coins, decap sk (encap (kemPub sk) coins).1 = some (encap (kemPub sk) coins).2)
    (kemPub_length : ∀ sk, (kemPub sk).length = 1184)
    (encap_ss_length : ∀ pk coins, (encap pk coins).2.length = 32)
    (decap_length : ∀ sk ct ss, decap sk ct = some ss → ss.length = 32) : Pqxdh.Crypto :=
  { c with
    kemPub := kemPub
    encap := encap
    decap := decap
    decap_encap := decap_encap
    kemPub_length := kemPub_length
    encap_ss_length := encap_ss_length
    decap_length := decap_length }

/-- The same source with only its KEM fields replaced; the HKDF prefix law is unchanged. -/
def sourceWithKem (source : FixedHkdfSha512NoSaltSource) (kemPub : Pqxdh.Bytes → Pqxdh.Bytes)
    (encap : Pqxdh.Bytes → Pqxdh.Bytes → Pqxdh.Bytes × Pqxdh.Bytes)
    (decap : Pqxdh.Bytes → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (decap_encap : ∀ sk coins, decap sk (encap (kemPub sk) coins).1 = some (encap (kemPub sk) coins).2)
    (kemPub_length : ∀ sk, (kemPub sk).length = 1184)
    (encap_ss_length : ∀ pk coins, (encap pk coins).2.length = 32)
    (decap_length : ∀ sk ct ss, decap sk ct = some ss → ss.length = 32) : FixedHkdfSha512NoSaltSource :=
  ⟨withKem source.crypto kemPub encap decap decap_encap kemPub_length encap_ss_length decap_length,
    ⟨source.prefixConsistent.rootPrefix, source.prefixConsistent.ratchetPrefix⟩⟩

/-- The HB-112 actual game is definitionally unchanged when only the KEM fields of the source primitive bundle change. -/
theorem actual_withKem
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List beaconcrypt_core.ratchet.RatchetChain)
    (kemPub : Pqxdh.Bytes → Pqxdh.Bytes)
    (encap : Pqxdh.Bytes → Pqxdh.Bytes → Pqxdh.Bytes × Pqxdh.Bytes)
    (decap : Pqxdh.Bytes → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (decap_encap : ∀ sk coins, decap sk (encap (kemPub sk) coins).1 = some (encap (kemPub sk) coins).2)
    (kemPub_length : ∀ sk, (kemPub sk).length = 1184)
    (encap_ss_length : ∀ pk coins, (encap pk coins).2.length = 32)
    (decap_length : ∀ sk ct ss, decap sk ct = some ss → ss.length = 32) :
    PqxdhInitialRootEventSecrecy.actual
        { env with
          source := sourceWithKem env.source kemPub encap decap decap_encap kemPub_length encap_ss_length
            decap_length }
        baseImpl kem attachedVerify primitives program post selected number ancestors disclosed =
      PqxdhInitialRootEventSecrecy.actual env baseImpl kem attachedVerify primitives program post selected number
        ancestors disclosed := by
  rfl

/-- The HB-111 actual game is definitionally unchanged when only the KEM fields of the source primitive bundle change. -/
theorem rootActual_withKem
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (kemPub : Pqxdh.Bytes → Pqxdh.Bytes)
    (encap : Pqxdh.Bytes → Pqxdh.Bytes → Pqxdh.Bytes × Pqxdh.Bytes)
    (decap : Pqxdh.Bytes → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (decap_encap : ∀ sk coins, decap sk (encap (kemPub sk) coins).1 = some (encap (kemPub sk) coins).2)
    (kemPub_length : ∀ sk, (kemPub sk).length = 1184)
    (encap_ss_length : ∀ pk coins, (encap pk coins).2.length = 32)
    (decap_length : ∀ sk ct ss, decap sk ct = some ss → ss.length = 32) :
    PqxdhAuthenticatedRootExperiment.actual
        { env with
          source := sourceWithKem env.source kemPub encap decap decap_encap kemPub_length encap_ss_length
            decap_length }
        baseImpl kem attachedVerify primitives program post =
      PqxdhAuthenticatedRootExperiment.actual env baseImpl kem attachedVerify primitives program post := by
  rfl

end KemFields

end BeaconcryptCore.Computational.PqxdhHypothesisWitness

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_length

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_full

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hkdfOf_root

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_prefixConsistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_prefixConsistent

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_full_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_full_correct

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_root_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_root_correct

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_compatible

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_adapter' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.toy_root_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hb112_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hb112_instance

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.hb111_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.hb111_instance

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.actual_withKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.actual_withKem

/-- info: 'BeaconcryptCore.Computational.PqxdhHypothesisWitness.rootActual_withKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhHypothesisWitness.rootActual_withKem
