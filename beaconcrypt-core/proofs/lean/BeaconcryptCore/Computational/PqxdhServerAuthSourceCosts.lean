import BeaconcryptCore.Computational.PqxdhServerAuthGapDh
import Mathlib.Tactic.FailIfNoProgress

/-!
The exact source prefixes retain generation, all three verifications, arbitrary-key encapsulation and optional decapsulation. Primitive resource contracts count both direct draws and interpreted base callbacks. The literal Phase 1 publication is deterministic after its source-ordered inputs have been sampled. These are query bounds, not primitive security or runtime claims.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment
open PqxdhJointDhExtractRoot (RootSpec)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Direct uniform queries of an abstract primitive program. -/
def IsAmbientUniform (query : (unifSpec + baseSpec).Domain) : Prop := query.isLeft = true

/-- Base-interface queries of an abstract primitive program. -/
def IsAmbientBase (query : (unifSpec + baseSpec).Domain) : Prop := query.isRight = true

instance : DecidablePred (IsAmbientUniform (baseSpec := baseSpec)) := fun query =>
  inferInstanceAs (Decidable (query.isLeft = true))
instance : DecidablePred (IsAmbientBase (baseSpec := baseSpec)) := fun query =>
  inferInstanceAs (Decidable (query.isRight = true))

/-- Interpret every base request with its complete uniform bill; no primitive or ambient work is removed. -/
theorem ambient_uniform (impl : QueryImpl baseSpec ProbComp) (qBase : Nat)
    (baseBound : ∀ query, (impl query).IsTotalQueryBound qBase)
    {α : Type} (work : OracleComp (unifSpec + baseSpec) α) (u b : Nat)
    (uniform : work.IsQueryBoundP (IsAmbientUniform (baseSpec := baseSpec)) u) (base : work.IsQueryBoundP (IsAmbientBase (baseSpec := baseSpec)) b) :
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl impl) work).IsTotalQueryBound (u + qBase * b) := by
  induction work using OracleComp.inductionOn generalizing u b with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniform base
      rw [simulateQ_query_bind]
      rcases query with coin | query
      · have bound : ((PqxdhInitializerSecrecy.kemAmbientImpl impl) (.inl coin)).IsTotalQueryBound 1 := by
          exact ⟨Nat.one_pos, fun _ => trivial⟩
        have tail := fun reply => ih reply _ _ (uniform.2 reply) (base.2 reply)
        apply (isTotalQueryBound_bind bound tail).mono
        simp only [IsAmbientUniform, IsAmbientBase, Sum.isLeft, Sum.isRight, Bool.false_eq_true,
          not_true_eq_false, false_or, ite_true, ite_false] at uniform base ⊢
        omega
      · have tail := fun reply => ih reply _ _ (uniform.2 reply) (base.2 reply)
        apply (isTotalQueryBound_bind (baseBound query) tail).mono
        simp only [IsAmbientUniform, IsAmbientBase, Sum.isLeft, Sum.isRight, Bool.false_eq_true,
          not_true_eq_false, false_or, ite_true, ite_false] at uniform base ⊢
        rw [Nat.mul_sub_left_distrib]
        have enough : qBase ≤ qBase * b := by simpa using Nat.mul_le_mul_left qBase base.1
        omega

/-- Declared primitive-interface query counts, keeping direct randomness separate from base callbacks. -/
structure KemCaps where
  baseUniform : Nat
  keygenUniform : Nat
  keygenBase : Nat
  encapsUniform : Nat
  encapsBase : Nat
  decapsUniform : Nat
  decapsBase : Nat

/-- The complete uniform cost of one key generation. -/
def KemCaps.keygenCost (caps : KemCaps) : Nat := caps.keygenUniform + caps.baseUniform * caps.keygenBase
/-- The complete uniform cost of one encapsulation at any supplied key. -/
def KemCaps.encapsCost (caps : KemCaps) : Nat := caps.encapsUniform + caps.baseUniform * caps.encapsBase
/-- The complete uniform cost of one optional decapsulation. -/
def KemCaps.decapsCost (caps : KemCaps) : Nat := caps.decapsUniform + caps.baseUniform * caps.decapsBase

/-- Resource contracts on the unchanged primitive programs and fixed base interpreter. These bounds make no cryptographic security claim. -/
structure KemBound (setup : Setup baseSpec KemSK) (caps : KemCaps) : Prop where
  base : ∀ query, (setup.baseImpl query).IsTotalQueryBound caps.baseUniform
  keygenUniform : setup.kem.keygen.IsQueryBoundP (IsAmbientUniform (baseSpec := baseSpec)) caps.keygenUniform
  keygenBase : setup.kem.keygen.IsQueryBoundP (IsAmbientBase (baseSpec := baseSpec)) caps.keygenBase
  encapsUniform : ∀ key, (setup.kem.encaps key).IsQueryBoundP (IsAmbientUniform (baseSpec := baseSpec)) caps.encapsUniform
  encapsBase : ∀ key, (setup.kem.encaps key).IsQueryBoundP (IsAmbientBase (baseSpec := baseSpec)) caps.encapsBase
  decapsUniform : ∀ secret ciphertext, (setup.kem.decaps secret ciphertext).IsQueryBoundP (IsAmbientUniform (baseSpec := baseSpec)) caps.decapsUniform
  decapsBase : ∀ secret ciphertext, (setup.kem.decaps secret ciphertext).IsQueryBoundP (IsAmbientBase (baseSpec := baseSpec)) caps.decapsBase

/-- Actual interpreted key generation pays both declared primitive query classes. -/
theorem keygen_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps) :
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound caps.keygenCost :=
  ambient_uniform setup.baseImpl caps.baseUniform bounded.base setup.kem.keygen
    caps.keygenUniform caps.keygenBase bounded.keygenUniform bounded.keygenBase

/-- Actual interpreted encapsulation pays both declared primitive query classes for every supplied public key. -/
theorem encaps_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (key : PqxdhKemIndCca.MlKem768PublicKey) :
    (encapsulate setup key).IsTotalQueryBound caps.encapsCost := by
  unfold encapsulate
  rw [simulateQ_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact ambient_uniform setup.baseImpl caps.baseUniform bounded.base (setup.kem.encaps key)
    caps.encapsUniform caps.encapsBase (bounded.encapsUniform key) (bounded.encapsBase key)

/-- Source-prefix callback classes; all other parsing, point, conversion, freshness and DH callbacks remain in the fourth class. -/
inductive ServerKind where
  | generate | encapsulate | verify | other
  deriving DecidableEq

def serverClass {E : Type} : PqxdhServerRootPreparation.Query Reader E → ServerKind
  | .generate => .generate
  | .encapsulate _ => .encapsulate
  | .verify _ _ => .verify
  | _ => .other

def verifyCap : ServerKind → Nat
  | .verify => 3
  | .other => 6
  | _ => 0

/-- Every failed or successful signature attempt is counted in its original source position. -/
theorem verify_callbacks {E Shared : Type} (raw : Pqxdh.Bytes) (kind : ServerKind) :
    (PqxdhServerRootPreparation.verifyInput (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => serverClass query = kind) (verifyCap kind) := by
  cases kind <;> unfold PqxdhServerRootPreparation.verifyInput
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [serverClass, verifyCap], ?_⟩)
    | intro answer; cases answer
    | split

def collectCap : ServerKind → Nat
  | .generate | .encapsulate => 1
  | .verify => 0
  | .other => 11

set_option maxHeartbeats 1000000 in
/-- The later source prefix samples one scalar and makes one encapsulation, retaining every rejection branch. -/
theorem collect_callbacks {E Shared : Type} (verified : PqxdhServerRootPreparation.Verified Reader)
    (kind : ServerKind) :
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified).IsQueryBoundP
      (fun query => serverClass query = kind) (collectCap kind) := by
  cases kind <;> unfold PqxdhServerRootPreparation.collectVerified
  all_goals simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left]
  all_goals repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [serverClass, collectCap], ?_⟩)
    | (fail_if_no_progress simp only [OptionT.run_bind, OptionT.run_monadLift, Option.elimM, bind_map_left, Option.elim_some, OptionT.run_mk, OptionT.run_pure, serverClass, collectCap, Bool.not_true, Bool.false_eq_true, ite_true, ite_false])
    | intro answer; cases answer

def serverCap (kind : ServerKind) : Nat := verifyCap kind + collectCap kind

/-- The raw source prefix has caps one scalar generation, one encapsulation, three signature verifications and 17 other callback slots. -/
theorem server_callbacks {E Shared : Type} (raw : Pqxdh.Bytes) (kind : ServerKind) :
    (PqxdhServerRootPreparation.collect (Reader := Reader) (E := E) (Shared := Shared) raw).IsQueryBoundP
      (fun query => serverClass query = kind) (serverCap kind) := by
  apply isQueryBoundP_bind (verify_callbacks raw kind)
  rintro (_ | verified) _
  · trivial
  · exact collect_callbacks verified kind

instance : Fintype ServerKind where
  elems := { .generate, .encapsulate, .verify, .other }
  complete := by intro kind; cases kind <;> simp

/-- A source scalar generation is exactly the original 32-byte sampler followed by pure packaging. -/
theorem generate_uniform (setup : Setup baseSpec KemSK) :
    (generateEphemeral setup).IsTotalQueryBound 32 := by
  simpa only [generateEphemeral, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhJointGapDh.sampleScalar_uniform

def serverUniformCost (caps : KemCaps) : ServerKind → Nat
  | .generate => 32
  | .encapsulate => caps.encapsCost
  | _ => 0

set_option maxHeartbeats 1000000 in
/-- Concrete prefix callbacks pay only their actual sampling category; verification and functional point/DH checks remain explicit source callbacks. -/
theorem server_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhServerRootPreparation.Spec Reader ScalarBytes PeerEncoding).Domain)
    (consumed : List Pqxdh.Bytes) :
    (((PqxdhServerStaticDhSource.prefixImpl setup.serverDomain (serverAux setup codec checks)
      (fun _ => pure ())) query).run consumed).IsTotalQueryBound (serverUniformCost caps (serverClass query)) := by
  cases query <;> first | trivial | skip
  · change (generateEphemeral setup >>= fun value => pure (value, consumed)).IsTotalQueryBound 32
    rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact generate_uniform setup
  · change (encapsulate setup _ >>= fun value => pure (value, consumed)).IsTotalQueryBound caps.encapsCost
    rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact encaps_uniform setup caps bounded _

/-- Evaluate the complete weighted prefix bill. -/
theorem server_bill (caps : KemCaps) :
    (∑ kind, serverUniformCost caps kind * serverCap kind) = 32 + caps.encapsCost := by
  change (∑ kind ∈ ({ .generate, .encapsulate, .verify, .other } : Finset ServerKind),
    serverUniformCost caps kind * serverCap kind) = _
  simp [serverUniformCost, serverCap, verifyCap, collectCap]

/-- Every raw accept prefix retains all primitive work, while its uniform bill contains exactly one possible scalar sampler and one possible encapsulation. -/
theorem server_prefix_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    ((serverPrefix setup codec checks raw).run consumed).IsTotalQueryBound (32 + caps.encapsCost) := by
  rw [← isQueryBoundP_true_iff]
  have result := FinitePartitionQueryBounds.weighted_bound
    (serverClass (Reader := Reader) (E := ScalarBytes)) (serverUniformCost caps) serverCap
    (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain (serverAux setup codec checks) (fun _ => pure ()))
    (fun _ => True) (PqxdhServerRootPreparation.collect raw)
    (server_callbacks raw) (fun query state => (server_step_uniform setup codec checks caps bounded query state).isQueryBoundP)
    consumed
  simpa only [serverPrefix, server_bill] using result

def beaconDecaps {I D K X : Type} : PqxdhPhase2GapDhSource.Query I D K X Response → Bool
  | .decapsulate _ _ => true
  | _ => false

set_option maxHeartbeats 1000000 in
/-- The actual Beacon prefix attempts at most one optional decapsulation at the source position, without requiring successful admission. -/
theorem beacon_collect_decaps {I D K X : Type} (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhPhase2GapDhSource.collect (X := X) (Response := Response) identity oneTime kem raw).IsQueryBoundP
      (fun query => beaconDecaps query = true) 1 := by
  unfold PqxdhPhase2GapDhSource.collect
  simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, OptionT.run_monadLift, Option.elimM, bind_map_left]
  repeat' first
    | trivial
    | (rw [isQueryBoundP_query_bind_iff]; refine ⟨by simp [beaconDecaps], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim_some])
    | intro answer; cases answer

/-- Pure source metadata admission adds no decapsulation attempt. -/
theorem beacon_prepare_decaps {I D K X : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (PqxdhPhase2DhMetadata.prepare (X := X) (Response := Response) control identity oneTime kem raw).IsQueryBoundP
      (fun query => beaconDecaps query = true) 1 := by
  unfold PqxdhPhase2DhMetadata.prepare
  exact isQueryBoundP_bind (beacon_collect_decaps identity oneTime kem raw) (m := 0) (fun _ _ => trivial)

/-- Both preparation query classes include every possible reply and rejection continuation. -/
theorem beacon_callbacks {I D K X : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (kind : Bool) :
    (PqxdhPhase2DhMetadata.prepare (X := X) (Response := Response) control identity oneTime kem raw).IsQueryBoundP
      (fun query => beaconDecaps query = kind) (if kind then 1 else 12) := by
  cases kind
  · exact (PqxdhPhase2DhMetadata.prepare_bound control identity oneTime kem raw).isQueryBoundP
  · exact beacon_prepare_decaps control identity oneTime kem raw

/-- Actual optional decapsulation pays every declared direct and interpreted base draw, including unsuccessful results. -/
theorem decaps_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (secret : KemSK) (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) :
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (Option.map PqxdhRootTableInitialization.rootArray <$> setup.kem.decaps secret ciphertext)).IsTotalQueryBound caps.decapsCost := by
  rw [simulateQ_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact ambient_uniform setup.baseImpl caps.baseUniform bounded.base (setup.kem.decaps secret ciphertext)
    caps.decapsUniform caps.decapsBase (bounded.decapsUniform secret ciphertext) (bounded.decapsBase secret ciphertext)

/-- The concrete Beacon prefix has randomness only in its actual optional KEM operation. -/
theorem beacon_step_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (query : PqxdhPhase2GapDhSource.Query Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) (state : Unit) :
    (((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed)
      (fun _ => pure ())) query).run state).IsTotalQueryBound (if beaconDecaps query then caps.decapsCost else 0) := by
  cases query <;> first | trivial | skip
  case decapsulate ciphertext secret =>
    change (beaconAux setup codec beaconSeed (.decapsulate ciphertext secret) >>= fun value => pure (value, state)).IsTotalQueryBound caps.decapsCost
    rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact decaps_uniform setup caps bounded secret (PqxdhPhase2InputBytes.ciphertext ciphertext)
  case dhPair pair point => cases pair <;> trivial

/-- Full Beacon preparation retains every conversion/DH/parse callback and pays the complete single optional-decapsulation bill. -/
theorem beacon_prefix_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (caps : KemCaps) (bounded : KemBound setup caps)
    (control : pqxdh.BeaconInitSent) (identity : Unit) (oneTime : Unit ⊕ ScalarBytes)
    (kem : KemSK) (raw : Pqxdh.Bytes) (state : Unit) :
    ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run state).IsTotalQueryBound caps.decapsCost := by
  rw [← isQueryBoundP_true_iff]
  have result := FinitePartitionQueryBounds.weighted_bound
    (beaconDecaps (I := Unit) (D := Unit ⊕ ScalarBytes) (K := KemSK) (X := Unit) (Response := Response))
    (fun kind => if kind then caps.decapsCost else 0) (fun kind => if kind then 1 else 12)
    (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain (beaconAuxUnit setup codec beaconSeed) (fun _ => pure ()))
    (fun _ => True) (PqxdhPhase2DhMetadata.prepare control identity oneTime kem raw)
    (beacon_callbacks control identity oneTime kem raw)
    (fun query state => (beacon_step_uniform setup codec beaconSeed caps bounded query state).isQueryBoundP) state
  simpa only [beaconPrefix, Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false, Nat.mul_one, Nat.zero_mul, Nat.add_zero] using result

set_option backward.isDefEq.respectTransparency false in
/-- The three actual Beacon signature callbacks use the trusted deterministic signing function; no unused dynamic coin interface is executed. -/
theorem phase1_signing_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (index : Nat) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (keys : PqxdhEd25519EufCma.Phase1KeyTuple) :
    (simulateQ (phase1Impl setup codec beaconSeed oneTime)
      (PqxdhLivePhase1Bundle.signing index identity keys)).IsTotalQueryBound 0 := by
  simp only [PqxdhLivePhase1Bundle.signing, PqxdhJointPhase1SourceWriter.signingProgram,
    simulateQ_bind, simulateQ_spec_query, phase1Impl, pure_bind, simulateQ_pure]
  trivial

set_option backward.isDefEq.respectTransparency false in
/-- The original optional writer and state publication introduce no random draws. -/
theorem phase1_writing_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes) (identity : Std.Array Std.U8 32#usize)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (generated : Option (Unit ⊕ ScalarBytes))
    (state : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :
    (simulateQ (phase1Impl setup codec beaconSeed oneTime)
      (PqxdhLivePhase1Bundle.writing identity candidate generated state)).IsTotalQueryBound 0 := by
  unfold PqxdhLivePhase1Bundle.writing PqxdhBeaconPhase1Publication.afterSigning
  split <;> simp only [simulateQ_bind, simulateQ_spec_query, phase1Impl, pure_bind, simulateQ_pure]
  · trivial
  · split <;> simp only [simulateQ_pure] <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- Original Phase 1 preparation, three signatures, optional serialization and complete state publication are deterministic once its actual generated inputs are fixed. -/
theorem phase1_after_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (oneTime : ScalarBytes)
    (publicFields : PqxdhLivePhase1Bundle.Public Unit (Unit ⊕ ScalarBytes) KemSK)
    (generated : Option (Unit ⊕ ScalarBytes))
    (state : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :
    (simulateQ (phase1Impl setup codec beaconSeed oneTime)
      (PqxdhLivePhase1Bundle.afterGenerated publicFields generated state)).IsTotalQueryBound 0 := by
  unfold PqxdhLivePhase1Bundle.afterGenerated
  split <;> simp only [simulateQ_bind, simulateQ_pure]
  · trivial
  · apply isTotalQueryBound_bind (phase1_signing_uniform setup codec beaconSeed oneTime _ _ _) (n₂ := 0)
    rintro (_ | candidate)
    · simp only [simulateQ_pure]; trivial
    · exact phase1_writing_uniform setup codec beaconSeed oneTime _ candidate generated state

set_option backward.isDefEq.respectTransparency false in
/-- The body already sampled the Beacon seed, one-time scalar and KEM pair; its literal Phase 1 publication adds no hidden random draws. -/
theorem phase1_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk).IsTotalQueryBound 0 := by
  unfold phase1Run PqxdhLivePhase1Bundle.bundle
  simp only [freshBeacon, simulateQ_bind, simulateQ_spec_query, phase1Impl, pure_bind]
  exact phase1_after_uniform setup codec beaconSeed oneTime _ _ _

end BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.ambient_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.ambient_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.keygen_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.keygen_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.encaps_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.encaps_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.verify_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.verify_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.collect_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.collect_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.generate_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.generate_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_step_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_bill

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.server_prefix_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_collect_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_collect_decaps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_prepare_decaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_prepare_decaps

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_callbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.decaps_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.decaps_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_step_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.beacon_prefix_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_signing_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_signing_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_writing_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_writing_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_after_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_after_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts.phase1_uniform
