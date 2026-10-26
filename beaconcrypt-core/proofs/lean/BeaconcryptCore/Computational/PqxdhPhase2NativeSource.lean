import BeaconcryptCore.Computational.PqxdhPhase2SourceAux
import BeaconcryptCore.Computational.PqxdhPhase2PreChallenge

/-!
Concrete native Phase2 callbacks use the original optional local operations and common source cache, including the original joint identity service. The native interpreter alone owns the selected KEM secret. Its ordinary prechallenge compiler uses the same live identity state and does not receive that secret. These are exact operational equalities before any security hybrid.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2NativeSource
open PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhStatefulPhase1EufCma PqxdhInitializerSecrecy
open PqxdhBeaconPhase2Routed (AuxSpec)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRootTableInitialization (rootArray)
variable {ι I D K X Response A KemSK Auxiliary : Type} {baseSpec : OracleSpec ι}

/-- The original selected-key decapsulation runs only in the private source interpreter. -/
noncomputable def native
    (source : FixedHkdfSha512NoSaltSource)
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (aux : QueryImpl (AuxSpec I D K X Response) (StateT Auxiliary ProbComp)) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (Option K) X Response)
      (StateT Auxiliary ProbComp)
  | .inl (.decode raw) => aux (.decode raw)
  | .inl (.ciphertext response) => aux (.ciphertext response)
  | .inl (.ephemeral response) => aux (.ephemeral response)
  | .inl (.serverIdentity response) => aux (.serverIdentity response)
  | .inl (.publicConversion value) => aux (.publicConversion value)
  | .inl (.privateConversion identity) => aux (.privateConversion identity)
  | .inl (.decapsulate value none) =>
      liftM (Option.map rootArray <$> simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret (PqxdhPhase2InputBytes.ciphertext value)))
  | .inl (.decapsulate value (some prior)) => aux (.localDecapsulation value prior)
  | .inl (.dhPair pair value) => aux (.dhPair pair value)
  | .inl (.dhIdentity identity value) => aux (.dhIdentity identity value)
  | .inl (.assignedId response) => aux (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => aux (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => aux (.initial request)
  | .inr (.inr (.application response)) => aux (.application response)

/-- The ordinary interpreter forwards base work and actual selected-key decapsulation. -/
def interpretation (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    QueryImpl (MlKemCCAOracleSpec baseSpec) ProbComp :=
  kemAmbientImpl baseImpl ∘ₛ localKemPreChallengeImpl kem secret

/-- Each concrete source auxiliary callback retains its exact optional reply, local state, common cache and entire identity history. -/
theorem auxiliary_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (query : (PqxdhPhase2SourceAux.Spec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (interpretation baseImpl kem secret)
      ((borrowedAux attachedVerify primitives count source localImpl query).run state) =
      (directAux attachedVerify primitives count source localImpl query).run state := by
  rw [borrowed_step]
  change simulateQ (kemAmbientImpl baseImpl ∘ₛ localKemPreChallengeImpl kem secret) (ccaCoins _) = _
  rw [QueryImpl.simulateQ_compose]
  exact evalKem_coins baseImpl kem secret _

/-- The actual native callback uses the same original selected decapsulation, optional source operations and complete private poststate. -/
theorem pre_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (Option K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response).Domain)
    (state : SharedState A × BareState count) :
    simulateQ (interpretation baseImpl kem secret)
      ((PqxdhPhase2PreChallenge.pre source
        (borrowedAux attachedVerify primitives count source localImpl) query).run state) =
      (native source baseImpl kem secret (directAux attachedVerify primitives count source localImpl) query).run state := by
  rcases query with (query | (query | query)) <;> cases query <;>
    try exact auxiliary_step attachedVerify primitives count source localImpl baseImpl kem secret _ state
  case inl.decapsulate value key =>
    cases key with
    | some prior => exact auxiliary_step attachedVerify primitives count source localImpl baseImpl kem secret _ state
    | none =>
      change simulateQ (interpretation baseImpl kem secret)
        ((fun reply => (reply, state)) <$> (Option.map rootArray <$>
          ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext value)) : OracleComp (MlKemCCAOracleSpec baseSpec) _))) = _
      rw [simulateQ_map, simulateQ_map]
      simp only [native, StateT.run_monadLift, monadLift_self, bind_pure_comp]
      exact congrArg (fun work => (fun reply => (reply, state)) <$> (Option.map rootArray <$> work))
        (simulateQ_spec_query (interpretation baseImpl kem secret) (.inr (PqxdhPhase2InputBytes.ciphertext value)))
  all_goals exact simulateQ_pure (interpretation baseImpl kem secret) _

/-- The concrete ordinary prechallenge interpreter realizes the entire original native callback interface. -/
theorem pre_interpretation
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) :
    (interpretation baseImpl kem secret).mapStateTBase
      (PqxdhPhase2PreChallenge.pre source (borrowedAux attachedVerify primitives count source localImpl)) =
      native source baseImpl kem secret (directAux attachedVerify primitives count source localImpl) := by
  funext query state
  exact pre_step attachedVerify primitives count source localImpl baseImpl kem secret query state

/-- Every adaptive native continuation retains its complete original result and both private states under the same ordinary prechallenge interpreter. -/
theorem pre_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (Option K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response) Result)
    (state : SharedState A × BareState count) :
    simulateQ (interpretation baseImpl kem secret)
      ((simulateQ (PqxdhPhase2PreChallenge.pre source
        (borrowedAux attachedVerify primitives count source localImpl)) client).run state) =
      (simulateQ (native source baseImpl kem secret
        (directAux attachedVerify primitives count source localImpl)) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, pre_interpretation]

end BeaconcryptCore.Computational.PqxdhPhase2NativeSource

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2NativeSource.auxiliary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2NativeSource.auxiliary_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_interpretation

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2NativeSource.pre_complete
