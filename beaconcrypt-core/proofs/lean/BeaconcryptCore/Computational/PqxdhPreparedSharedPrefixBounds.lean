import BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds
import BeaconcryptCore.Computational.PqxdhInitialSampledResources

/-!
The concrete prepared source input's existing callback certificate supplies the common-ROM prefix ledger. Original source callback costs are transported only across literal computation equations, and the actual retained initializer supplies its32-draw cap. Prior key generation and the earlier preparation remain a separately billed prefix.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds
open PqxdhNativeSharedPrefix PqxdhPreparedSharedPrefix PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase1AcceptanceOracle PqxdhCorrelatedExpand PqxdhPrivateKemSource AdaptiveCtxSharedHash
variable {ι M P I K X Response A N C KemSK Value : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Removing the inaccessible commitment cache changes no source-local uniform request. -/
theorem local_uniform (work : LocalCallback A N C Value) (state : ExternalState A N C) (q : Nat) :
    (work.run state).IsTotalQueryBound q ↔
      (localLift work ((state.1.1, ∅), state.1.2) state.2).IsTotalQueryBound q := by
  simp only [localLift, IsTotalQueryBound, isQueryBound_map_iff]
  rfl

variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => environment original callbacks
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

/-- The exact actual source certificate yields both prefix query bills, including all32 initializer draws and every source-local callback allowance. -/
theorem bills (start : Input) (output : HmacBlock) (depth qPost qPre qApplication qSelector qAux qKnown : Nat)
    (caps : PqxdhInitialSampledResources.Caps
      (input original callbacks baseImpl kem attachedVerify primitives secret challenge start)
      qPost qPre qApplication qSelector qAux qKnown) (hash : Bool) :
    (PqxdhPreparedSharedPrefix.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth).IsQueryBoundP
      (HashClass hash) ((7 + qPost * 67) * (if hash then 1 else 76 + qPre + qApplication + 32 + qSelector + qAux)) := by
  unfold PqxdhPreparedSharedPrefix.run
  apply PqxdhNativeSharedPrefixBounds.carried_bound
  · intro query state
    apply (local_uniform _ state qPre).mpr
    rw [PqxdhPreparedPrefixCallbacks.preparation_source]
    exact caps.preBound query ((state.1.1, ∅), state.1.2) state.2
  · intro query state
    apply (local_uniform _ state qApplication).mpr
    rw [PqxdhPreparedPrefixCallbacks.application_source]
    exact caps.applicationBound query ((state.1.1, ∅), state.1.2) state.2
  · exact initial_local_uniform _ _ _ _
  · intro query state
    apply (local_uniform _ state qSelector).mpr
    rw [PqxdhPreparedPrefixCallbacks.selector_source]
    exact caps.selectorBound query ((state.1.1, ∅), state.1.2) state.2
  · intro query state
    apply (local_uniform _ state qAux).mpr
    rw [PqxdhPreparedPrefixCallbacks.auxiliary_source]
    exact caps.auxBound query ((state.1.1, ∅), state.1.2) state.2
  · exact caps.postBound

end BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds


/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds.local_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds.local_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds.bills
