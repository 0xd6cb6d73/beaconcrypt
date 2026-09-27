import BeaconcryptCore.Computational.PqxdhSharedParentResources
import BeaconcryptCore.Computational.PqxdhPreparedSharedParent
import BeaconcryptCore.Computational.PqxdhPreparedSharedPrefixBounds
import BeaconcryptCore.Computational.PqxdhInitialSampledResources

/-!
The complete prepared parent source retains every cached continuation and the original final decision. Its actual callback certificate supplies the full shared-ROM ledger, including 32 initializer draws. The whole later-message prefix separately adds earlier preparation and output sampling.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhPreparedSharedParentBounds
open PqxdhNativeSharedPrefix PqxdhPreparedSharedPrefix PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase1AcceptanceOracle PqxdhCorrelatedExpand PqxdhPrivateKemSource AdaptiveCtxSharedHash
variable {ι M P I K X Response A N C KemSK Value : Type} {baseSpec : OracleSpec ι} {S B : Nat}

open PqxdhPreparedSharedPrefixBounds

variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => environment original callbacks
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

/-- The source callback certificate bounds the complete parent preparation, including cached continuation work and all 32 retained initializer draws. -/
theorem bills (start : Input) (output : HmacBlock) (depth qPost qPre qApplication qSelector qAux qKnown : Nat)
    (caps : PqxdhInitialSampledResources.Caps
      (input original callbacks baseImpl kem attachedVerify primitives secret challenge start)
      qPost qPre qApplication qSelector qAux qKnown) (hash : Bool) :
    (PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth).IsQueryBoundP
      (HashClass hash) ((7 + qPost * 67) * (if hash then 1 else 76 + qPre + qApplication + 32 + qSelector + qAux)) := by
  unfold PqxdhPreparedSharedParent.run PqxdhPreparedSharedPrefix.run PqxdhPreparedSharedParent.collect
  apply PqxdhSharedParentResources.prepared_bound
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

end BeaconcryptCore.Computational.PqxdhPreparedSharedParentBounds


/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedParentBounds.bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedParentBounds.bills
