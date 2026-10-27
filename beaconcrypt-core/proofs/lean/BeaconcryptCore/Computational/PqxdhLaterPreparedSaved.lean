import BeaconcryptCore.Computational.PqxdhLaterSavedSupport
import BeaconcryptCore.Computational.PqxdhLaterSharedMessagePrefix
import BeaconcryptCore.Computational.PqxdhInitialPreparedSourceCaps

/-! The actual authenticated preparation and complete executed later prefix supply the saved-descriptor certificates from the original source query ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterPreparedSaved
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState PqxdhPhase1AcceptanceOracle PqxdhKemIndCca
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
local notation "prior" => PqxdhInitialPreparedSourceInput.prior env0 baseImpl kem attachedVerify primitives program post selected number ancestors disclosed
local notation "MaterialContext" => PqxdhErasedParentMaterial.MaterialContext (extra := SelectorSpec baseSpec) (M := M) (P := P)
    (I := IdentityHandle I) (D := DhPair setup) (K := KemHandle K) (X := X ⊕ PqxdhPhase2JointIdentity.Converted)
    (Response := Response) (A := A) (N := BareState 1) (S := S) (B := B + 1)
local notation "LocalContext" => PqxdhLaterSharedMessagePrefix.LocalContext (setup := setup) (M := M) (P := P)
    (I := I) (K := K) (X := X) (Response := Response) (A := A) (S := S) (B := B)

/-- The literal prepared material sampler supplies both descriptor certificates and its exact parent address, consuming the original source Post budget. -/
theorem prepared_scope (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat) (context : MaterialContext)
    (supported : context ∈ support (PqxdhErasedParentMaterial.prepare env.source env.recordWriter env.senderId env.route env.decode depth prior)) :
    PqxdhLaterSavedSupport.PacketFits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) context.1.1.1 ∧
    PqxdhPreparedDescriptorScope.PacketValid env.decode context.1.1.1 ∧
    context.1.1.2.address = PqxdhErasedParentSample.address context.1.1.1 := by
  apply PqxdhLaterSavedSupport.material_scope env.source env.recordWriter env.senderId env.route env.decode depth
    (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) prior _ context supported
  intro input reached
  exact (PqxdhInitialPreparedSourceCaps.supported_caps env0 baseImpl kem attachedVerify primitives program post c
    selected number ancestors disclosed input reached).postBound

/-- The executed complete prefix supplies these same facts while retaining the ROM cache actually reached by preparation and every common or cached branch. -/
theorem executed_scope (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (depth : Nat) (result : LocalContext × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ hashImpl
      (PqxdhLaterSharedMessagePrefix.run setup env callbacks program post attachedVerify primitives baseImpl kem
        selected number ancestors disclosed depth)).run ∅)) :
    let context := PqxdhLaterSharedMessagePrefix.restore setup result.1 result.2
    PqxdhLaterSavedSupport.PacketFits (PqxdhInitialPreparedSourceCaps.postCap env0 baseImpl kem program post c) context.1.1.1 ∧
    PqxdhPreparedDescriptorScope.PacketValid env.decode context.1.1.1 ∧
    context.1.1.2.address = PqxdhErasedParentSample.address context.1.1.1 := by
  apply prepared_scope setup env callbacks program post attachedVerify primitives baseImpl kem selected number ancestors disclosed c depth
  rw [← PqxdhLaterSharedMessagePrefix.source setup env callbacks program post attachedVerify primitives baseImpl kem
    selected number ancestors disclosed depth]
  rw [support_map]
  exact ⟨result, supported, rfl⟩

end BeaconcryptCore.Computational.PqxdhLaterPreparedSaved

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterPreparedSaved.prepared_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterPreparedSaved.prepared_scope
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterPreparedSaved.executed_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterPreparedSaved.executed_scope
