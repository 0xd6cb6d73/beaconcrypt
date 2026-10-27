import BeaconcryptCore.Computational.PqxdhPreparedSharedParent

/-! The literal prepared source supplies both the carried prefix and its completed/cached continuation through one shared ROM. Only an actual missing parent address returns a pending runtime descriptor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSharedParentInput
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
open CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => PqxdhPreparedSharedPrefix.environment original callbacks
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)
local notation "pre" => PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "application" => PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 original.source original.localImpl baseImpl kem secret challenge
local notation "selector" => PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge)
local notation "aux" => PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks

abbrev LocalPacket := Bool ⊕ ((Input × HmacBlock) × (Bool ⊕
  PqxdhSharedParentCollect.Pending (PqxdhPrivateKemSource.SelectorSpec baseSpec) M P
    (IdentityHandle I) (DhPair setup) (KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)))

noncomputable def run (start : Input) (output : HmacBlock) (depth : Nat) :
    OracleComp HashSpec (LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
      (X := X) (Response := Response) (A := A) (S := S) (B := B)) := do
  let value ← PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  pure (.inr (PqxdhErasedParentSample.forgetStart
    (PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge start, output), value))

def restore (packet : LocalPacket (setup := setup) (M := M) (P := P) (I := I) (K := K)
    (X := X) (Response := Response) (A := A) (S := S) (B := B)) (cache : CtxRO.QueryCache) :
    PqxdhErasedParentSample.Packet (extra := SelectorSpec baseSpec) (M := M) (P := P)
      (I := IdentityHandle I) (D := DhPair setup) (K := KemHandle K)
      (X := X ⊕ PqxdhPhase2JointIdentity.Converted) (Response := Response) (A := A) (N := BareState 1)
      (S := S) (B := B + 1) :=
  match packet with
  | .inl decision => .inl decision
  | .inr (start, pending) => .inr (start, PqxdhSharedParentCollect.restore pending cache)

set_option backward.isDefEq.respectTransparency false in
/-- The runtime packet retains the actual reached cache while dropping only an earlier cache field that the saved native continuation never reads. -/
theorem source (start : Input) (output : HmacBlock) (depth : Nat) (cache : CtxRO.QueryCache) :
    (fun result => restore result.1 result.2) <$>
      (simulateQ hashImpl (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)).run cache =
    (fun value => PqxdhErasedParentSample.normalize (.inr
      ((PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge
        { start with shared := (start.shared.1, cache) }, output), value))) <$>
      PqxdhErasedParentSample.sampleOne (env).source (env).recordWriter (env).senderId (env).route (env).decode depth
        (PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge
          { start with shared := (start.shared.1, cache) }, output) := by
  have actual := congrArg (fun work => (fun value => PqxdhErasedParentSample.normalize (.inr
      ((PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge
        { start with shared := (start.shared.1, cache) }, output), value))) <$> work)
    (PqxdhPreparedSharedParent.source original callbacks baseImpl kem attachedVerify primitives secret challenge
      { start with shared := (start.shared.1, cache) } output depth)
  have runEq : PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge
      { start with shared := (start.shared.1, cache) } output depth =
      PqxdhPreparedSharedParent.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth := rfl
  rw [runEq] at actual
  simpa only [run, simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure,
    map_pure, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map, restore, PqxdhErasedParentSample.normalize,
    PqxdhErasedParentSample.forgetStart, PqxdhPreparedSharedPrefix.input] using actual

end BeaconcryptCore.Computational.PqxdhSharedParentInput


/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentInput.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentInput.source
