import BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix
import BeaconcryptCore.Computational.PqxdhSharedParentCollect
import BeaconcryptCore.Computational.PqxdhErasedParentSample

/-! The literal prepared source supplies both the carried prefix and its completed/cached continuation through one shared ROM. Only an actual missing parent address returns a pending runtime descriptor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedSharedParent
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

noncomputable def collect (start : Input) (output : HmacBlock) (depth : Nat) :=
  PqxdhSharedParentCollect.collect (P := P) (env).source (env).recordWriter pre application
    (initialLocal (env).source start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)) selector aux
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
    (PqxdhInitialSourceExperiment.root (env).source zeroRoot (RawCtxSelectedInitialConstructor.response64 output) start.selected)
    start.selected start.number start.ancestors start.disclosed depth

noncomputable def run (start : Input) (output : HmacBlock) (depth : Nat) := do
  let cut ← PqxdhPreparedSharedPrefix.run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  collect original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth cut

set_option backward.isDefEq.respectTransparency false in
/-- The actual source's complete prepared sampler retains all cached/common branches and the literal reached pending state without support-proof or event-equality assumptions. -/
theorem source (start : Input) (output : HmacBlock) (depth : Nat) :
    (fun result => PqxdhSharedParentCollect.restore result.1 result.2) <$>
      (simulateQ hashImpl (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)).run start.shared.2 =
    PqxdhErasedParentSample.sampleOne (env).source (env).recordWriter (env).senderId (env).route (env).decode depth
      (PqxdhPreparedSharedPrefix.input original callbacks baseImpl kem attachedVerify primitives secret challenge start, output) := by
  simp only [run, simulateQ_bind, StateT.run_bind, map_bind, PqxdhErasedParentSample.sampleOne,
    PqxdhInitialPreparedParent.prepare]
  have prefixRun := PqxdhPreparedSharedPrefix.source original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth
  unfold PqxdhInitialSampledParent.sourceRun at prefixRun
  rw [← prefixRun]
  simp only [bind_map_left]
  apply bind_congr
  intro result
  have actual := PqxdhSharedParentCollect.collect_source (env).source (env).recordWriter pre application
    (initialLocal (env).source start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output)) selector aux
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
    (PqxdhInitialSourceExperiment.root (env).source zeroRoot (RawCtxSelectedInitialConstructor.response64 output) start.selected)
    start.selected start.number start.ancestors start.disclosed depth result.1 result.2
  simp only [PqxdhPreparedPrefixCallbacks.preparation_source, PqxdhPreparedPrefixCallbacks.application_source,
    PqxdhPreparedPrefixCallbacks.selector_source, PqxdhPreparedPrefixCallbacks.auxiliary_source, initial_source] at actual
  dsimp only [collect,
    PqxdhInitialSourcePreparedSecrecy.pre, PqxdhInitialSourcePreparedSecrecy.application,
    PqxdhInitialSourcePreparedSecrecy.selector, PqxdhInitialSourcePreparedSecrecy.aux,
    PqxdhInitialSourcePreparedSecrecy.observe, PqxdhPreparedSharedPrefix.input,
    PqxdhInitialPreparedSourceInput.other, PqxdhPreparedSharedPrefix.environment,
    PqxdhInitialSampledParent.response, PqxdhInitialSampledParent.marker] at actual ⊢
  exact actual

end BeaconcryptCore.Computational.PqxdhPreparedSharedParent


/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedParent.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedParent.source
