import BeaconcryptCore.Computational.PqxdhPreparedPrefixCallbacks
import BeaconcryptCore.Computational.PqxdhInitialSampledParent

/-!
The actual prepared-source prefix is compiled to the common ROM. Preparation, application, selector and publication callbacks are the literal source callbacks, using source-local allocation and writer interfaces. This file does not install a reached cache into an ordinary challenger: its complete cache equation is intended for a prefix that has already executed the actual earlier preparation through that same ROM.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma
open PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment PqxdhPhase1AcceptanceOracle
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhNativeSharedPrefix
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (original : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

/-- Concrete source allocation and serialization callbacks cannot inspect or mutate the commitment cache. -/
def environment : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B :=
  { original with phase1Writer := PqxdhSourceAuxiliary.phase1 callbacks, aux := PqxdhSourceAuxiliary.server callbacks }

variable (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (secret : KemSK) (challenge : MlKem768Ciphertext)
local notation "env" => environment original callbacks
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)
local notation "Input" => PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X)
    (Response := Response) (A := A) (S := S) (B := B) (setup := setup)

noncomputable def input (start : Input) : Input :=
  { start with other := PqxdhInitialPreparedSourceInput.other env baseImpl kem attachedVerify primitives secret challenge }

noncomputable def state (start : Input) (output : HmacBlock) : Local A (BareState 1) RootOracle.QueryCache := {
  shared := start.shared.1
  store := (fun _ => none, ⟨PqxdhInitialSourceExperiment.root original.source zeroRoot
    (RawCtxSelectedInitialConstructor.response64 output) start.selected, 0⟩)
  inputs := []
  privateState := start.privateState
  roots := start.cache
  audit := [] }

noncomputable def run (start : Input) (output : HmacBlock) (depth : Nat) :=
  PqxdhNativeSharedPrefix.carried (env).source (env).recordWriter (depth + 1)
    (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env).source (env).localImpl baseImpl kem secret challenge)
    (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env).source (env).localImpl baseImpl kem secret challenge)
    (PqxdhNativeSharedPrefix.initialLocal (env).source start.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 output))
    (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A) (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
    (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
    (PqxdhInitialSelectedOrigin.mark (env).source start.selectedMessage) (env).senderId (env).route (env).decode
    (PqxdhInitialSourceExperiment.execution (RawCtxSelectedInitialConstructor.response64 output) start.index start.metadata
      {start.ready with root := zeroRoot} start.post start.before)
    depth (state original start output)

set_option backward.isDefEq.respectTransparency false in
/-- The actual full source prefix, including its first builder and every adaptive callback, is the compiled shared-ROM computation with exactly its reached state restored. -/
theorem source (start : Input) (output : HmacBlock) (depth : Nat) :
    RawCtxSharedPrefixScan.restore attach <$>
      (simulateQ AdaptiveCtxSharedHash.hashImpl (run original callbacks baseImpl kem attachedVerify primitives secret challenge start output depth)).run start.shared.2 =
      PqxdhInitialSampledParent.sourceRun (env).source (env).recordWriter (env).senderId (env).route (env).decode depth
        (input original callbacks baseImpl kem attachedVerify primitives secret challenge start, output) := by
  unfold run
  rw [PqxdhNativeSharedPrefix.carried_source]
  simp only [PqxdhPreparedPrefixCallbacks.preparation_source, PqxdhPreparedPrefixCallbacks.application_source,
    PqxdhPreparedPrefixCallbacks.selector_source, PqxdhPreparedPrefixCallbacks.auxiliary_source, initial_source]
  rfl

/-- The actual root preparation already supplies these concrete callbacks. Normalization retains its original common decision and every pending field; it does not substitute an unrelated source input. -/
theorem input_source
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (selected : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64)
    (ancestors disclosed : List RatchetChain) :
    Sum.map id (input original callbacks baseImpl kem attachedVerify primitives context.secretKey context.ciphertext)
      (PqxdhInitialPreparedSourceInput.input env baseImpl kem attachedVerify primitives program post context selected number ancestors disclosed) =
      PqxdhInitialPreparedSourceInput.input env baseImpl kem attachedVerify primitives program post context selected number ancestors disclosed := by
  unfold PqxdhInitialPreparedSourceInput.input
  cases context.state <;> rfl

end BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix


/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix.source

/-- info: 'BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix.input_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPreparedSharedPrefix.input_source
