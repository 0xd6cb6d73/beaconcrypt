import BeaconcryptCore.Computational.RawCtxInitialSecrecy
import BeaconcryptCore.Computational.PqxdhProtocolQueryBounds

/-!
The initial-secret component is consumed by the original registration builder before its first record is sent. The challenge is explicitly sampled before the factored builder and paid even when the builder rejects before initialization. The original fixed initializer is pure, so its actual game is literally the source builder; no random generator interchange is inferred from that fact. The global root-miss sampler remains a caller supplied distribution, whose context must be established by the authenticated-root composition. This module supplies its concrete source continuation rather than a security assumption about arbitrary established roles.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

variable {M P I D K A Context : Type} {S B : Nat}
abbrev State := PqxdhRegistrationProtocolState.State M P I D K A S B
abbrev Result := RustM (Option PqxdhServerRegistrationPublication.Response) × State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B)

noncomputable def observer
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool) :
    RawCtxInitialSecrecy.Observer Context := fun context initial => do
  let result ← (PqxdhInitialBuilderCut.protocolBuild source writer initial.1 aux senderId index metadata
    (PqxdhInitialBuilderCut.eraseRoot (ready context))).run (state context)
  outside context result

noncomputable def native
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool) : ProbComp Bool := do
  let (context, root) ← sample
  let result ← (PqxdhRegistrationProtocolState.build source writer aux senderId index metadata
    {(ready context) with root := root}).run (state context)
  outside context result

/-- The component's actual initializer observer is exactly the original source builder and its complete caller continuation, with the sampled root installed only for the source calculation. -/
theorem native_source
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool) :
    RawCtxInitialSecrecy.actual source sample (observer source writer aux senderId index metadata ready state outside) =
      native source writer aux senderId index metadata sample ready state outside := by
  rfl

/-- The actual source builder before its first send reduces to the same explicit fixed-Extract and HMAC games on the root/context sampler. -/
theorem native_bound
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool) :
    let observe := observer source writer aux senderId index metadata ready state outside
    (native source writer aux senderId index metadata sample ready state outside).boolDistance
        (RawCtxInitialSecrecy.random sample observe) ≤
      (extractRealGame hmac (RawCtxInitialSecrecy.joint sample)
        (fullExtractReduction hmac .ratchet (RawCtxInitialSecrecy.observer observe))).boolDistance
        (extractUniformGame (RawCtxInitialSecrecy.joint sample)
          (fullExtractReduction hmac .ratchet (RawCtxInitialSecrecy.observer observe))) +
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (RawCtxInitialSecrecy.joint sample)
        (RawCtxInitialSecrecy.observer observe))).boolDistance
        (hmacPrfRandomGame (fullExpandReduction .ratchet (RawCtxInitialSecrecy.joint sample)
          (RawCtxInitialSecrecy.observer observe))) := by
  simpa only [native_source] using RawCtxInitialSecrecy.primitive_bound source hmac correct sample
    (observer source writer aux senderId index metadata ready state outside)

/-- The actual source consumer pays the complete sampler, real builder callback bill and caller continuation, including rejected registrations. -/
theorem native_uniform
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (senderId : M → Std.U64) (index : Fin S) (metadata : P)
    (sample : RawCtxInitialSecrecy.Sampler Context)
    (ready : Context → PqxdhPrivateAcceptedRoot.Ready)
    (state : Context → State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B))
    (outside : Context → Result (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) → ProbComp Bool)
    (qSample qAux qOutside : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (auxBound : ∀ query primitive, ((aux query).run primitive).IsTotalQueryBound qAux)
    (outsideBound : ∀ context result, (outside context result).IsTotalQueryBound qOutside) :
    (native source writer aux senderId index metadata sample ready state outside).IsTotalQueryBound
      (qSample + ((64 + 5 * qAux) + qOutside)) := by
  exact isTotalQueryBound_bind sampleBound fun pair => isTotalQueryBound_bind
    (PqxdhProtocolQueryBounds.build_uniform source writer aux qAux auxBound senderId index metadata
      {(ready pair.1) with root := pair.2} (state pair.1)) (fun result => outsideBound pair.1 result)

end BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderSecrecy.native_uniform
