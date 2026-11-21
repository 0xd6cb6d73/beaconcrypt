-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxKernel
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntaxFree
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Physical interpretation of the actual OPEN accept free syntax uses only per-query indexed/root-prepare transports and derived CTX/public-reservation laws. Structural zero-service coverage eliminates demand/publication requirements for every reply. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (M Full interpret)
open RegistrationNativePlatformServerOpenCtxEffects (realize)
open RegistrationNativePlatformServerOpenCtxKernel (Callbacks Transport extended nativeExtended)
variable {n : Nat} {ι KemSK Extra Platform Value : Type} {base : OracleSpec ι}

theorem query (setup : Setup base KemSK) (free : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (transport : Transport setup free native) (reserve : StateT Platform ProbComp Bool)
    (request : (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK).Domain)
    (before : Full (Private n KemSK Extra) Platform)
    (allowed : ¬ RegistrationNativePlatformServerOpenSyntaxFree.IsService (n := n) (KemSK := KemSK) request) :
    Prod.map id realize <$> (interpret (extended free reserve request)).run before =
      (RegistrationAgreementNestedState.flatten (nativeExtended setup native reserve request)).run (realize before) := by
  cases request with
  | inl request => exact RegistrationNativePlatformServerOpenCtxKernel.query setup free native transport request before allowed
  | inr request => exact RegistrationNativePlatformServerOpenCtxKernel.reserve_source reserve before

theorem program (setup : Setup base KemSK) (free : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (transport : Transport setup free native) (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) Value)
    (noServices : work.IsQueryBoundP (RegistrationNativePlatformServerOpenSyntaxFree.IsService (n := n) (KemSK := KemSK)) 0)
    (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (extended free reserve) work)).run before =
      (RegistrationAgreementNestedState.flatten (simulateQ (nativeExtended setup native reserve) work)).run (realize before) := by
  rw [RegistrationNativePlatformCtxRunner.simulate]
  have whole := RegistrationNativePlatformServerOpenSyntaxFree.transport_zero
    (RegistrationNativePlatformServerOpenSyntaxFree.IsService (n := n) (KemSK := KemSK))
    (fun request => interpret (extended free reserve request))
    (RegistrationAgreementNestedState.implementation (nativeExtended setup native reserve)) realize
    (query setup free native transport reserve) work noServices before
  rw [RegistrationAgreementNestedState.program] at whole
  exact whole

/- Elaborating the closed `accept_free` application normalizes its result type with `whnf`, which would otherwise evaluate the concrete OPEN accept program (pin recomputation) deep into its byte-array construction. The proof only transports the syntactic bound, so the program is opaque here. -/
attribute [local irreducible] RegistrationNativePlatformServerOpenSyntax.accept in
theorem accept_program (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (free : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (transport : Transport setup free native) (reserve : StateT Platform ProbComp Bool)
    (material : RegistrationServerMaterialFrontend.State) (environment : RegistrationServerReferenceCompiler.Environment)
    (before : Full (Private n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (simulateQ (extended free reserve)
      (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run material).run environment))).run before =
      (RegistrationAgreementNestedState.flatten (simulateQ (nativeExtended setup native reserve)
        (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run material).run environment))).run (realize before) :=
  program setup free native transport reserve _
    (RegistrationNativePlatformServerOpenSyntaxFree.accept_free setup checks verify packet material environment) before

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.accept_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram.accept_program
