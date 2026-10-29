-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRoot

/-! The actual checked Server preparation is an echo capability. A successful Ready stores the descriptor of its own reached collector, so later source provenance cannot substitute an unrelated prepared reference. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRootEcho
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (State Provider)
variable {n : Nat} {ι KemSK Reader E : Type} {base : OracleSpec ι}

/-- A successful actual Server root client retains precisely the descriptor computed from that same collected input. -/
theorem server (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (binding : session.RegistrationBinding)
    (collected : RegistrationNativeSecretWordServerCollect.Input Reader E PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : State n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (RegistrationNativeSecretWordLiveRoot.preparation setup wire route sign input inside provider)
        (RegistrationNativeSecretWordServerRoot.client binding collected)).run before)) :
    ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
    obtain ⟨result, reached, equal⟩ := supported
    cases referenceShape : result.1 with
    | none => simp only [referenceShape, Option.map_none] at equal; cases equal
    | some reference =>
        simp only [referenceShape, Option.map_some, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
        obtain ⟨sameReady, _sameState⟩ := equal
        cases sameReady
        apply (RegistrationNativeSecretWordLiveFlags.prepare_receipt setup wire route sign input inside provider _ reference before result.2 ?_).1
        simpa only [RegistrationNativeSecretWordLiveRoot.preparation, ← referenceShape, Prod.mk.eta] using reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRootEcho
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRootEcho.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveRootEcho.server
