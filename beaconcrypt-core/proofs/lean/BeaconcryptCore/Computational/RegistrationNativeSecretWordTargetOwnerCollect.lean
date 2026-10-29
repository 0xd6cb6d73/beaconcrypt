-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPrefix
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution

/-! The actual complete Beacon collector is closed by the same native Word source as its original frontend. Public-header and private KEM receipts are extracted from this actual lowering with its full environment and provider state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl lower_run)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)

noncomputable def compiler : QueryImpl
    (RegistrationNativeSecretWordBeaconCollect.Spec Unit Unit Unit Unit registration.AuthenticatedResponse)
    (StateT (Auxiliary n KemSK) ProbComp) := fun query =>
  lower (localImpl setup wire route sign input inside provider outer false)
    (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query)

/-- The actual entire ordered collector lowers callback by callback with the same complete mutable source state. -/
theorem collect_run :
    lower (localImpl (n := n) setup wire route sign input inside provider outer false)
      (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated) =
      simulateQ (compiler setup wire route sign input inside provider outer owner oneTime authenticated)
        (RegistrationNativeSecretWordBeaconPrepare.prepare authenticated.pending.control () () () []) := by
  unfold RegistrationNativeSecretWordBeaconCompiler.collect
  exact RegistrationNativeSecretWordTargetServerExecution.lower_program _ _ _

/-- The lowered actual public compiler retains the exact authenticated packet and its original public-conversion equation. -/
theorem header (before after : Auxiliary n KemSK)
    (value : RegistrationNativeSecretWordBeaconPrefix.Header Unit registration.AuthenticatedResponse)
    (supported : (some value, after) ∈ support
      ((simulateQ (compiler setup wire route sign input inside provider outer owner oneTime authenticated)
        (simulateQ RegistrationNativeSecretWordBeaconCollect.ordinary
          (RegistrationNativeSecretWordBeaconPrefix.beforeDecap () []))).run before)) :
    value.response = authenticated ∧ value.ciphertext = authenticated.packet.public.kem_cipher_text ∧
      value.server = authenticated.packet.public.identity_key ∧
      setup.source.crypto.xpkConv (absBytes value.server) = some (absBytes value.serverConverted) := by
  change (some value, after) ∈ support ((simulateQ
    (fun query => lower (localImpl setup wire route sign input inside provider outer false)
      (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query)) _).run before) at supported
  rw [← RegistrationNativeSecretWordTargetServerExecution.lower_program, lower_run, support_map] at supported
  obtain ⟨⟨⟨reply, env⟩, privateState⟩, called, equal⟩ := supported
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl, rfl⟩ := equal
  apply RegistrationNativeSecretWordTargetOwnerPrefix.header setup owner oneTime authenticated before.1 env value
  apply support_simulateQ_run'_subset (localImpl setup wire route sign input inside provider outer false) _ before.2
  rw [StateT.run'_eq, support_map]
  exact ⟨((some value, env), privateState), called, rfl⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect.collect_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect.collect_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect.header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect.header
