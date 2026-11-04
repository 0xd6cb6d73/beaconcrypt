-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput
import BeaconcryptCore.Computational.RegistrationNativeServerPublicContents

/-! Actual checked Init authentication and successful Server admission identify the classical Server identity carried by the earlier source response stage. This uses the literal matched token and admission checks, without assuming a repeated pin call returned its stored value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMatchedServerPin
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin RegistrationServerNativeSource.agree

/-- A matched actual token's successful Server initial capability uses the configured classical Server identity. -/
theorem initial_identity (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (token : peer.ConsumedRegistration)
    (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (receipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (control : pqxdh.ServerState) (actualPin : session.ServerAuthenticationPin) (availability : pqxdh.KeyIdAvailability)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (admitted : registration.begin_server_completion control actualPin availability token.agreement application = .ok (.Ok initial)) :
    initial.candidate.server_identity_public_key = pin.binding.identity_public_key := by
  have supported := receipt.checked
  rw [RegistrationNativeInitAuthentication.authenticate, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have valueEq : inner.1 = .ok (receipt.events, .Accepted receipt.authenticated) := congrArg Prod.fst same
  have native : (.ok (receipt.events, .Accepted receipt.authenticated), inner.2) ∈ support
      ((RegistrationWorldAuthentication.begin setup (RegistrationNativeWire.ledgerCodec wire) route source.verify receipt.before.pin receipt.packet).run receipt.before.world.world.1) := by
    simpa only [← valueEq, Prod.mk.eta] using called
  have actual := RegistrationWorldAuthentication.begin_native_support setup (RegistrationNativeWire.ledgerCodec wire) route source.verify receipt.before.pin receipt.packet
    receipt.before.world.world.1 inner.2 receipt.events receipt.authenticated native
  have selected := RegistrationAuthenticationNative.begin_selected_pin setup.source.crypto source.verify
    (RegistrationNativeWire.ledgerCodec wire).frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) receipt.before.pin receipt.packet
    (RegistrationWorldAuthentication.project receipt.before.world.world.1) (RegistrationWorldAuthentication.project inner.2)
    receipt.events receipt.authenticated (by simpa only [RegistrationAuthenticationShared.begin] using actual)
  have binding : token.agreement.binding = receipt.authenticated.binding :=
    congrArg (fun value : agreement.ServerAgreement => value.binding) receipt.root.completedEq
  have samePin := (RegistrationNativeServerBindingReceipt.initial_root control actualPin availability token.agreement application initial admitted).1
  have tokenIdentity : token.agreement.binding.server_pin.binding.identity_public_key = pin.binding.identity_public_key := by
    rw [binding, selected.1, receipt.pinEq]
  have bytes : absBytes actualPin.binding.identity_public_key = absBytes pin.binding.identity_public_key :=
    samePin.2.1.symm.trans (congrArg absBytes tokenIdentity)
  have identity : actualPin.binding.identity_public_key = pin.binding.identity_public_key :=
    Subtype.ext ((absBytes_inj_iff _ _).mp bytes)
  exact (RegistrationNativeServerPublicContents.initial control actualPin availability token.agreement application initial admitted).1.trans identity

end BeaconcryptCore.Computational.RegistrationNativeMatchedServerPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMatchedServerPin.initial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMatchedServerPin.initial_identity
