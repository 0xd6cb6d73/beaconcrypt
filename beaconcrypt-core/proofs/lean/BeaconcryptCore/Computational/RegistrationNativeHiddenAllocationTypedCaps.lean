-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationPublicCaps
import BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild
import BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps

/-! Every actual typed native operation except creation is physically allocation-free. This combines the actual finite Server and Beacon callback footprints and keeps terminal malformed-finish and all optional failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationTypedCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenAllocationCore (Allowed mapped)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

private theorem bind_apply {A B : Type}
    (work : RegistrationNativePublicFrontend.M n KemSK source A)
    (next : A → RegistrationNativePublicFrontend.M n KemSK source B)
    (before : RegistrationNativePublicFrontend.State source) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl

private theorem get_apply (before : RegistrationNativePublicFrontend.State source) :
    (get : RegistrationNativePublicFrontend.M n KemSK source (RegistrationNativePublicFrontend.State source)) before =
      pure (before, before) := rfl

private theorem modify_apply (change : RegistrationNativePublicFrontend.State source → RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicFrontend.State source) :
    (modify change : RegistrationNativePublicFrontend.M n KemSK source Unit) before = pure ((), change before) := rfl

def NonCreate : TypedSpec.Domain → Prop
  | .inr (.create _ _ _) => False
  | _ => True

/-- Every non-creation command in the literal public frontend has no physical owner append on any oracle branch. -/
theorem typed (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : TypedSpec.Domain) (before : RegistrationNativePublicFrontend.State source) (quiet : NonCreate query) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before) Allowed := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp]
      exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
  | inr query => cases query with
    | create edPin mlPin keyId => exact quiet.elim
    | bundle index =>
        exact RegistrationNativeHiddenAllocationPublicCaps.native selectedOwner publicPrekey _ before
          (RegistrationNativeHiddenBeaconAllocationCaps.bundle_safe setup wire index)
    | finish index packet => exact RegistrationNativeHiddenBeaconFinishAllocationCaps.frontend_safe setup source index packet before
    | accept packet =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run, bind_apply, get_apply, pure_bind, modify_apply]
        exact RegistrationNativeHiddenServerAllocationCaps.accept_frontend_safe setup checks source.verify _ packet _
    | build handle application => exact RegistrationNativeHiddenServerAllocationCapsBuild.build_frontend_safe setup.source wire checks sign handle application before
    | hmac key bytes => trivial
    | hash bytes =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp]
        exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
    | serverSend keyId plaintext | serverRaw raw =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.record, StateT.run]
        exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | beaconSend index plaintext | beaconRaw index raw =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.record, StateT.run]
        split
        · trivial
        · exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationTypedCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationTypedCaps.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationTypedCaps.typed
