-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementRoot

/-! The server's real static-DH implementation and its executable reference prefix use the actual native agreement callbacks. Typed constructors introduce no extra primitive effects, and the static-call visit is performed exactly once. All remaining native callback effects, including generated secret-handle state, are retained in the backend. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationAgreementInterpreter

open RegistrationAgreementExecutor
open PqxdhJointIdentity
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationAgreementRoot (callbacks nativeOption option)

def sourceImpl {m : Type → Type} [Monad m] (joint : Primitives) (seed : IdentitySeed)
    (backend : QueryImpl Spec m) (visit : Word32 → m Unit) : QueryImpl Spec m
  | .dh request => match request.secret_role with
      | .LocalIdentity => do
          let _ ← visit request.public_key
          pure (nativeOption ((joint.staticDh seed (PqxdhPhase2GapDhSource.peer request.public_key)).map
            PqxdhRootTableInitialization.rootArray))
      | _ => backend (.dh request)
  | request => backend request

def prepImpl {m : Type → Type} [Monad m] (backend : QueryImpl Spec m) :
    QueryImpl (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit) m
  | .decode raw => simulateQ backend (callbacks (.decode raw))
  | .identity packet => simulateQ backend (callbacks (.identity packet))
  | .identityPoint key => simulateQ backend (callbacks (.identityPoint key))
  | .pqField packet => simulateQ backend (callbacks (.pqField packet))
  | .preField packet => simulateQ backend (callbacks (.preField packet))
  | .oneField packet => simulateQ backend (callbacks (.oneField packet))
  | .verify key signed => simulateQ backend (callbacks (.verify key signed))
  | .registrationStatus rid => simulateQ backend (callbacks (.registrationStatus rid))
  | .reserveRegistration => simulateQ backend (callbacks .reserveRegistration)
  | .parseDh point => simulateQ backend (callbacks (.parseDh point))
  | .generate => simulateQ backend (callbacks .generate)
  | .parseKem key => simulateQ backend (callbacks (.parseKem key))
  | .encapsulate key => simulateQ backend (callbacks (.encapsulate key))
  | .publicConversion key => simulateQ backend (callbacks (.publicConversion key))
  | .privateConversion => simulateQ backend (callbacks .privateConversion)
  | .staticDh _ => pure none
  | .ephemeralDh secret key => simulateQ backend (callbacks (.ephemeralDh secret key))

private theorem option_roundtrip {Value : Type} (value : Option Value) : option (nativeOption value) = value := by
  cases value <;> rfl

theorem callbacks_source {m : Type → Type} [Monad m] [LawfulMonad m]
    (joint : Primitives) (seed : IdentitySeed) (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Word32).Domain) :
    simulateQ (sourceImpl joint seed backend visit) (callbacks query) =
      PqxdhServerStaticDhSource.nativeImpl joint seed (prepImpl backend) visit query := by
  cases query <;> simp only [callbacks, simulateQ_pure, simulateQ_map, simulateQ_spec_query,
    sourceImpl, PqxdhServerStaticDhSource.nativeImpl, prepImpl, map_bind, map_pure,
    option_roundtrip]

theorem prefix_source {m : Type → Type} [Monad m] [LawfulMonad m] {Result : Type}
    (joint : Primitives) (seed : IdentitySeed) (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (work : OracleComp (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Word32) Result) :
    simulateQ (sourceImpl joint seed backend visit) (simulateQ callbacks work) =
      simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed (prepImpl backend) visit) work := by
  rw [← QueryImpl.simulateQ_compose]
  have equal : (sourceImpl joint seed backend visit) ∘ₛ callbacks =
      PqxdhServerStaticDhSource.nativeImpl joint seed (prepImpl backend) visit := by
    funext query
    exact callbacks_source joint seed backend visit query
  rw [equal]

theorem server_source {m : Type → Type} [Monad m] [LawfulMonad m]
    (joint : Primitives) (seed : IdentitySeed) (backend : QueryImpl Spec m) (visit : Word32 → m Unit)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    simulateQ (sourceImpl joint seed backend visit) (server control .Fresh authenticated) = (do
      let input ← (simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed (prepImpl backend) visit)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))
      match input with
      | none => pure (.ok (.Rejected .None))
      | some input =>
          simulateQ (sourceImpl joint seed backend visit) (RegistrationAgreementRoot.finish control authenticated input)) := by
  rw [RegistrationAgreementRoot.server_normalized control packet authenticated]
  simp only [RegistrationAgreementRoot.normalized, simulateQ_bind, prefix_source]
  congr 1
  funext input
  cases input <;> simp only [simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationAgreementInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementInterpreter.callbacks_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementInterpreter.callbacks_source

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementInterpreter.prefix_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementInterpreter.prefix_source

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementInterpreter.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementInterpreter.server_source
