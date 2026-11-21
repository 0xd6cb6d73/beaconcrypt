-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationPublicConversion
import BeaconcryptCore.Computational.RegistrationBeaconPreparationInterpreter

/-! The selected-DH root address uses the public conversion derived from the actual reached source prefix and pinned Server identity. Its callback law is the existing functional source conversion contract, and the concrete typed source adapter discharges that law. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationBeaconConversion

open PqxdhJointIdentity PqxdhJointGapDh
open PqxdhBeaconPhase2Preparation (Word32)

def backend {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :=
  RegistrationAgreementShared.implementation source (RegistrationPublicConversion.primitive source.crypto primitive)

theorem aux_conversion {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (authenticated : registration.AuthenticatedResponse) (key converted : Word32)
    (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : (some converted, after) ∈ support
      ((RegistrationBeaconRootInterpreter.auxImpl (backend source primitive) authenticated (.publicConversion key)).run before)) :
    source.crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  change (some converted, after) ∈ support
    (pure (RegistrationAgreementRoot.option (RegistrationPublicConversion.convert source.crypto key), before) : ProbComp _) at supported
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  have actual := supported.1.symm
  cases reply : RegistrationPublicConversion.convert source.crypto key with
  | none => simp only [reply, RegistrationAgreementRoot.option, reduceCtorEq] at actual
  | some word =>
      simp only [reply, RegistrationAgreementRoot.option] at actual
      have same : word = converted := Option.some.inj actual
      subst word
      exact RegistrationPublicConversion.convert_sound source.crypto key converted reply

variable (completedBinding : session.CompletedRegistrationBinding)

theorem admitted_server (control : pqxdh.BeaconInitSent)
    (collected : PqxdhPhase2GapDhSource.Inputs registration.AuthenticatedResponse)
    (metadata : PqxdhBeaconPhase2Shared.Metadata)
    (accepted : PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control collected = some metadata) :
    absBytes collected.server = absBytes control.expected_server_binding.identity_public_key := by
  classical
  by_cases equal : absBytes control.expected_server_binding.identity_public_key = absBytes collected.server
  · exact equal.symm
  · simp only [PqxdhPhase2DhMetadata.admitted, equal, ↓reduceIte, reduceCtorEq] at accepted

theorem collected_conversion {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring crypto joint secretOfSeed)
    (seed : IdentitySeed)
    (aux : QueryImpl RegistrationBeaconRootInterpreter.AuxSpec (StateT Auxiliary ProbComp))
    (conversion : ∀ key before converted after, (some converted, after) ∈ support
      ((aux (.publicConversion key)).run before) → crypto.xpkConv (absBytes key) = some (absBytes converted))
    (visit : Word32 → StateT Auxiliary ProbComp Unit) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = (joint.publicKeys seed).ed25519.toList)
    (before after : Auxiliary) (collected : PqxdhPhase2GapDhSource.Inputs registration.AuthenticatedResponse)
    (metadata : PqxdhBeaconPhase2Shared.Metadata)
    (supported : (some collected, after) ∈ support
      ((simulateQ (PqxdhPhase2GapDhSource.prefixImpl domain aux visit)
        (PqxdhPhase2GapDhSource.collect () () () [])).run before))
    (accepted : PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control collected = some metadata) :
    PqxdhPhase2GapDhSource.peer collected.serverConverted = (joint.publicKeys seed).convertedX25519 := by
  have actual := PqxdhPhase2GapDhSource.collect_conversion domain crypto aux conversion visit
    () () () [] before after collected supported
  rw [admitted_server (completedBinding := completedBinding) control collected metadata accepted, pin] at actual
  have expected := PqxdhJointIdentity.jointPublic_conversion crypto joint secretOfSeed wiring seed
  rw [expected] at actual
  apply List.Vector.toList_injective
  exact (Option.some.inj actual).symm

theorem reached_conversion {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (joint : Primitives) (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring crypto joint secretOfSeed)
    (seed : IdentitySeed)
    (aux : QueryImpl RegistrationBeaconRootInterpreter.AuxSpec (StateT Auxiliary ProbComp))
    (conversion : ∀ key before converted after, (some converted, after) ∈ support
      ((aux (.publicConversion key)).run before) → crypto.xpkConv (absBytes key) = some (absBytes converted))
    (visit : Word32 → StateT Auxiliary ProbComp Unit) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = (joint.publicKeys seed).ed25519.toList)
    (before after : Auxiliary) (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (supported : (some pending, after) ∈ support
      ((simulateQ (PqxdhPhase2GapDhSource.prefixImpl domain aux visit)
        (PqxdhPhase2DhMetadata.prepare (completedBinding := completedBinding) control () () () [])).run before)) :
    PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519 := by
  simp only [PqxdhPhase2DhMetadata.prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨collected, middle⟩, first, last⟩ := supported
  cases collected with
  | none => simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
      Option.bind_none, Option.some_ne_none, false_and] at last
  | some collected =>
      cases accepted : PqxdhPhase2DhMetadata.admitted (completedBinding := completedBinding) control collected with
      | none => simp only [accepted, Option.map_none, Option.bind_some, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at last
      | some metadata =>
          simp only [accepted, Option.map_some, Option.bind_some, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at last
          have pendingEq : (⟨collected, metadata⟩ : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse) = pending := last.1.symm
          subst pending
          exact collected_conversion (completedBinding := completedBinding) crypto joint dh domain secretOfSeed wiring seed aux conversion visit control
            pin before middle collected metadata first accepted

end BeaconcryptCore.Computational.RegistrationBeaconConversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconConversion.aux_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconConversion.aux_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconConversion.admitted_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconConversion.admitted_server

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconConversion.collected_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconConversion.collected_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconConversion.reached_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconConversion.reached_conversion
