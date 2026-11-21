-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs

/-! Entry-stage properties of the selected actual public Rust bodies. An unavailable Beacon state returns before any decoder, signer or RNG request; a failed Init decoder returns before recomputing the Server pin or authenticating. These are equations for the source cohort, rather than assumptions about an independent wrapper model. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterPublicWrapperStages
open PublicWrapperPlatform
open beaconcrypt_public_wrapper

variable [Material] [Platform] [Allocator] [AdapterInitEdPrimitive.Operations]
variable [LocalOperations] [CryptoOperations] [ContainerOperations] [Codecs]
variable [beaconcrypt.ratchet.Operations] [beaconcrypt.auth.Operations]
variable [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations]

omit [Platform] [Allocator] [LocalOperations] [ContainerOperations] [Codecs] [beaconcrypt.ratchet.Operations] in
theorem bundle_unavailable {R E : Type} (random : rand_core.TryCryptoRng R E)
    (before : beacon.Beacon) (rng : R)
    (unavailable : match before.state with
      | .InitSent _ _ _ _ | .Established _ _ _ | .Aborted _ => True
      | .Fresh _ _ _ | .FreshWithCoins _ _ _ _ => False) :
    beacon.Beacon.get_registration_bundle_with_rng random before rng =
      .ok (.None, before, rng) := by
  cases stateEq : before.state <;>
    simp only [stateEq] at unavailable <;>
    simp only [beacon.Beacon.get_registration_bundle_with_rng, stateEq]

omit [Allocator] [ContainerOperations] [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem finish_unavailable (before : beacon.Beacon) (bytes : Slice U8)
    (unavailable : match before.state with
      | .InitSent _ _ _ _ => False
      | .Fresh _ _ _ | .FreshWithCoins _ _ _ _ | .Established _ _ _ | .Aborted _ => True) :
    beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration before bytes =
      .ok (.None, before) := by
  cases stateEq : before.state <;>
    simp only [stateEq] at unavailable <;>
    simp only [beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration, stateEq]

omit [Allocator] [ContainerOperations] [beaconcrypt.ratchet.Operations] [RegistrationWriterPrimitive.Operations] [AdapterWirePrimitive.Operations] in
theorem lookup_decode_none (before : server.Server) (bytes : Slice U8)
    (decode : beaconcrypt_parse.decode_init bytes = .ok .None) :
    server.Server.authenticate_registration_lookup before bytes = .ok .None := by
  simp only [server.Server.authenticate_registration_lookup, decode, bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

end BeaconcryptCore.Refinement.AdapterPublicWrapperStages

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStages.bundle_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStages.bundle_unavailable

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStages.finish_unavailable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStages.finish_unavailable

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicWrapperStages.lookup_decode_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicWrapperStages.lookup_decode_none
