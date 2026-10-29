-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementShared
import BeaconcryptCore.Computational.PqxdhServerAuthExperiment

/-! The typed native public conversion is the existing optional source conversion and width parser. Its successful replies therefore supply the literal source equation used by the selected-DH preparation compiler. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationPublicConversion

open PqxdhBeaconPhase2Preparation (Word32)

def convert (crypto : Pqxdh.Crypto) (key : Word32) : core.option.Option Word32 :=
  match (crypto.xpkConv (absBytes key)).bind PqxdhServerAuthExperiment.toWord32 with
  | none => .None
  | some key => .Some key

def primitive {Auxiliary : Type} (crypto : Pqxdh.Crypto)
    (backend : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)
  | .convertPublic key => pure (convert crypto key)
  | query => backend query

theorem convert_sound (crypto : Pqxdh.Crypto) (key converted : Word32)
    (actual : convert crypto key = .Some converted) :
    crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  cases convertedBytes : crypto.xpkConv (absBytes key) with
  | none => simp only [convert, convertedBytes, Option.bind_none, reduceCtorEq] at actual
  | some bytes =>
      cases parsed : PqxdhServerAuthExperiment.toWord32 bytes with
      | none => simp only [convert, convertedBytes, Option.bind_some, parsed, reduceCtorEq] at actual
      | some word =>
          have same : word = converted := by
            have reply : (.Some word : core.option.Option Word32) = .Some converted := by
              simpa only [convert, convertedBytes, Option.bind_some, parsed] using actual
            injection reply
          subst word
          rw [PqxdhServerAuthExperiment.toWord32_some bytes converted parsed]

theorem query_sound {Auxiliary : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (backend : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (key converted : Word32) (before after : RawCtxSharedPrimitive.SharedState Auxiliary)
    (supported : (.Some converted, after) ∈ support
      ((RegistrationAgreementShared.implementation source (primitive source.crypto backend) (.convertPublic key)).run before)) :
    source.crypto.xpkConv (absBytes key) = some (absBytes converted) := by
  change (.Some converted, after) ∈ support (pure (convert source.crypto key, before) : ProbComp _) at supported
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
  exact convert_sound source.crypto key converted supported.1.symm

end BeaconcryptCore.Computational.RegistrationPublicConversion

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicConversion.convert_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicConversion.convert_sound

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicConversion.query_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicConversion.query_sound
