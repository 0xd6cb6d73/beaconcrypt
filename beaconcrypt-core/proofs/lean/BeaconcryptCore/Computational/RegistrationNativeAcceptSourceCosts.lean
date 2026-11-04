-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts
import BeaconcryptCore.Computational.RegistrationNativePrimitiveCosts

/-! The actual authenticated Server collector has one scalar draw and one indexed encapsulation site. The weighted source bill retains all thirteen callback positions and their rejected continuations, while charging the precise two nonzero classes. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeAcceptSourceCosts
open PqxdhRecordLiftInterface (EffectKind)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_indicator weighted_add)
open RegistrationNativePrimitiveCosts (coinCost)
open PqxdhServerAuthSourceCosts (serverClass collect_callbacks collectCap)
variable {Reader E Shared : Type}

def bill (qKem : Nat) : PqxdhServerRootPreparation.Query Reader E → EffectKind → Nat
  | .generate, kind => coinCost 32 kind
  | .encapsulate _, kind => coinCost qKem kind
  | _, _ => 0

theorem collector_bound (verified : PqxdhServerRootPreparation.Verified Reader) (qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill qKem query kind)
      (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified)
      (coinCost (32 + qKem) kind) := by
  have generated := weighted_indicator (fun query => serverClass query = .generate) (coinCost 32 kind)
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified) 1
    (collect_callbacks verified .generate)
  have encapsulated := weighted_indicator (fun query => serverClass query = .encapsulate) (coinCost qKem kind)
    (PqxdhServerRootPreparation.collectVerified (E := E) (Shared := Shared) verified) 1
    (collect_callbacks verified .encapsulate)
  have combined := weighted_add _ _ _ _ _ generated encapsulated
  convert combined using 1
  · funext query
    cases query <;> cases kind <;> simp [bill, serverClass, coinCost]
  · cases kind <;> simp [coinCost]

end BeaconcryptCore.Computational.RegistrationNativeAcceptSourceCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeAcceptSourceCosts.collector_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeAcceptSourceCosts.collector_bound
