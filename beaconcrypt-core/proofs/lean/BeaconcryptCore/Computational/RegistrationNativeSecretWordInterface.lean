-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemInterface

/-! The symbolic mixed frontend has the same native preparation, material/common, routed KEM and record surfaces. Only references and shared-secret replies carry opaque words. Actual record, signing, encoding, World effects and public control types remain the original ones. These definitions introduce no source equivalence or independence assumption. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface
open RegistrationNativeSecretWordMessage (Message PrepareSpec)
open RegistrationNativeSecretWordKemInterface (WordPoolSpec WordEncapSpec Routed)
open PqxdhRecordLiftInterface (EnvEffects)
variable {n : Nat} {KemSK Value : Type}

abbrev WordPairedPublicSpec (n : Nat) := (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) +
  RegistrationNativePairedServerService.Common n
abbrev LocalKem (KemSK : Type) := RegistrationNativeKemInterface.OtherSpec + (WordPoolSpec KemSK + WordEncapSpec)
abbrev LocalSpec (n : Nat) (KemSK : Type) := PrepareSpec + (WordPairedPublicSpec n + LocalKem KemSK)
abbrev RoutedLocalSpec (n : Nat) (KemSK : Type) := PrepareSpec + (WordPairedPublicSpec n + Routed KemSK)
abbrev Spec (n : Nat) (KemSK : Type) := RoutedLocalSpec n KemSK + PqxdhRecordLiftInterface.RecordSpec .O

def effect (query : (EnvEffects n).Domain) : OracleComp (LocalSpec n KemSK) ((EnvEffects n).Range query) :=
  (LocalSpec n KemSK).query (.inr (.inl (.inr (.inr query))))

def prepare (message : Message) : OracleComp (LocalSpec n KemSK) (Option Message) :=
  (LocalSpec n KemSK).query (.inl message)

def demand (message : Message) : OracleComp (LocalSpec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)) :=
  (LocalSpec n KemSK).query (.inr (.inl (.inl message)))

def common : QueryImpl (RegistrationNativePairedServerService.Common n) (OracleComp (LocalSpec n KemSK)) :=
  fun query => (LocalSpec n KemSK).query (.inr (.inl (.inr query)))

def paired : QueryImpl (WordPairedPublicSpec n) (OracleComp (LocalSpec n KemSK)) :=
  fun query => (LocalSpec n KemSK).query (.inr (.inl query))

def localKem : QueryImpl (LocalKem KemSK) (OracleComp (LocalSpec n KemSK)) :=
  fun query => (LocalSpec n KemSK).query (.inr (.inr query))

def route (selected : Bool) : QueryImpl (LocalKem KemSK) (OracleComp (Routed KemSK))
  | .inl query => (Routed KemSK).query (.inl (.inl query))
  | .inr (.inl query) => (Routed KemSK).query (.inr (.inl query))
  | .inr (.inr key) => if selected then (Routed KemSK).query (.inr (.inr key))
      else (Routed KemSK).query (.inl (.inr key))

def routedKem : QueryImpl (Routed KemSK) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl (.inr (.inr query)))

def liftLocal (selected : Bool) : QueryImpl (LocalSpec n KemSK) (OracleComp (Spec n KemSK))
  | .inl message => (Spec n KemSK).query (.inl (.inl message))
  | .inr (.inl query) => (Spec n KemSK).query (.inl (.inr (.inl query)))
  | .inr (.inr query) => simulateQ routedKem (route selected query)

/-- Marking a parsed accept changes only the branch of its encapsulation request; every private pool operation remains indexed. -/
theorem route_pool (selected : Bool) (query : (WordPoolSpec KemSK).Domain) :
    route (KemSK := KemSK) selected (.inr (.inl query)) =
      ((Routed KemSK).query (.inr (.inl query)) : OracleComp (Routed KemSK) _) := rfl

/-- Ordinary native common work is forwarded without changing any record, publication, signing or encoding callback. -/
theorem lift_common (selected : Bool) (query : (RegistrationNativePairedServerService.Common n).Domain) :
    simulateQ (liftLocal selected) (common (KemSK := KemSK) query) =
      (Spec n KemSK).query (.inl (.inr (.inl (.inr query)))) := by
  simp only [common, simulateQ_spec_query, liftLocal]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface.route_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface.route_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface.lift_common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterface.lift_common
