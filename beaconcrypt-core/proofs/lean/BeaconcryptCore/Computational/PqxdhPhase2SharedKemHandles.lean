import BeaconcryptCore.Computational.PqxdhPhase2KemHandles
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-!
Changing a private KEM handle representation changes only the argument at the original decapsulation callback. Both the native and opaque-shared executions retain their original complete owner type, callback effects and optional outcomes. This is a protocol interface law, with no key equality or security premise.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SharedKemHandles
open PqxdhBeaconPhase2Shared
variable {I D K K' X Response Shared : Type}

def preparation (key : K → K') :
    QueryImpl (Spec I D K X Response Shared) (OracleComp (Spec I D K' X Response Shared))
  | .decode raw => (Spec I D K' X Response Shared).query (.decode raw)
  | .ciphertext response => (Spec I D K' X Response Shared).query (.ciphertext response)
  | .ephemeral response => (Spec I D K' X Response Shared).query (.ephemeral response)
  | .serverIdentity response => (Spec I D K' X Response Shared).query (.serverIdentity response)
  | .publicConversion value => (Spec I D K' X Response Shared).query (.publicConversion value)
  | .privateConversion identity => (Spec I D K' X Response Shared).query (.privateConversion identity)
  | .decapsulate value kem => (Spec I D K' X Response Shared).query (.decapsulate value (key kem))
  | .dhPair pair value => (Spec I D K' X Response Shared).query (.dhPair pair value)
  | .dhIdentity identity value => (Spec I D K' X Response Shared).query (.dhIdentity identity value)
  | .assignedId response => (Spec I D K' X Response Shared).query (.assignedId response)
  | .eraseShared secrets => (Spec I D K' X Response Shared).query (.eraseShared secrets)

def full (key : K → K') :
    QueryImpl (FullSpec I D K X Response Shared) (OracleComp (FullSpec I D K' X Response Shared))
  | .inl query => simulateQ preLift (preparation key query)
  | .inr query => (FullSpec I D K' X Response Shared).query (.inr query)

set_option backward.isDefEq.respectTransparency false in
/-- The same complete native and shared callback contracts hold after translating only the private KEM argument. -/
theorem full_calls {m : Type → Type} [Monad m] [LawfulMonad m]
    (key : K → K') (interpret : Shared → PqxdhBeaconPhase2Preparation.Word32)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D K' X Response) m)
    (handles : QueryImpl (FullSpec I D K' X Response Shared) m)
    (calls : FullCalls interpret native handles) :
    FullCalls interpret (native ∘ₛ PqxdhPhase2KemHandles.native key) (handles ∘ₛ full key) := by
  constructor
  all_goals constructor <;> intros <;> simp only [QueryImpl.compose, PqxdhPhase2KemHandles.native,
    PqxdhPhase2KemHandles.preparation, full, preparation, preLift, simulateQ_spec_query]
  all_goals first
    | exact calls.preparation.decode _
    | exact calls.preparation.ciphertext _
    | exact calls.preparation.ephemeral _
    | exact calls.preparation.serverIdentity _
    | exact calls.preparation.publicConversion _
    | exact calls.preparation.privateConversion _
    | exact calls.preparation.decapsulate _ _
    | exact calls.preparation.dhPair _ _
    | exact calls.preparation.dhIdentity _ _
    | exact calls.preparation.assignedId _
    | exact calls.preparation.eraseShared _
    | exact calls.tail.root _ _ ‹_›
    | exact calls.tail.initial _
    | exact calls.tail.application _
    | exact calls.tail.raw _

end BeaconcryptCore.Computational.PqxdhPhase2SharedKemHandles

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SharedKemHandles.full_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SharedKemHandles.full_calls
