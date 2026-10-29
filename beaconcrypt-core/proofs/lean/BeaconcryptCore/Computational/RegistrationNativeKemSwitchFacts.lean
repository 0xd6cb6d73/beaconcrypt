-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource

/-! The open typed candidate provider retains the actual ambient operation and all private phase/table coordinates. Its literal first matching getter samples the exact candidate supplied to the SDK. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemSwitchSource (Phase source)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Every actual ambient callback is independent of the private KEM phase and retains the complete private table. -/
theorem ambient_run (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (query : ambient.Domain) (before : Auxiliary) (privateState : PqxdhDynamicKemRouter.State KemSK) (phase : Phase) :
    (((source baseImpl kem other selected pairs publicKey real (.inl query)).run).run ((before, privateState), phase)) =
      (fun result => (some result.1, ((result.2, privateState), phase))) <$> (other query).run before := by
  cases phase <;> simp only [source, RegistrationNativeKemSwitchSource.post,
    RegistrationNativeKemSwitchSource.carry, RegistrationNativeKemGame.stopped,
    RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
    OptionT.run_mk, StateT.run, Functor.map_map]

/-- A first getter at the genuine reserved key receives the exact sampled challenge ciphertext and candidate, without requiring that its owner is already created. -/
theorem matching_getter (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (before : RegistrationNativeKemGame.State Auxiliary KemSK) :
    (((source baseImpl kem other selected pairs publicKey real (.inr (.inr publicKey))).run).run (before, none)) =
      (do let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
          let uniform ← $ᵗ MlKemSharedSecret
          pure (some (pair.1, if real then pair.2 else uniform),
            (before, some (pair.1, if real then pair.2 else uniform)))) := by
  simp only [source, OptionT.run_mk, StateT.run, ite_true, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts.ambient_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts.ambient_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts.matching_getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchFacts.matching_getter
