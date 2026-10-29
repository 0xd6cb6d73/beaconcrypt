-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource

/-! A total online reserved provider keeps the actual live KEM pool and first-getter phase, without any Server seed or selected prekey scalar. Its per-query projection follows the existing stopped online source at every affordable non-revealing query, including complete/no-get and mismatched first getters. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemSwitchSource (Phase Switched)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemPoolSource (IsReveal)
variable {κ ι KemSK Auxiliary : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

abbrev State (Auxiliary KemSK : Type) := (Auxiliary × PqxdhLiveKemBirth.Pool KemSK) × Phase

def project (pairs : List (MlKem768PublicKey × KemSK)) (before : Switched Auxiliary KemSK) : State Auxiliary KemSK :=
  (RegistrationNativeKemPoolSource.project pairs before.1, before.2)

def carry {Reply : Type} (phase : Phase) (result : Reply × (Auxiliary × PqxdhLiveKemBirth.Pool KemSK)) : Reply × State Auxiliary KemSK :=
  (result.1, (result.2, phase))

noncomputable def source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) :
    QueryImpl (Spec ambient KemSK) (StateT (State Auxiliary KemSK) ProbComp) := fun query before =>
  match before.2 with
  | some phase => carry before.2 <$> (RegistrationNativeKemCandidateReserved.reserved baseImpl kem other selected pairs phase.1 phase.2 query).run before.1
  | none => match query with
    | .inr (.inr key) => do
        let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps publicKey)
        let uniform ← $ᵗ MlKemSharedSecret
        let candidate := if real then pair.2 else uniform
        let reply ← if key = publicKey then pure (pair.1, candidate)
          else simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key)
        pure (reply, (before.1, some (pair.1, candidate)))
    | query => carry none <$> (RegistrationNativeKemReservation.reserved baseImpl kem other pairs query).run before.1

/-- The affordable actual online provider is exactly the total live-pool provider after dropping only its private routing monitor. -/
theorem step_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (query : (Spec ambient KemSK).Domain) (before : Switched Auxiliary KemSK)
    (noReveal : ¬IsReveal query) (room : before.1.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real query).run).run before) =
      (fun result => (some result.1, result.2)) <$>
        (source baseImpl kem other selected pairs publicKey real query).run (project pairs before) := by
  cases phaseRun : before.2 with
  | some phase =>
      have law := congrArg (fun distribution => (fun result => (result.1, (result.2, some phase))) <$>
        distribution) (RegistrationNativeKemCandidateReserved.step_source baseImpl kem other selected pairs phase.1 phase.2 query before.1 noReveal room)
      simpa only [source, RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.post,
        RegistrationNativeKemSwitchSource.carry, OptionT.run_mk, StateT.run, Functor.map_map, Prod.map_def, id_eq,
        project, carry] using law
  | none =>
      rcases query with query | (query | key)
      · have law := congrArg (fun distribution => (fun result => (result.1, (result.2, (none : Phase)))) <$>
          distribution) (RegistrationNativeKemPoolSource.step_source baseImpl kem other selected pairs (.inl query) before.1 noReveal room)
        simpa only [source, RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.carry,
          OptionT.run_mk, StateT.run, Functor.map_map, Prod.map_def, id_eq, project, carry] using law
      · have law := congrArg (fun distribution => (fun result => (result.1, (result.2, (none : Phase)))) <$>
          distribution) (RegistrationNativeKemPoolSource.step_source baseImpl kem other selected pairs (.inr (.inl query)) before.1 noReveal room)
        simpa only [source, RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.carry,
          OptionT.run_mk, StateT.run, Functor.map_map, Prod.map_def, id_eq, project, carry] using law
      · simp only [source, RegistrationNativeKemSwitchSource.source, phaseRun, OptionT.run_mk, StateT.run,
          map_bind, project, Prod.map_def, id_eq]
        by_cases matching : key = publicKey <;>
          simp only [matching, ite_true, ite_false, map_bind, map_pure, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved.step_source
