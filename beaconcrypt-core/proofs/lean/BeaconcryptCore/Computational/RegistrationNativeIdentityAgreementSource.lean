-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementShape
import BeaconcryptCore.Computational.RegistrationNativeIdentityReadonlySource
import BeaconcryptCore.Computational.RegistrationNativeIdentityDhSource

/-! The entire native Beacon agreement controller uses the same source primitives with its generated identity behind an indexed joint service. Functional converter width follows from the concrete source representation; local static DH uses its private stored seed, while all other callbacks retain the original ordinary programs and request logs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open RegistrationNativeIdentitySourceSimulation
open RegistrationNativeIdentityFrontend (Owner)
open RegistrationNativeIdentityAgreementShape (Other)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {source : RegistrationNativeMldsa.Source}

theorem ordinary_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) (ordinary : Other query) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime query)
      (RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime query) := by
  rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary,
    RegistrationNativeIdentityAgreementShape.original_other setup owner seed RegistrationNativeIdentityFrontend.dummyIdentity oneTime query ordinary]
  let current := RegistrationNativeIdentityFrontend.restore RegistrationNativeIdentityFrontend.dummyIdentity owner
  have lifted := RegistrationBeaconReferenceNativeCallbacks.owned_query (n := n) (Auxiliary := Auxiliary) setup
    current.prekeyScalar (RegistrationBeaconReferenceCompiler.eraseOwner current) oneTime query
  rw [RegistrationBeaconReferenceCompiler.restore_erase current] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityReadonlySource.source_lift setup checks representation created seeds _

theorem ordinary_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Request) (ordinary : Other query) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime query) := by
  rw [RegistrationNativeIdentityAgreementShape.exposed_other setup owner oneTime query ordinary]
  let current := RegistrationNativeIdentityFrontend.restore RegistrationNativeIdentityFrontend.dummyIdentity owner
  have lifted := RegistrationBeaconReferenceNativeCallbacks.owned_query (n := n) (Auxiliary := Auxiliary) setup
    current.prekeyScalar (RegistrationBeaconReferenceCompiler.eraseOwner current) oneTime query
  rw [RegistrationBeaconReferenceCompiler.restore_erase current] at lifted
  rw [lifted]
  exact RegistrationNativeIdentityReadonlySource.keeps_lift setup checks representation created _

theorem original_conversion (setup : Setup base KemSK)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup
      (RegistrationNativeIdentityFrontend.restore seed owner) oneTime (.convertSecret .LocalIdentity) = pure true := by
  simp only [RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
    RegistrationNativeKemInterface.other, simulateQ_spec_query, RegistrationNativeKemBackend.beaconOther,
    RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
    RegistrationBeaconRoleBackend.localBackend, RegistrationNativeIdentityFrontend.restore,
    StateT.run, map_pure, StateT.monad_pure_def, RegistrationNativeBeaconFrontend.sample, simulateQ_pure]
  rw [RegistrationServerRoleBackend.selected_conversion setup representation seed]

theorem conversion_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime (.convertSecret .LocalIdentity))
      (RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime (.convertSecret .LocalIdentity)) := by
  simp only [RegistrationNativeIdentityFrontend.agreement, RegistrationNativeBeaconFrontend.agreement,
    RegistrationNativeIdentityFrontend.agreementCore, RegistrationNativeBeaconFrontend.agreementCore]
  apply related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativeIdentityCommonSource.update_source setup checks representation created seeds _)
    (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
  intro _
  rw [original_conversion setup representation owner seed oneTime]
  exact related_pure setup checks representation created seeds true

theorem local_dh_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (peer : PqxdhBeaconPhase2Preparation.Word32) (found : seeds[owner.identity.handle]? = some seed) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime (.dh ⟨.LocalIdentity, peer⟩))
      (RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime (.dh ⟨.LocalIdentity, peer⟩)) := by
  simp only [RegistrationNativeIdentityFrontend.agreement, RegistrationNativeBeaconFrontend.agreement,
    RegistrationNativeIdentityFrontend.agreementCore, RegistrationNativeBeaconFrontend.agreementCore]
  exact related_bind setup checks representation created seeds _ _ _ _
    (RegistrationNativeIdentityCommonSource.update_source setup checks representation created seeds _)
    (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
    (fun _ => RegistrationNativeIdentityDhSource.local_dh_source setup checks representation created seeds owner seed oneTime peer found)

/-- Every actual native agreement request has the original seed-bearing source reply and effects, with local identity operations supplied only by the indexed service. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed) (query : RegistrationAgreementExecutor.Request) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime query)
      (RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime query) := by
  classical
  by_cases ordinary : Other query
  · exact ordinary_source setup checks representation created seeds owner seed oneTime query ordinary
  · cases query with
    | convertSecret role =>
        change ¬ (role ≠ .LocalIdentity) at ordinary
        have same : role = .LocalIdentity := Classical.not_not.mp ordinary
        subst role
        exact conversion_source setup checks representation created seeds owner seed oneTime
    | dh request =>
        change ¬ (request.secret_role ≠ .LocalIdentity) at ordinary
        have same : request.secret_role = .LocalIdentity := Classical.not_not.mp ordinary
        cases request with
        | mk role peer =>
            change role = .LocalIdentity at same
            subst role
            exact local_dh_source setup checks representation created seeds owner seed oneTime peer found
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request => exact False.elim (ordinary trivial)

theorem query_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (RegistrationNativeIdentityFrontend.agreement setup owner oneTime query) := by
  classical
  by_cases ordinary : Other query
  · exact ordinary_keeps setup checks representation created owner oneTime query ordinary
  · cases query with
    | convertSecret role =>
        change ¬ (role ≠ .LocalIdentity) at ordinary
        have same : role = .LocalIdentity := Classical.not_not.mp ordinary
        subst role
        exact keeps_bind setup checks representation created _ _
          (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
          (fun _ => keeps_pure setup checks representation created true)
    | dh request =>
        change ¬ (request.secret_role ≠ .LocalIdentity) at ordinary
        have same : request.secret_role = .LocalIdentity := Classical.not_not.mp ordinary
        cases request with
        | mk role peer =>
            change role = .LocalIdentity at same
            subst role
            exact keeps_bind setup checks representation created _ _
              (RegistrationNativeIdentityCommonSource.update_keeps setup checks representation created _)
              (fun _ => RegistrationNativeIdentityDhSource.service_keeps setup checks representation created owner.identity peer)
    | convertPublic key | generate role | encapsulate key | decapsulate ciphertext | root request => exact False.elim (ordinary trivial)

theorem program_source (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (seeds : List IdentitySeed)
    (owner : Owner source) (seed : IdentitySeed) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : seeds[owner.identity.handle]? = some seed) (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    Related (n := n) (Auxiliary := Auxiliary) setup checks representation created seeds
      (simulateQ (RegistrationNativeIdentityFrontend.agreement setup owner oneTime) work)
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup (RegistrationNativeIdentityFrontend.restore seed owner) oneTime) work) :=
  related_program setup checks representation created seeds _ _
    (query_source setup checks representation created seeds owner seed oneTime found)
    (query_keeps setup checks representation created owner oneTime) work

theorem program_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    Keeps (n := n) (Auxiliary := Auxiliary) setup checks representation created
      (simulateQ (RegistrationNativeIdentityFrontend.agreement setup owner oneTime) work) :=
  keeps_program setup checks representation created _ (query_keeps setup checks representation created owner oneTime) work

end BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.ordinary_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.ordinary_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.ordinary_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.original_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.original_conversion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.conversion_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.conversion_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.local_dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.local_dh_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.query_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityAgreementSource.program_keeps
