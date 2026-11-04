-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotOrdinal
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
import BeaconcryptCore.Computational.RegistrationNativePairedCompile
/-! The successful-handle projection of the existing opaque observer has an exact one-list state interpreter. This projection retains every original request and reply and makes installation-free source prefixes neutral without exposing material. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
open RegistrationNativePublicFrontend (Spec)
open PqxdhRecordLiftInterface (Role)
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordPartnerSnapshotOrdinal (receiptHandles)
open RegistrationNativePairedSafe (GlobalInstall)
variable {n : Nat} {KemSK A : Type}

def update (role : Role) (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : List Handle) : List Handle :=
  match query with
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId _ _)))))) =>
      if role=.server ∧ @Eq Bool reply true then before++[.peer keyId] else before
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner _ _)))))) =>
      if role=.beacon ∧ @Eq Bool reply true then before++[.owner owner] else before
  | _ => before

def handler (role : Role) : QueryImpl (Spec n KemSK) (StateT (List Handle) (OracleComp (Spec n KemSK))) := fun query before=>
  (fun reply=>(reply,update role query reply before)) <$> (Spec n KemSK).query query

private theorem step (role : Role) (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : RegistrationNativePlatformPublicRecordSlots.State n) :
    receiptHandles role (RegistrationNativePlatformPublicRecordSlots.step query reply before).snapshot=
      update role query reply (receiptHandles role before.snapshot) := by
  rcases query with (prepare|(demand|(publication|environment))|kem)|record
  · rfl
  · rfl
  · rfl
  · rcases environment with coin|capability
    · rfl
    · cases capability with
      | installServer keyId binding kernel | installBeacon owner binding kernel =>
          cases role <;> cases reply <;>
            simp [receiptHandles,RegistrationNativePlatformPublicRecordSlots.step,
              RegistrationNativePlatformPublicRecordSlots.snapshotUpdate,update]
      | _ => rfl
  · rfl
  · rfl

/-- The original slot observer's handle projection is exactly its one-list interpreter on every adaptive source tree. -/
theorem program_source (role : Role) (work : OracleComp (Spec n KemSK) A)
    (before : RegistrationNativePlatformPublicRecordSlots.State n) :
    Prod.map id (fun current=>receiptHandles role current.snapshot) <$>
      RegistrationNativePlatformPublicRecordSlots.program work before =
    (simulateQ (handler role) work).run (receiptHandles role before.snapshot) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    RegistrationNativePlatformPublicRecordSlots.handler (handler role)
    (fun current=>receiptHandles role current.snapshot) _ work before
  intro query current
  simp only [RegistrationNativePlatformPublicRecordSlots.handler,handler,StateT.run,Functor.map_map]
  apply congrArg (fun change=>change <$> ((Spec n KemSK).query query : OracleComp (Spec n KemSK) _))
  funext reply
  change (reply,receiptHandles role (RegistrationNativePlatformPublicRecordSlots.step query reply current).snapshot)=_
  rw [step]

private theorem update_free (role : Role) (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (before : List Handle) (quiet : ¬GlobalInstall (KemSK := KemSK) role query) : update role query reply before=before := by
  rcases query with (prepare|(demand|(publication|environment))|kem)|record
  · rfl
  · rfl
  · rfl
  · rcases environment with coin|capability
    · rfl
    · cases capability with
      | installServer keyId binding kernel => cases role with
        | server => exact False.elim (quiet rfl)
        | beacon => rfl
      | installBeacon owner binding kernel => cases role with
        | server => rfl
        | beacon => exact False.elim (quiet rfl)
      | _ => rfl
  · rfl
  · rfl

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before=(do let result ← work before; next result.1 result.2) := rfl

/-- An actual zero-install source prefix preserves this handle list exactly, without constraining any other query or failure. -/
theorem free (role : Role) (work : OracleComp (Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0) (before : List Handle) :
    (simulateQ (handler role) work).run before=(fun value=>(value,before)) <$> work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
      have head := (isQueryBoundP_query_bind_iff _ _ _ _).mp bounded
      have quiet := head.1.resolve_right (by omega)
      simp only [simulateQ_bind,simulateQ_spec_query,handler,StateT.run,bind_apply,bind_map_left,map_bind]
      apply bind_congr
      intro reply
      rw [update_free role query reply before quiet]
      exact ih reply (by simpa only [Nat.zero_sub,ite_self] using head.2 reply) before

/-- The actual effect embedding retains a zero role-install bill and hence the original successful-handle list. -/
theorem effects_free (role : Role) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role) 0) (before : List Handle) :
    (simulateQ (handler role) (simulateQ (RegistrationNativePairedCompile.effects (KemSK := KemSK)) work)).run before =
      (fun value=>(value,before)) <$> simulateQ RegistrationNativePairedCompile.effects work := by
  apply free
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  rcases query with coin|capability
  · simp [RegistrationNativePairedCompile.effects,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,
      RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,isQueryBoundP_query_iff]
  · cases capability <;> cases role <;>
      simp [RegistrationNativePairedCompile.effects,GlobalInstall,RegistrationNativeSecretWordAtomInstallCaps.Install,
        RegistrationNativeSecretWordAtomInstallCaps.InstallEnv,isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.effects_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles.effects_free
