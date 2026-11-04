-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinish

/-! The corrected platform finish retains the same actual pinned-response, agreement and first-record cuts, then copies the application and installs the source assigned identifier. Every cut is derived from support of the same complete execution; no partner or successful-install premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt
open RegistrationNativePlatformBeaconFinish (afterAuthentication afterAuthenticationWith install_exact)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (BeaconShell)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def consumed (before : Local n KemSK source) (index : Nat) (aborted : pqxdh.BeaconAborted) : Local n KemSK source :=
  (match before.1[index]? with
    | none => before.1
    | some owner => before.1.set index { owner with phase := .aborted aborted }, before.2)

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem finish_eq (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    RegistrationNativePlatformBeaconFinish.finish (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source wire index packet = (do
      let owners ← get
      match owners[index]? with
      | none => pure (.ok none)
      | some owner => match owner.phase with
        | .initSent pending oneTime => do
          match pending.aborted_state with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok aborted => do
            updatePhase index (.aborted aborted)
            let authenticated ← simulateQ (authentication setup source)
              (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))
            match authenticated with
            | .fail error => abort owner *> pure (.fail error)
            | .div => abort owner *> pure .div
            | .ok (.Err _) => abort owner *> pure (.ok none)
            | .ok (.Ok accepted) => afterAuthentication setup wire index owner oneTime accepted
        | _ => pure (.ok none)) := rfl

private theorem lower_get (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : Local n KemSK source) :
    (lower setup checks representation created (get : M n KemSK source RegistrationServerRoleBackend.State (State source))).run before =
      pure (before.1, before) := by
  simp only [lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_consume (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (before : Local n KemSK source)
    (index : Nat) (aborted : pqxdh.BeaconAborted) :
    (lower setup checks representation created (updatePhase index (.aborted aborted))).run before =
      pure ((), consumed before index aborted) := by
  simp only [lower, updatePhase, StateT.run, state_modify_apply, state_pure_apply, simulateQ_pure, map_pure, consumed]
  rfl

private theorem terminal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (outcome : RustM (Option Pqxdh.Bytes)) (before after : Local n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created (work *> pure outcome)).run before)) :
    .ok (some application) = outcome := by
  rw [seqRight_eq_bind, lower_bind] at supported
  rw [lower_pure, StateT.run_bind] at supported
  simp only [StateT.run_pure, bind_pure_comp, support_map] at supported
  obtain ⟨result, _possible, same⟩ := supported
  exact (congrArg Prod.fst same).symm

attribute [local irreducible] afterAuthentication authentication RegistrationResponseExecutor.begin abort

/-- Successful actual completion has a same-run accepted response cut and the literal continuation to its original returned plaintext. -/
theorem cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before)) :
    ∃ owner pending oneTime aborted accepted middle,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ pending.aborted_state = .ok aborted ∧
      (.ok (.Ok accepted), middle) ∈ support
        ((lower setup checks representation created
          (simulateQ (authentication setup source)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))).run
              (consumed before index aborted)) ∧
      (.ok (some application), after) ∈ support
        ((lower setup checks representation created
          (afterAuthentication setup wire index owner oneTime accepted)).run middle) := by
  rw [finish_eq, lower_bind, StateT.run_bind, lower_get, pure_bind] at supported
  cases selected : before.1[index]? with
  | none =>
      simp only [selected, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | some owner =>
      simp only [selected] at supported
      cases phase : owner.phase with
      | fresh | freshWithCoins _ | established _ | aborted _ =>
          simp only [phase, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
      | initSent pending oneTime =>
          simp only [phase] at supported
          cases moved : pending.aborted_state with
          | fail error | div =>
              simp only [moved, lower_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              cases supported
          | ok aborted =>
              simp only [moved, lower_bind, StateT.run_bind, lower_consume, pure_bind, mem_support_bind_iff] at supported
              obtain ⟨middle, called, continued⟩ := supported
              rcases middle with ⟨reply, middle⟩
              cases reply with
              | fail error | div =>
                  have impossible := terminal setup checks representation created (abort owner) _ middle after application continued
                  cases impossible
              | ok result => cases result with
                | Err aborted =>
                    have impossible := terminal setup checks representation created (abort owner) _ middle after application continued
                    cases impossible
                | Ok accepted => exact ⟨owner, pending, oneTime, aborted, accepted, middle, rfl, phase, moved, called, continued⟩


attribute [local irreducible] agreement record effect RegistrationAgreementExecutor.beacon RegistrationBeaconRecordExecutor.begin

/-- Successful actual post-authentication execution contains one actual completed agreement, first-record result and true install reply, before publishing the exact application suffix. -/
theorem completion_cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (afterAuthentication setup wire index owner oneTime authenticated)).run before)) :
    ∃ capability established agreed recorded installed,
      (.ok (.BeaconComplete capability), agreed) ∈ support
        ((lower setup checks representation created
          (simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before) ∧
      (.ok (.Ok established), recorded) ∈ support
        ((lower setup checks representation created
          (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run agreed) ∧
      (true, installed) ∈ support
        ((lower setup checks representation created (effect (.inr (.installBeacon owner.worldOwner
          (⟨established.binding.assigned_key_id, established.control, established.binding.associated_data⟩ : BeaconShell)
          (.known established.kernel))))).run recorded) ∧
      application = TranscriptAuthParts.absSlice established.application := by
  rw [afterAuthentication, afterAuthenticationWith, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, agreed⟩, called, continued⟩ := supported
  cases reply with
  | fail error | div =>
      have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
      cases impossible
  | ok result => cases result with
    | BeaconComplete capability =>
        rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨reply, recorded⟩, opened, continued⟩ := continued
        cases reply with
        | fail error | div =>
            have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
            cases impossible
        | ok result => cases result with
          | Err aborted =>
              have impossible := terminal setup checks representation created (abort owner) _ recorded after application continued
              cases impossible
          | Ok established =>
              simp only [install_exact] at continued
              rw [lower_bind, StateT.run_bind, mem_support_bind_iff] at continued
              obtain ⟨⟨installed, final⟩, inserted, returned⟩ := continued
              cases installed with
              | false =>
                  have impossible := terminal setup checks representation created (abort owner) _ final after application returned
                  cases impossible
              | true =>
                  have same := terminal setup checks representation created
                    (updatePhase index (.established ⟨established.control, established.binding, established.application⟩)) _ final after application returned
                  exact ⟨capability, established, agreed, recorded, final, called, opened, inserted,
                    Option.some.inj (RustM.ok.inj same)⟩
    | _ =>
        have impossible := terminal setup checks representation created (abort owner) _ agreed after application continued
        cases impossible


end BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt.cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt.cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt.completion_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt.completion_cut
