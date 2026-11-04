-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseFinish
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

/-! Native successful completion receipts retain the actual agreement capability, first-record opening, installation query and final plaintext from one supported source execution. Agreement and kernel retention are derived from the extracted continuation bodies, rather than assumed from a partner relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (BeaconShell)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)
open RegistrationNativeResponseFinish (afterAuthentication)
variable {n : Nat} {ι KemSK Value Next Index : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source} {spec : OracleSpec Index}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State))
    (work : OracleComp spec Value) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

private theorem source_support (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State))
    (work : OracleComp spec Value) (before after : Local n KemSK source) (value : Value)
    (supported : (value, after) ∈ support
      ((lower setup checks representation created (simulateQ implementation work)).run before)) :
    value ∈ support work := by
  rw [lower_simulate] at supported
  apply OracleComp.support_simulateQ_run'_subset
    (fun query => lower setup checks representation created (implementation query)) work before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

private theorem terminal (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (outcome : RustM (Option Pqxdh.Bytes)) (before after : Local n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created (work *> pure outcome)).run before)) :
    .ok (some application) = outcome := by
  rw [seqRight_eq_bind, lower_bind, lower_pure, StateT.run_bind] at supported
  simp only [StateT.run_pure, bind_pure_comp, support_map] at supported
  obtain ⟨result, _possible, same⟩ := supported
  exact (congrArg Prod.fst same).symm

attribute [local irreducible] agreement record abort effect RegistrationAgreementExecutor.beacon RegistrationBeaconRecordExecutor.begin

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
          (⟨owner.pin.binding.identity_key_id, established.control, established.binding.associated_data⟩ : BeaconShell)
          (.known established.kernel))))).run recorded) ∧
      application = TranscriptAuthParts.absSlice established.application := by
  rw [afterAuthentication, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
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

/-- The actual agreement capability in a complete native finish retains every authenticated registration-binding field, including both pins and populated AD281. -/
theorem binding (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (capability : agreement.BeaconAgreement)
    (before after : Local n KemSK source)
    (supported : (.ok (.BeaconComplete capability), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before)) :
    capability.binding = authenticated.pending.binding :=
  RegistrationAgreementExecutor.beacon_binding authenticated capability
    (source_support setup checks representation created _ _ before after _ supported)

/-- The first-record continuation reaches its actual native AEAD finish from the exact initial capability carrying that agreement root. -/
theorem record_reaches (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon)
    (before after : Local n KemSK source)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before)) :
    ∃ (initial : registration.BeaconInitialKdf) (pending : registration.BeaconRecordAead)
      (plaintext : core.option.Option (Slice Std.U8)),
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
      pending.finish plaintext = .ok (.Ok completed) := by
  have native := source_support setup checks representation created (record setup wire)
    (RegistrationBeaconRecordExecutor.begin capability) before after _ supported
  unfold RegistrationBeaconRecordExecutor.begin at native
  cases started : registration.begin_beacon_completion capability with
  | fail error | div =>
      simp only [started, RegistrationBeaconRecordExecutor.continueWith, support_pure, Set.mem_singleton_iff] at native
      cases native
  | ok initial =>
      simp only [started, RegistrationBeaconRecordExecutor.continueWith] at native
      obtain ⟨pending, plaintext, reached, finished⟩ :=
        RegistrationBeaconRecordExecutor.fromInitial_reaches initial completed native
      exact ⟨initial, pending, plaintext, rfl,
        RegistrationBeaconRecordExecutor.initial_agreement capability initial started, reached, finished⟩

/-- Native first-record success retains the actual agreement root, initial capability, populated metadata, consumed sequence-one kernel and admitted application bytes. -/
theorem record_consumed (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (capability : agreement.BeaconAgreement) (completed : registration.CompletedBeacon)
    (before after : Local n KemSK source)
    (supported : (.ok (.Ok completed), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (record setup wire) (RegistrationBeaconRecordExecutor.begin capability))).run before)) :
    completed.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        capability.binding capability.candidate.assigned_key_id ∧
      ∃ (initial : registration.BeaconInitialKdf) (pending : registration.BeaconRecordAead) (plaintext : Slice Std.U8),
        registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
        BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
        pending.agreement = capability ∧
        pending.pending.finish (.Some plaintext) = .ok (completed.kernel,
          .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ :
            record.OpenedRecord (Slice Std.U8))) ∧ completed.application = plaintext.drop 8#usize := by
  obtain ⟨initial, pending, plaintext, started, initialSame, reached, finished⟩ :=
    record_reaches setup checks representation created wire capability completed before after supported
  obtain ⟨kernel, own, specification⟩ :=
    BeaconcryptCore.Refinement.RegistrationReachability.reachable_completion initial pending plaintext reached
  have sameAgreement : pending.agreement = capability := own.trans initialSame
  have admitted := specification.2.2
  rw [finished] at admitted
  cases plaintext with
  | none => simp at admitted
  | some bytes =>
      simp only [RustM.ok.injEq] at admitted
      change core.result.Result.Ok completed =
        (if 8 < bytes.val.length ∧ (bytes.val.take 8).map absByte =
            Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
          then .Ok (BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon pending kernel bytes)
          else .Err (⟨pending.agreement.candidate.server_binding.identity_key_id⟩ : pqxdh.BeaconAborted)) at admitted
      split at admitted
      · have same : completed = BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon pending kernel bytes := by
          simpa using admitted
        rw [same]
        refine ⟨?_, initial, pending, bytes, started, initialSame, reached, sameAgreement, ?_, rfl⟩
        · simp only [BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon, sameAgreement]
        · simpa only [BeaconcryptCore.Refinement.RegistrationRecords.completedBeacon, sameAgreement] using specification.2.1
      · simp at admitted

/-- Every successful actual post-authentication finish has its full source-stage agreement and consumed-kernel receipt; all retained pins, root and initial state belong to that same supported execution. -/
theorem complete (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (afterAuthentication setup wire index owner oneTime authenticated)).run before)) :
    ∃ (capability : agreement.BeaconAgreement) (established : registration.CompletedBeacon)
      (initial : registration.BeaconInitialKdf) (pending : registration.BeaconRecordAead) (plaintext : Slice Std.U8),
      capability.binding = authenticated.pending.binding ∧
      established.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
        authenticated.pending.binding capability.candidate.assigned_key_id ∧
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
      pending.agreement = capability ∧
      pending.pending.finish (.Some plaintext) = .ok (established.kernel,
        .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ :
          record.OpenedRecord (Slice Std.U8))) ∧
      established.application = plaintext.drop 8#usize ∧
      application = TranscriptAuthParts.absSlice established.application := by
  obtain ⟨capability, established, agreed, recorded, _installed, first, opened, _inserted, same⟩ :=
    completion_cut setup checks representation created wire index owner oneTime authenticated before after application supported
  have retained := binding setup checks representation created owner oneTime authenticated capability before agreed first
  obtain ⟨metadata, initial, pending, plaintext, started, initialSame, reached, sameAgreement, kernel, message⟩ :=
    record_consumed setup checks representation created wire capability established agreed recorded opened
  exact ⟨capability, established, initial, pending, plaintext, retained,
    by simpa only [retained] using metadata, started, initialSame, reached, sameAgreement, kernel, message, same⟩

/-- A complete source-stage receipt retains the root-bearing agreement and initial capability, all populated metadata, assigned identifier, actual consumed receive kernel and exact payload. -/
def Receipt (owners : State source) (index : Nat) (packet : Option registration.ResponsePacket)
    (application : Pqxdh.Bytes) : Prop :=
  ∃ (owner : Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (received : registration.ResponsePacket) (capability : agreement.BeaconAgreement)
    (established : registration.CompletedBeacon) (initial : registration.BeaconInitialKdf)
    (pending : registration.BeaconRecordAead) (plaintext : Slice Std.U8),
    owners[index]? = some owner ∧ owner.phase = .initSent original oneTime ∧ packet = some received ∧
    capability.binding = original.binding ∧
    established.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding
      original.binding capability.candidate.assigned_key_id ∧
    registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
    BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested pending) ∧
    pending.agreement = capability ∧
    pending.pending.finish (.Some plaintext) = .ok (established.kernel,
      .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ :
        record.OpenedRecord (Slice Std.U8))) ∧
    established.application = plaintext.drop 8#usize ∧
    application = TranscriptAuthParts.absSlice established.application

/-- Original complete finish success derives its complete source-stage receipt directly, including mandatory response authentication, with no completed-agreement premise. -/
theorem finish (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before)) :
    Receipt before.1 index packet application := by
  obtain ⟨owner, original, oneTime, aborted, authenticated, middle, selected, phase, _moved, called, continued⟩ :=
    RegistrationNativeResponseFinish.cut setup checks representation created wire index packet before after application supported
  cases packet with
  | none =>
      rw [RegistrationResponseExecutor.begin_malformed, simulateQ_pure, lower_pure] at called
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
      cases called
  | some received =>
      have projected : (.ok (.Ok authenticated), project middle) ∈ support
          ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
            (RawCtxSourceHkdf.kdfImpl setup.source) original (.Some received)).run
              (project (RegistrationNativeResponseFinish.consumed before index aborted))) := by
        rw [RegistrationResponseExecutor.execute,
          ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
        exact Set.mem_image_of_mem (Prod.map id project) called
      obtain ⟨_digest, same, _verified, _receipts, _earlier, _cached⟩ := RegistrationResponseExecutor.accepted_receipt
        setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
        original received (project (RegistrationNativeResponseFinish.consumed before index aborted))
        (project middle) authenticated projected
      obtain ⟨capability, established, initial, pending, plaintext, retained, metadata, started,
        initialSame, reached, sameAgreement, kernel, message, returned⟩ :=
        complete setup checks representation created wire index owner oneTime authenticated middle after application continued
      subst authenticated
      exact ⟨owner, original, oneTime, received, capability, established, initial, pending, plaintext,
        selected, phase, rfl, retained, metadata, started, initialSame, reached, sameAgreement, kernel, message, returned⟩

private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id RegistrationNativeMldsaShared.close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, RegistrationNativeMldsaShared.close]

/-- The original mandatory-ML typed finish, on its unchanged source profile, derives the same complete consumed-kernel receipt. -/
theorem typed_finish (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (credential : RegistrationNativeMldsa.Credential source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index packet))).run before)) : Receipt before.beacons index packet application := by
  change (.ok (some application), after) ∈ support
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index packet)).run before) at supported
  rw [source_lower, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  have outcome : reached.1 = .ok (some application) := congrArg Prod.fst same
  exact finish setup checks representation created wire index packet
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) reached.2 application
    (outcome ▸ possible)

end BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.completion_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.completion_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.binding
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.record_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.record_reaches

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.record_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.record_consumed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.typed_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt.typed_finish
