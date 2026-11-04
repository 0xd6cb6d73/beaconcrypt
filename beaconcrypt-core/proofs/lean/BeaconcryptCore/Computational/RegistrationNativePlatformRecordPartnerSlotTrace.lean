-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTraceCore
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotInput
/-! The same persistent selective execution relates every successful opaque slot receipt to its actual chronological descriptor and complete selected input. All dictionary entries and physical platform effects persist across later requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePlatformRecordPartnerSlotTraceCore (Witness Ordered note event install)
open RegistrationNativePlatformRecordSlotGhost (Receipt)
open RegistrationNativeRelatedFamily (Message)
open PqxdhRecordLiftInterface (Slot)
variable {n : Nat} {I KemSK ProviderState Physical A : Type} {base : OracleSpec I}

abbrev State (n : Nat) (KemSK ProviderState Physical : Type) :=
  RegistrationNativePlatformPublicRecordSlots.State n × RegistrationNativeG2Trace.State ×
    (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState × Physical)

def Current (input : Message → Option Pqxdh.Bytes) (selected : Pqxdh.Bytes → Bool)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State)
    (keys : RegistrationNativeHiddenService.State n) : Prop :=
  ∀ slot,ghost.pending=some slot → ∃ message bytes,trace.current=some message ∧ input message=some bytes ∧
    selected bytes=true ∧ keys.slots bytes=some slot

def Entries (input : Message → Option Pqxdh.Bytes) (selected : Pqxdh.Bytes → Bool)
    (keys : RegistrationNativeHiddenService.State n) (entries : List (Witness n)) : Prop :=
  ∀ entry∈entries,∀slot,entry.receipt.slot=some slot →
    ∃ message bytes,entry.message=some message ∧ input message=some bytes ∧ selected bytes=true ∧ keys.slots bytes=some slot

def Valid (input : Message → Option Pqxdh.Bytes) (selected : Pqxdh.Bytes → Bool)
    (before : State n KemSK ProviderState Physical) : Prop :=
  RegistrationNativeSelectiveHiddenDictionaryRun.Good before.2.2.1 ∧
    Current input selected before.1 before.2.1 before.2.2.1.1.keys ∧
      ∃ entries,Ordered before.1 before.2.1 entries ∧ Entries input selected before.2.2.1.1.keys entries

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "backend" => RegistrationNativePlatformRecordPartnerSlotInput.closed setup wire sign seed scalar candidate provider physical
local notation "Input" => RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar
local notation "Selected" => RegistrationNativeSelectiveHiddenService.selected
  (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate

noncomputable def handler : QueryImpl (Spec n KemSK) (StateT (State n KemSK ProviderState Physical) ProbComp) := fun query before =>
  (fun reached=>(reached.1,(RegistrationNativePlatformPublicRecordSlots.step query reached.1 before.1,
    RegistrationNativeG2Trace.finish query reached.1 (RegistrationNativeG2Trace.begin query before.2.1),reached.2))) <$>
      (backend query).run before.2.2

private theorem current_keeps (oldGhost newGhost : RegistrationNativePlatformPublicRecordSlots.State n)
    (oldTrace newTrace : RegistrationNativeG2Trace.State) (oldKeys newKeys : RegistrationNativeHiddenService.State n)
    (valid : Current Input Selected oldGhost oldTrace oldKeys)
    (pending : newGhost.pending=oldGhost.pending) (current : newTrace.current=oldTrace.current)
    (keeps : ∀ bytes slot,oldKeys.slots bytes=some slot → newKeys.slots bytes=some slot) :
    Current Input Selected newGhost newTrace newKeys := by
  intro slot active
  obtain ⟨message,bytes,named,formed,selected,assigned⟩ := valid slot (pending.symm.trans active)
  exact ⟨message,bytes,current.trans named,formed,selected,keeps bytes slot assigned⟩

private theorem entries_keeps (oldKeys newKeys : RegistrationNativeHiddenService.State n) (entries : List (Witness n))
    (valid : Entries Input Selected oldKeys entries)
    (keeps : ∀ bytes slot,oldKeys.slots bytes=some slot → newKeys.slots bytes=some slot) :
    Entries Input Selected newKeys entries := by
  intro entry member slot hidden
  obtain ⟨message,bytes,named,formed,selected,assigned⟩ := valid entry member slot hidden
  exact ⟨message,bytes,named,formed,selected,keeps bytes slot assigned⟩

private theorem note_fields (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (trace : RegistrationNativeG2Trace.State)
    (entry : Witness n) (recorded : note query reply ghost trace=some entry) :
    entry.message=trace.current ∧ entry.receipt.slot=ghost.pending := by
  rcases query with (prepare|(demand|(publication|environment))|kem)|record
  · cases recorded
  · cases recorded
  · cases recorded
  · rcases environment with coin|capability
    · cases recorded
    · cases capability with
      | installServer keyId binding kernel | installBeacon owner binding kernel =>
          cases reply with
          | false => cases recorded
          | true =>
              change some _=some entry at recorded
              cases Option.some.inj recorded
              exact ⟨rfl,rfl⟩
      | _ => cases recorded
  · cases recorded
  · cases recorded

private theorem current_query (query : (Spec n KemSK).Domain)
    (before : State n KemSK ProviderState Physical) (reached : (Spec n KemSK).Range query ×
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState × Physical))
    (supported : reached∈support ((backend query).run before.2.2))
    (valid : Current Input Selected before.1 before.2.1 before.2.2.1.1.keys)
    (keeps : ∀ bytes slot,before.2.2.1.1.keys.slots bytes=some slot → reached.2.1.1.keys.slots bytes=some slot) :
    Current Input Selected (RegistrationNativePlatformPublicRecordSlots.step query reached.1 before.1)
      (RegistrationNativeG2Trace.finish query reached.1 (RegistrationNativeG2Trace.begin query before.2.1)) reached.2.1.1.keys := by
  rcases query with (prepare|(demand|(publication|environment))|kem)|record
  · intro slot impossible
    cases impossible
  · intro slot active
    rcases reached with ⟨reply,after⟩
    cases reply with
    | none => cases active
    | some choice => cases choice with
      | known output => cases active
      | hidden reference =>
          change some reference.slot=some slot at active
          cases Option.some.inj active
          obtain ⟨bytes,formed,selected,assigned⟩ := RegistrationNativePlatformRecordPartnerSlotInput.demand_receipt
            setup wire sign seed scalar candidate provider physical demand before.2.2 after reference supported
          exact ⟨demand,bytes,rfl,formed,selected,assigned⟩
  · exact current_keeps setup seed scalar candidate _ _ _ _ _ _ valid rfl rfl keeps
  · rcases environment with coin|capability
    · exact current_keeps setup seed scalar candidate _ _ _ _ _ _ valid rfl rfl keeps
    · cases capability with
      | installServer keyId binding kernel | installBeacon owner binding kernel =>
          intro slot impossible
          cases impossible
      | _ => exact current_keeps setup seed scalar candidate _ _ _ _ _ _ valid rfl rfl keeps
  · rcases kem with (other|key)|(pool|key)
    all_goals exact current_keeps setup seed scalar candidate _ _ _ _ _ _ valid rfl rfl keeps
  · exact current_keeps setup seed scalar candidate _ _ _ _ _ _ valid rfl rfl keeps

/-- Every actual persistent callback preserves the common ordered receipt list and its full selected-input dictionary witnesses. -/
theorem query (query : (Spec n KemSK).Domain) (before : State n KemSK ProviderState Physical)
    (valid : Valid Input Selected before) (result : (Spec n KemSK).Range query × State n KemSK ProviderState Physical)
    (supported : result∈support ((handler setup wire sign seed scalar candidate provider physical query).run before)) :
    Valid Input Selected result.2 := by
  simp only [handler,StateT.run,support_map] at supported
  obtain ⟨reached,called,rfl⟩ := supported
  have retained := RegistrationNativePlatformRecordPartnerSlotInput.program_keeps setup wire sign seed scalar candidate provider physical
    ((Spec n KemSK).query query) before.2.2 reached valid.1 (by simpa only [simulateQ_spec_query,StateT.run] using called)
  refine ⟨retained.1,current_query setup wire sign seed scalar candidate provider physical query before reached called valid.2.1 retained.2,?_⟩
  obtain ⟨entries,ordered,formed⟩ := valid.2.2
  refine ⟨entries++(note query reached.1 before.1 before.2.1).toList,
    RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_step query reached.1 before.1 before.2.1 entries ordered,?_⟩
  intro entry member slot hidden
  rw [List.mem_append] at member
  rcases member with earlier|new
  · exact entries_keeps setup seed scalar candidate _ _ entries formed retained.2 entry earlier slot hidden
  · cases noted : note query reached.1 before.1 before.2.1 with
    | none => simp only [noted,Option.toList_none,List.not_mem_nil] at new
    | some actual =>
        simp only [noted,Option.toList_some,List.mem_singleton] at new
        subst entry
        have fields := note_fields query reached.1 before.1 before.2.1 actual noted
        obtain ⟨message,bytes,named,input,selected,assigned⟩ := valid.2.1 slot (fields.2.symm.trans hidden)
        exact ⟨message,bytes,fields.1.trans named,input,selected,retained.2 bytes slot assigned⟩

/-- The actual adaptive execution preserves every earlier successful installation/input receipt through arbitrary reached physical effects. -/
theorem program (work : OracleComp (Spec n KemSK) A) (before : State n KemSK ProviderState Physical)
    (valid : Valid Input Selected before) (result : A × State n KemSK ProviderState Physical)
    (supported : result∈support ((simulateQ (handler setup wire sign seed scalar candidate provider physical) work).run before)) :
    Valid Input Selected result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind request next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      exact ih middle.1 middle.2 (query setup wire sign seed scalar candidate provider physical request before valid middle called) result continued

/-- Cold analysis observers require only the actual dictionary invariant of the retained native state. -/
theorem initial (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (physicalBefore : Physical)
    (good : RegistrationNativeSelectiveHiddenDictionaryRun.Good before) :
    Valid Input Selected (RegistrationNativePlatformPublicRecordSlots.initial,RegistrationNativeG2Trace.initial,(before,physicalBefore)) := by
  refine ⟨good,?_,[],RegistrationNativePlatformRecordPartnerSlotTraceCore.ordered_initial,?_⟩
  · intro slot impossible
    cases impossible
  · intro entry member
    cases member

/-- Every hidden snapshot receipt has its exact ordered native descriptor and complete selected-input witness in the final persistent dictionary. -/
theorem receipt_at (before : State n KemSK ProviderState Physical) (valid : Valid Input Selected before)
    (ordinal : Nat) (receipt : Receipt n) (found : before.1.snapshot.installs[ordinal]?=some receipt)
    (slot : Slot n) (hidden : receipt.slot=some slot) :
    ∃ (entries past suffix : List (Witness n)) (entry : Witness n) (message : Message) (bytes : Pqxdh.Bytes),
      Ordered before.1 before.2.1 entries ∧ entries=past++entry::suffix ∧ past.length=ordinal ∧
      entry.receipt=receipt ∧ entry.message=some message ∧ Input message=some bytes ∧ Selected bytes=true ∧
      before.2.2.1.1.keys.slots bytes=some slot ∧
      before.2.1.events.filterMap install =past.filterMap event++[(receipt.role,message)]++suffix.filterMap event := by
  obtain ⟨entries,ordered,formed⟩ := valid.2.2
  rw [ordered.1,List.getElem?_map] at found
  cases taken : entries[ordinal]? with
  | none => simp only [taken,Option.map_none] at found; cases found
  | some entry =>
      simp only [taken,Option.map_some,Option.some.injEq] at found
      obtain ⟨inside,elementEq⟩ := List.getElem?_eq_some_iff.mp taken
      have decomposition : entries=entries.take ordinal++entry::entries.drop (ordinal+1) := by
        conv_lhs => rw [←List.take_append_drop ordinal entries]
        rw [List.drop_eq_getElem_cons inside,elementEq]
      have member : entry∈entries := List.mem_of_getElem? taken
      obtain ⟨message,bytes,named,input,selected,assigned⟩ := formed entry member slot ((congrArg Receipt.slot found).trans hidden)
      refine ⟨entries,entries.take ordinal,entries.drop (ordinal+1),entry,message,bytes,ordered,decomposition,?_,found,named,input,selected,assigned,?_⟩
      · simp only [List.length_take,Nat.min_eq_left (Nat.le_of_lt inside)]
      · rw [ordered.2]
        conv_lhs => rw [decomposition,List.filterMap_append,List.filterMap_cons]
        simp only [event,named,Option.map_some,found,List.append_assoc,List.singleton_append]

/-- Two hidden receipts for the same actual slot name one identical complete selected input, without root or material equality. -/
theorem same_slot (before : State n KemSK ProviderState Physical) (valid : Valid Input Selected before)
    (first second : Nat) (firstReceipt secondReceipt : Receipt n)
    (firstAt : before.1.snapshot.installs[first]?=some firstReceipt)
    (secondAt : before.1.snapshot.installs[second]?=some secondReceipt)
    (slot : Slot n) (firstSlot : firstReceipt.slot=some slot) (secondSlot : secondReceipt.slot=some slot) :
    ∃ firstMessage secondMessage bytes,
      (firstReceipt.role,firstMessage)∈before.2.1.events.filterMap install ∧
      (secondReceipt.role,secondMessage)∈before.2.1.events.filterMap install ∧
      Input firstMessage=some bytes ∧ Input secondMessage=some bytes ∧ Selected bytes=true ∧
      before.2.2.1.1.keys.slots bytes=some slot := by
  obtain ⟨_entries,firstPrefix,firstSuffix,_entry,firstMessage,firstBytes,_ordered,_split,_length,_receipt,_named,
    firstFormed,firstSelected,firstAssigned,firstEvents⟩ := receipt_at setup seed scalar candidate before valid first firstReceipt firstAt slot firstSlot
  obtain ⟨_entries,secondPrefix,secondSuffix,_entry,secondMessage,secondBytes,_ordered,_split,_length,_receipt,_named,
    secondFormed,_secondSelected,secondAssigned,secondEvents⟩ := receipt_at setup seed scalar candidate before valid second secondReceipt secondAt slot secondSlot
  have same : firstBytes=secondBytes := valid.1.2 firstBytes secondBytes slot firstAssigned secondAssigned
  refine ⟨firstMessage,secondMessage,firstBytes,?_,?_,firstFormed,same ▸ secondFormed,firstSelected,firstAssigned⟩
  · rw [firstEvents]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))))
  · rw [secondEvents]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_singleton_self _))))

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.receipt_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.receipt_at

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.same_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSlotTrace.same_slot
