-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSnapshotHandles
/-! Exact successful source-handle lists follow the original typed, raw and full public ledger. Local callback receipts are transported through actual parsing and secrecy callbacks without replacing successful session coordinates by attempt ordinals. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger
open RegistrationNativeRawAdapter (TypedSpec adapter handler)
open RegistrationNativeInstallOrdinals (handles)
open RegistrationNativeInstallTypedEntry (entry)
variable {NativeState : Type}
variable (typed : QueryImpl TypedSpec (StateT NativeState ProbComp)) (wire : RegistrationNativeWire.Wire)
    (observed : PqxdhRecordLiftInterface.Role → NativeState → List PqxdhDeploymentInterface.Handle)
    (valid : NativeState → Prop)
    (step : ∀ query before result, valid before → result∈support ((typed query).run before) →
      ∀ role,observed role result.2=observed role before++handles role [entry query result.1])

include step
private theorem mapped (query : RegistrationNativeInterface.Spec.Domain) (request : TypedSpec.Domain)
    (observe : TypedSpec.Range request → RegistrationNativeInterface.Spec.Range query)
    (source : adapter wire query = observe <$> (TypedSpec.query request : OracleComp TypedSpec _))
    (same : ∀ reply role, handles role [entry request reply] = handles role [⟨.inl query, observe reply⟩])
    (before : NativeState) (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (prior : valid before) (supported : result ∈ support ((handler wire typed query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    observed role result.2=observed role before++handles role [⟨.inl query,result.1⟩] := by
  rw [handler, QueryImpl.apply_compose, source, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨actual, called, rfl⟩ := supported
  rw [step request before actual prior called role,same actual.1 role]

omit step in
private theorem rejected (query : RegistrationNativeInterface.Spec.Domain)
    (reply : RegistrationNativeInterface.Spec.Range query) (source : adapter wire query = pure reply)
    (empty : ∀ role, handles role [⟨.inl query, reply⟩] = [])
    (before : NativeState) (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (supported : result ∈ support ((handler wire typed query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    observed role result.2=observed role before++handles role [⟨.inl query,result.1⟩] := by
  rw [handler, QueryImpl.apply_compose, source, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  simp only [empty role,List.append_nil]

/-- Every actual raw native callback carries the typed successful installation receipt for its original query and reply. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : NativeState)
    (result : RegistrationNativeInterface.Spec.Range query × NativeState)
    (prior : valid before) (supported : result ∈ support ((handler wire typed query).run before))
    (role : PqxdhRecordLiftInterface.Role) :
    observed role result.2=observed role before++handles role [⟨.inl query,result.1⟩] := by
  cases query with
  | inl coin =>
      exact mapped typed wire observed valid step _ (.inl coin) id rfl
        (fun reply role => by cases role <;> rfl) before result prior supported role
  | inr command => cases command with
    | create edPin mlPin keyId =>
        cases ed : PqxdhDeploymentInterface.parsePin edPin with
        | none =>
            exact rejected typed wire observed (.inr (.create edPin mlPin keyId)) none (by simp only [adapter, ed])
              (fun role => by cases role <;> rfl) before result supported role
        | some edParsed => cases ml : RegistrationNativeWire.parseMldsaPin mlPin with
          | none =>
              exact rejected typed wire observed (.inr (.create edPin mlPin keyId)) none (by simp only [adapter, ed, ml])
                (fun role => by cases role <;> rfl) before result supported role
          | some mlParsed =>
              exact mapped typed wire observed valid step _ (.inr (.create edParsed mlParsed keyId))
                RegistrationNativeRawAdapter.resultOption (by simp only [adapter, ed, ml])
                (fun reply role => by cases role <;> rfl) before result prior supported role
    | accept raw =>
        cases parsed : RegistrationNativeWire.readInit wire raw with
        | none =>
            exact rejected typed wire observed (.inr (.accept raw)) none (by simp only [adapter, parsed])
              (fun role => by cases role <;> rfl) before result supported role
        | some packet =>
            exact mapped typed wire observed valid step _ (.inr (.accept packet))
              RegistrationNativeRawAdapter.resultOption (by simp only [adapter, parsed])
              (fun reply role => by cases role <;> rfl) before result prior supported role
    | bundle owner =>
        exact mapped typed wire observed valid step _ (.inr (.bundle owner))
          RegistrationNativeRawAdapter.resultOption rfl (fun reply role => by cases role <;> rfl) before result prior supported role
    | build handle payload =>
        exact mapped typed wire observed valid step _ (.inr (.build handle (RegistrationNativeRawAdapter.application payload)))
          RegistrationNativeRawAdapter.responseOption rfl (fun reply role => by
            cases role <;> cases reply with
            | fail _ => rfl
            | div => rfl
            | ok answer => cases answer <;> rfl) before result prior supported role
    | finish owner raw =>
        exact mapped typed wire observed valid step _ (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw)))
          RegistrationNativeRawAdapter.resultOption rfl (fun reply role => by
            cases role <;> cases reply with
            | fail _ => rfl
            | div => rfl
            | ok answer => cases answer <;> rfl) before result prior supported role
    | hmac key message =>
        exact mapped typed wire observed valid step _ (.inr (.hmac key message)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | hash bytes =>
        exact mapped typed wire observed valid step _ (.inr (.hash bytes)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | serverSend keyId plaintext =>
        exact mapped typed wire observed valid step _ (.inr (.serverSend keyId plaintext)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | serverRaw raw =>
        exact mapped typed wire observed valid step _ (.inr (.serverRaw raw)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | beaconSend owner plaintext =>
        exact mapped typed wire observed valid step _ (.inr (.beaconSend owner plaintext)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role
    | beaconRaw owner raw =>
        exact mapped typed wire observed valid step _ (.inr (.beaconRaw owner raw)) id rfl
          (fun reply role => by cases role <;> rfl) before result prior supported role

section Full
omit step
variable {Value Reader Response : Type}
variable (preserves : ∀ query before result,valid before → result∈support ((typed query).run before) → valid result.2)

include preserves in
private theorem typed_program (work : OracleComp TypedSpec Value) (before : NativeState) (result : Value × NativeState)
    (prior : valid before) (supported : result∈support ((simulateQ typed work).run before)) : valid result.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported;cases supported;exact prior
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,later⟩ := supported
    exact ih middle.1 middle.2 result (preserves query before middle prior called) later

include preserves in
private theorem raw_preserves (query : RegistrationNativeInterface.Spec.Domain) (before : NativeState)
    (result : RegistrationNativeInterface.Spec.Range query × NativeState) (prior : valid before)
    (supported : result∈support ((handler wire typed query).run before)) : valid result.2 := by
  have law := RegistrationNativeRawAdapter.program_native wire typed (RegistrationNativeInterface.Spec.query query) before
  simp only [simulateQ_spec_query] at law
  rw [law] at supported
  exact typed_program typed valid preserves _ before result prior supported

private theorem restricted_handles (query : RegistrationNativeInterface.Spec.Domain)
    (reply : RegistrationNativeInterface.Spec.Range query)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query)≠false)
    (role : PqxdhRecordLiftInterface.Role) : handles role [⟨.inl query,reply⟩]=[] := by
  cases query with
  | inl coin=>cases role <;> rfl
  | inr command=>cases command <;> cases role <;>
      simp_all [PqxdhDeploymentSecrecy.coinOrSend,RegistrationNativeInterface.eraseCore,RegistrationNativeInterface.eraseCommand,handles]

include step preserves in
private theorem restricted (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP (fun query=>PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query)=false) 0)
    (before : NativeState) (result : Value × NativeState) (prior : valid before)
    (supported : result∈support ((simulateQ (handler wire typed) work).run before)) :
    valid result.2 ∧ ∀role,observed role result.2=observed role before := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨prior,fun _=>rfl⟩
  | query_bind query next ih=>
    rw [isQueryBoundP_query_bind_iff] at bounded
    have allowed := bounded.1.resolve_right (by omega)
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,later⟩ := supported
    have first := raw_preserves typed wire valid preserves query before middle prior called
    have last := ih middle.1 (by simpa using bounded.2 middle.1) middle.2 result first later
    refine ⟨last.1,fun role=>?_⟩
    rw [last.2 role,raw typed wire observed valid step query before middle prior called role,restricted_handles query middle.1 allowed role,List.append_nil]

private theorem ledger_trace (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State)
    (result : RegistrationNativeInterface.FullSpec.Range query × RegistrationNativeLedger.State)
    (supported : result∈support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds query).run before)) :
    result.2.transcript=before.transcript++[⟨query,result.1⟩] := by
  cases query with
  | inl query=>rw [RegistrationNativeLedger.query_forward,support_map] at supported;obtain ⟨reply,_called,rfl⟩:=supported;rfl
  | inr query=>rw [RegistrationNativeLedger.query_secrecy,support_map] at supported;obtain ⟨reply,_called,rfl⟩:=supported;rfl

include step preserves in
/-- Every literal full callback appends exactly the handles of its same original public reply, including secrecy sends and all failures. -/
theorem full_step (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × NativeState)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × NativeState))
    (prior : valid before.2)
    (supported : result∈support ((RegistrationNativeLedger.interpreted (handler wire typed) crypto codec serverKeyId bounds query).run before)) :
    valid result.2.2 ∧ result.2.1.transcript=before.1.transcript++[⟨query,result.1⟩] ∧
      ∀role,observed role result.2.2=observed role before.2++handles role [⟨query,result.1⟩] := by
  cases query with
  | inl query=>
    rw [RegistrationNativeLedger.interpreted,QueryImpl.flattenStateT_mapStateTBase_apply_run] at supported
    simp only [RegistrationNativeLedger.query_forward,simulateQ_map,simulateQ_spec_query,StateT.run_map,Functor.map_map,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    exact ⟨raw_preserves typed wire valid preserves query before.2 inner prior called,rfl,
      raw typed wire observed valid step query before.2 inner prior called⟩
  | inr query=>
    rw [RegistrationNativeLedger.interpreted,QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
    obtain ⟨inner,called,rfl⟩ := supported
    have kept := restricted typed wire observed valid step preserves _
      (RegistrationNativeLedger.secrecy_frame crypto codec serverKeyId bounds query before.1) before.2 inner prior called
    have original : inner.1∈support ((RegistrationNativeLedger.handler crypto codec serverKeyId bounds (.inr query)).run before.1) := by
      apply OracleComp.support_simulateQ_run'_subset (handler wire typed) _ before.2
      rw [StateT.run'_eq,support_map]
      exact Set.mem_image_of_mem Prod.fst called
    refine ⟨kept.1,ledger_trace crypto codec serverKeyId bounds (.inr query) before.1 inner.1 original,fun role=>?_⟩
    have quiet : handles role [⟨.inr query,inner.1.1⟩]=[] := by cases role <;> rfl
    simp only [quiet,List.append_nil]
    exact kept.2 role

include step preserves in
/-- Exact local callback receipts derive the whole full-compiler handle list at its literal native ledger transcript. -/
theorem full_program (crypto : Pqxdh.Crypto)
    (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value) (before : RegistrationNativeLedger.State × NativeState)
    (leadingHandles : PqxdhRecordLiftInterface.Role → List PqxdhDeploymentInterface.Handle)
    (prior : valid before.2) (initial : ∀role,observed role before.2=leadingHandles role++handles role before.1.transcript)
    (result : Value × (RegistrationNativeLedger.State × NativeState))
    (supported : result∈support ((simulateQ (RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds typed) work).run before)) :
    valid result.2.2 ∧ ∀role,observed role result.2.2=leadingHandles role++handles role result.2.1.transcript := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact ⟨prior,initial⟩
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,later⟩ := supported
    have first := full_step typed wire observed valid step preserves crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query before middle prior called
    apply ih middle.1 middle.2 first.1 _ result later
    intro role
    rw [first.2.2 role,initial role,first.2.1,RegistrationNativeInstallOrdinals.handles_append,List.append_assoc]
end Full

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.full_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.full_step
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.full_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerHandlesLedger.full_program
