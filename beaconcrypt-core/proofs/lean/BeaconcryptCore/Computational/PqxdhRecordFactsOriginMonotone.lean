-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginAmbient
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReceive

/-! Existing produced frames and seal-dictionary entries persist through the actual adaptive record client. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftIdeal PqxdhRecordFactsOriginServices
open PqxdhRecordLiftWorldCompiler (Label)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The source can append publications and insert seals, without discarding prior witnesses. -/
structure Grows (before after : CtxPrivate n) : Prop where
  produced : ∃ tail, after.base.produced = before.base.produced ++ tail
  seals : ∀ label entry, entry ∈ (before.keys label).1.successfulSeals →
    entry ∈ (after.keys label).1.successfulSeals

/-- Exact retention is a special case of witness growth. -/
theorem grows_of_equal (before after : CtxPrivate n)
    (produced : after.base.produced = before.base.produced)
    (seals : ∀ label, (after.keys label).1.successfulSeals = (before.keys label).1.successfulSeals) :
    Grows before after :=
  ⟨⟨[], by simpa only [List.append_nil] using produced⟩,
    fun label _ member => (seals label).symm ▸ member⟩

/-- Every previously produced tagged frame remains in the final source log. -/
theorem Grows.produced_mem (before after : CtxPrivate n) (grows : Grows before after)
    (entry : PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
    (member : entry ∈ before.base.produced) : entry ∈ after.base.produced :=
  grows.produced.elim fun tail equal => equal ▸ List.mem_append_left tail member

/-- Every actual service preserves prior publication and seal witnesses. -/
theorem service_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (before : CtxPrivate n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec query).run before)) :
    Grows before result.2 := by
  cases query
  case sealing pending =>
    obtain ⟨produced, unchanged | ⟨width, record, inserted, logged, reply⟩⟩ :=
      sealing_trace modes ideal replace setup codec pending before result supported
    · exact ⟨⟨[], by simpa only [List.append_nil] using produced⟩,
        fun label entry member => (unchanged.2.2 label).symm ▸ member⟩
    · refine ⟨⟨[], by simpa only [List.append_nil] using produced⟩, ?_⟩
      intro label entry member
      by_cases same : label = pending.material
      · simpa only [same, inserted, List.mem_cons] using Or.inr (same ▸ member)
      · exact (congrArg (fun state : KeyEntry => state.1.successfulSeals)
          (PqxdhRecordLiftCtxHybrid.sealing_other modes replace setup codec pending before result supported label same)).symm ▸ member
  case opening pending =>
    exact grows_of_equal before result.2
      (PqxdhRecordFactsOriginReceive.opening_logs modes replace setup codec pending before result supported).1
      (opening_seals modes ideal replace setup codec pending before result supported)
  case lookup coordinate =>
    exact grows_of_equal before result.2
      (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec coordinate before result supported).2.1
      (fun label => congrArg (fun keys => (keys label : KeyEntry).1.successfulSeals)
        (PqxdhRecordFactsOriginReceive.lookup_preserves modes replace setup codec coordinate before result supported).1)
  case publish tag =>
    simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
      StateT.run, map_pure, support_pure, Set.mem_singleton_iff] at supported
    exact supported ▸ ⟨⟨_, rfl⟩, fun _ _ member => member⟩
  all_goals first
    | exact grows_of_equal before result.2
        (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec _ (by trivial) before result supported).produced
        (fun label => congrArg (fun keys => (keys label : KeyEntry).1.successfulSeals)
          (PqxdhRecordFactsOriginAmbient.environmental_kept modes replace setup codec _ (by trivial) before result supported).keys)
    | skip
  all_goals simp only [ctxInterpreter, onBase, PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.withRecord, StateT.run, bind_pure_comp, Functor.map_map,
    support_map] at supported
  all_goals obtain ⟨inner, reached, rfl⟩ := supported
  all_goals exact grows_of_equal before _ rfl (fun _ => rfl)

/-- An unchanged state retains every prior witness. -/
theorem Grows.refl (state : CtxPrivate n) : Grows state state :=
  grows_of_equal state state rfl (fun _ => rfl)

/-- Growth composes through the actual intermediate state. -/
theorem Grows.trans (before middle after : CtxPrivate n) (first : Grows before middle)
    (second : Grows middle after) : Grows before after := by
  obtain ⟨left, leftEq⟩ := first.produced
  obtain ⟨right, rightEq⟩ := second.produced
  exact ⟨⟨left ++ right, by simpa only [leftEq, List.append_assoc] using rightEq⟩,
    fun label entry member => second.seals label entry (first.seals label entry member)⟩

/-- Any adaptive private-service client retains all prior witnesses at every supported final state. -/
theorem program_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (before : CtxPrivate n)
    (result : X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (ctxInterpreter modes replace setup codec) program).run before)) :
    Grows before result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (ctxInterpreter modes replace setup codec) (Grows before)
    (fun query state previous output reached => Grows.trans before state output.2 previous
      (service_grows modes ideal replace setup codec query state output reached))
    program before (Grows.refl before) result supported

/-- Every actual native command keeps prior witnesses, including arbitrary environment commands. -/
theorem native_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (query : PqxdhDeploymentInterface.Spec.Domain)
    (before : PqxdhRecordLiftFlat.NativeState n E)
    (result : PqxdhDeploymentInterface.Spec.Range query × PqxdhRecordLiftFlat.NativeState n E)
    (supported : result ∈ support ((PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env query).run before)) :
    Grows before.2 result.2.2 := by
  rw [PqxdhRecordLiftFlat.nativeImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact program_grows modes ideal replace setup codec _ before.2 inner reached

/-- Arbitrarily scheduled native commands retain old dictionary entries and the complete produced prefix. -/
theorem native_program_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (program : OracleComp PqxdhDeploymentInterface.Spec X)
    (before : PqxdhRecordLiftFlat.NativeState n E) (result : X × PqxdhRecordLiftFlat.NativeState n E)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env) program).run before)) :
    Grows before.2 result.2.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env)
    (fun state => Grows before.2 state.2)
    (fun query state previous output reached => Grows.trans before.2 state.2 output.2.2 previous
      (native_grows modes ideal replace setup codec route env query state output reached))
    program before (Grows.refl before.2) result supported

/-- A complete secrecy-ledger query preserves old witnesses, including every forwarded native command. -/
theorem full_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E)
    (result : PqxdhDeploymentInterface.FullSpec.Range query ×
      (PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E))
    (supported : result ∈ support ((PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds query).run before)) :
    Grows before.2.2 result.2.2.2 := by
  rw [PqxdhRecordLiftFlat.fullImpl_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact native_program_grows modes ideal replace setup codec route env _ before.2 inner reached

/-- Adaptive raw receives, honest sends, tests, reveals and stopping retain all earlier witnesses. -/
theorem full_program_grows (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : PqxdhRecordLiftInterface.Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (program : OracleComp PqxdhDeploymentInterface.FullSpec X)
    (before : PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E)
    (result : X × (PqxdhDeploymentSecrecy.Ledger × PqxdhRecordLiftFlat.NativeState n E))
    (supported : result ∈ support ((simulateQ
      (PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds) program).run before)) :
    Grows before.2.2 result.2.2.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftFlat.fullImpl modes replace setup codec route env serverKid bounds)
    (fun state => Grows before.2.2 state.2.2)
    (fun query state previous output reached => Grows.trans before.2.2 state.2.2 output.2.2.2 previous
      (full_grows modes ideal replace setup codec route env serverKid bounds query state output reached))
    program before (Grows.refl before.2.2) result supported

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.grows_of_equal' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.grows_of_equal
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.produced_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.produced_mem
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.service_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.service_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.refl
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.Grows.trans
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.program_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.native_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.native_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.native_program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.native_program_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.full_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.full_grows
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.full_program_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMonotone.full_program_grows
