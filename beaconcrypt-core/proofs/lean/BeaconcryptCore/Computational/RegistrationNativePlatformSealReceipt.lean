-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSealTrace
import BeaconcryptCore.Refinement.AdapterRecordRawBytes

/-! Successful source sealing retains the actual public reservation and trusted native AEAD call. Source checked arithmetic supplies any required capacity; optional primitive conversion and allocation failures cannot create a successful receipt. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {E Auxiliary Platform ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable [primitive : AdapterSealPrimitive.Operations]

theorem joined (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (prefixBytes : Std.Array U8 8#usize) (application plaintext : Slice U8)
    (before after : State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (some plaintext), after), next) ∈ support
      (((simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
        (AdapterSealNative.joined E prefixBytes application)).run before).run previous)) :
    ∃ capacity success,
      prefixBytes.val.length + application.val.length = capacity.val ∧
      (.ok (.Ok success), next) ∈ support ((allocation (Slice.new U8) capacity).run previous) ∧
      after = before ∧ plaintext.val = prefixBytes.val ++ application.val := by
  let first := Std.Array.to_slice prefixBytes
  have addFirst := FrameCodecWriteBytes.checked_add_some 0#usize first.len first.len (by simp only [UScalar.ofNatCore_val_eq, Nat.zero_add])
  have indices := AdapterSealFixedParts.indices2 first application
  obtain ⟨total, added, size⟩ := Transport.checked_add_exact first.len application.len
  dsimp only [first] at addFirst indices added size
  cases total with
  | none =>
      have stopped : simulateQ (RegistrationNativePlatformSourceSeal.handler (n := n) (Auxiliary := Auxiliary)
          coins setup codec view failure allocation) (AdapterSealNative.joined E prefixBytes application) = pure (.ok none) := by
        unfold AdapterSealNative.joined AdapterSealRequestMonad.Lifted.join
        simp only [AdapterSealJoinRequestExtraction.join, AdapterSealJoinRequestMonad.Lifted.index,
          AdapterSealJoinRequestMonad.Lifted.len, AdapterSealJoinRequestMonad.Lifted.checkedAdd,
          AdapterSealJoinRequestMonad.Lifted.branch, indices.1, indices.2,
          AdapterSealRequestMonad.Program.run_bind, AdapterSealRequestMonad.Program.run_lift,
          core.slice.Slice.len, rust_primitives.slice.slice_length, addFirst, added,
          core.option.Option.Insts.CoreOpsTry_traitTry.branch,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, pure_bind]
        rfl
      rw [stopped] at supported
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq] at supported
      cases supported.1.1
  | some capacity =>
      have length : prefixBytes.val.length + application.val.length = capacity.val := by
        simp only [Transport.absLength, Slice.len_val, Slice.length, Std.Array.to_slice] at size
        split_ifs at size with room
        exact (Option.some.inj size).symm
      rw [RegistrationNativePlatformJoinBytes.joined coins setup codec view failure allocation
        prefixBytes application capacity length before, StateT.run_map, support_map] at supported
      obtain ⟨⟨result, current⟩, allocated, equal⟩ := supported
      cases result with
      | fail error | div => cases equal
      | ok result => cases result with
        | Err error => cases equal
        | Ok success =>
            simp only [bind_tc_ok, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
            obtain ⟨⟨same, stateEq⟩, platformEq⟩ := equal
            subst current
            exact ⟨capacity, success, length, allocated, stateEq.symm, (congrArg Subtype.val same).symm⟩

private theorem aead_cut (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (plaintext : Slice U8) (associated : Std.Array U8 281#usize) (nonce : primitive.Nonce) (key : primitive.Key)
    (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (before after : State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (some (ciphertext, tag)), after), next) ∈ support
      (((simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
        (AdapterSealNative.aead E plaintext associated nonce key)).run before).run previous)) :
    ((.ok (.Ok (ciphertext, tag)), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext
        (some (Std.Array.to_slice associated)) nonce key).run before).run previous) := by
  simp only [AdapterSealNative.aead, simulateQ_map, simulateQ_spec_query,
    RegistrationNativePlatformSourceSeal.handler, StateT.run_map, support_map] at supported
  obtain ⟨⟨⟨result, current⟩, platform⟩, called, equal⟩ := supported
  cases result with
  | fail error | div => cases equal
  | ok result => cases result with
    | Err error => cases equal
    | Ok pair =>
        simp only [AdapterSealNative.finish, bind_tc_ok, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at equal
        obtain ⟨⟨same, stateEq⟩, platformEq⟩ := equal
        cases same
        cases stateEq
        cases platformEq
        exact called

omit primitive in
private theorem mark_cut
    (work : StateT (State n Auxiliary) (StateT Platform ProbComp) (RustM AdapterSealNative.Output))
    (request : record_effects.AeadSealRequest) (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (before after : State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (some (ciphertext, tag)), after), next) ∈ support (((do
      let result ← work
      modify fun current => RegistrationNativePlatformJoinBytes.marked request current
      pure result).run before).run previous)) :
    ∃ middle, ((.ok (some (ciphertext, tag)), middle), next) ∈ support ((work.run before).run previous) ∧
      after = RegistrationNativePlatformJoinBytes.marked request middle := by
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨result, middle⟩, platform⟩, called, returned⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  obtain ⟨⟨same, stateEq⟩, platformEq⟩ := returned
  cases same
  cases platformEq
  exact ⟨middle, called, stateEq⟩

def AllocationCut (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (plaintext : record_effects.SealPlaintextRequest) (before after : Platform) : Prop :=
  match plaintext with
  | .Single _ => after = before
  | .Prefixed prefixBytes application => ∃ capacity success,
      prefixBytes.val.length + application.val.length = capacity.val ∧
      (.ok (.Ok success), after) ∈ support ((allocation (Slice.new U8) capacity).run before)

/-- A successful actual source seal reaches the native AEAD with exactly the requested private key, nonce, AD and plaintext, after its literal public reservation. -/
theorem sealing (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (correct : view.Correct) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) (ciphertext : Slice U8) (tag : Std.Array U8 16#usize)
    (before after : State n Auxiliary) (previous next : Platform)
    (supported : ((.ok (some (ciphertext, tag)), after), next) ∈ support
      (((RegistrationNativePlatformSourceSeal.sealing coins setup codec view failure allocation request).run before).run previous)) :
    ∃ key nonce plaintext middle aeadState,
      AdapterSealRequestMonad.Lifted.key (m := RustM) request.key = .ok key ∧
      AdapterSealRequestMonad.Lifted.nonce (m := RustM) request.nonce = .ok nonce ∧
      AllocationCut allocation request.plaintext previous middle ∧
      RegistrationNativePlatformSourceSeal.input view plaintext (some (Std.Array.to_slice request.associated_data)) nonce key =
        RegistrationRecordPrimitives.sealInput request ∧
      ((.ok (.Ok (ciphertext, tag)), aeadState), next) ∈ support
        (((RegistrationNativePlatformSourceSeal.aead coins setup codec view failure plaintext
          (some (Std.Array.to_slice request.associated_data)) nonce key).run before).run middle) ∧
      after = RegistrationNativePlatformJoinBytes.marked request aeadState := by
  obtain ⟨aeadState, called, marked⟩ := mark_cut
    (simulateQ (RegistrationNativePlatformSourceSeal.handler coins setup codec view failure allocation)
      (AdapterSealNative.execute E request)) request ciphertext tag before after previous next supported
  unfold AdapterSealNative.execute at called
  cases keyRun : AdapterSealRequestMonad.Lifted.key (m := RustM) request.key with
  | fail error | div =>
      simp [keyRun, AdapterSealNative.continueWith, StateT.run_pure] at called
  | ok key =>
      simp only [keyRun, AdapterSealNative.continueWith] at called
      cases nonceRun : AdapterSealRequestMonad.Lifted.nonce (m := RustM) request.nonce with
      | fail error | div =>
          simp [nonceRun, StateT.run_pure] at called
      | ok nonce =>
          simp only [nonceRun] at called
          cases selected : request.plaintext with
          | Single plaintext =>
              rw [selected] at called
              have reached := aead_cut coins setup codec view failure allocation plaintext request.associated_data nonce key
                ciphertext tag before aeadState previous next called
              refine ⟨key, nonce, plaintext, previous, aeadState, rfl, rfl, rfl, ?_, reached, marked⟩
              unfold RegistrationNativePlatformSourceSeal.input RegistrationRecordPrimitives.sealInput
              rw [correct.1 request.key key keyRun, correct.2 request.nonce nonce nonceRun, selected]
              rfl
          | Prefixed prefixBytes application =>
              rw [selected] at called
              simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at called
              obtain ⟨⟨⟨result, joinedState⟩, platform⟩, joinedReached, continued⟩ := called
              cases result with
              | fail error | div =>
                  simp [StateT.run_pure] at continued
              | ok optional => cases optional with
                | none => simp [StateT.run_pure] at continued
                | some plaintext =>
                    obtain ⟨capacity, success, length, allocated, stateEq, bytes⟩ := joined coins setup codec view failure allocation
                      prefixBytes application plaintext before joinedState previous platform joinedReached
                    subst joinedState
                    have reached := aead_cut coins setup codec view failure allocation plaintext request.associated_data nonce key
                      ciphertext tag before aeadState platform next continued
                    refine ⟨key, nonce, plaintext, platform, aeadState, rfl, rfl, ?_, ?_, reached, marked⟩
                    · exact ⟨capacity, success, length, allocated⟩
                    · have plaintextEq : plaintext = (⟨prefixBytes.val ++ application.val, by
                          rw [List.length_append, length]; scalar_tac⟩ : Slice U8) := Subtype.ext bytes
                      rw [plaintextEq]
                      exact RegistrationNativePlatformJoinBytes.input_correct view correct request prefixBytes application
                        capacity length selected key nonce keyRun nonceRun

end BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt.joined' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt.joined

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSealReceipt.sealing
