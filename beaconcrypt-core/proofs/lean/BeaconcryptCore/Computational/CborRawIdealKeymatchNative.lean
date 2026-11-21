-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawNativePublic
import BeaconcryptCore.Computational.CborRawIdealBeaconTrace
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch

/-! The concrete native key trace permits independent registration and ordinary-record codecs. Public raw registration adaptation preserves accept and bundle witnesses, while every refused send is a complete-state quiet step. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchNative
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSlots (Coord SlotSpec slotCore detach attach)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg idealProg)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Entry Spec)
open PqxdhDeploymentIdealKeymatch
variable {ι KemSK Reader Response RecordReader RecordResponse : Type} {baseSpec : OracleSpec ι}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : Nat} (t : Target count) (p : Params KemSK count)

theorem mixed_handler_trace (recordCodec : Codec RecordReader RecordResponse) (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (transcript : List Entry) (x : XState KemSK (IdealBk TableState) 2)
    (trace : KeyTrace setup codec checks t p transcript x.base x.backend.2.2)
    (result : PqxdhDeploymentInterface.Spec.Range query × XState KemSK (IdealBk TableState) 2)
    (member : result ∈ support ((handlerWith setup recordCodec route (idealReg setup codec route checks t p created)
      query).run x)) :
    KeyTrace setup codec checks t p (transcript ++ [⟨.inl query, result.1⟩]) result.2.base result.2.backend.2.2 := by
  rcases query with coin | command
  · simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inl coin)) trivial _ rfl trace.owners rfl
      rfl
  · cases command with
    | create pin keyId =>
        have prog := idealReg_support setup codec route checks t p created ⟨.create pin keyId, trivial⟩ x result member
        obtain ⟨backend, sessions, owners⟩ := prog_create setup codec route checks t p _ created pin keyId _ _ prog
        replace owners := owners trace.owners
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.create pin keyId))) trivial _
          sessions owners (by rw [backend]) (by rw [backend])
    | bundle k =>
        have prog := idealReg_support setup codec route checks t p created ⟨.bundle k, trivial⟩ x result member
        obtain ⟨backend, sessions, keyed⟩ := prog_bundle setup codec route checks t p _ created k _ _ prog
        obtain ⟨owners, published⟩ := keyed trace.owners
        dsimp only [detach] at *
        change result.2.backend.2.2 = x.backend.2.2 at backend
        refine ⟨by rw [backend]; exact sessions.trans trace.sessions, fun raw s found => ?_, fun raw found => ?_,
          owners, fun k' bytes found => ?_⟩
        · rcases List.mem_append.mp found with old | new
          · rw [backend]; exact trace.below raw s old
          · cases List.mem_singleton.mp new
        · rcases List.mem_append.mp found with old | new
          · rw [backend]; exact trace.selected raw old
          · cases List.mem_singleton.mp new
        · rcases List.mem_append.mp found with old | new
          · exact trace.bundles k' bytes old
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            exact published bytes replies.symm
    | accept raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.accept raw, trivial⟩ x result member
        obtain ⟨accepts, sessions, owners, marks, returned⟩ := prog_accept setup codec route checks t p _ created raw _
          _ prog
        dsimp only [detach] at *
        change result.2.backend.2.2.accepts = x.backend.2.2.accepts + 1 at accepts
        change x.backend.2.2.accepts ≠ t.accept → result.2.backend.2.2.marks = x.backend.2.2.marks at marks
        refine ⟨by rw [accepts, sessions, trace.sessions], fun raw' s found => ?_, fun raw' found => ?_,
          by rw [owners]; exact trace.owners, fun k bytes found => ?_⟩
        · rcases List.mem_append.mp found with old | new
          · rw [accepts]; exact Nat.lt_succ_of_lt (trace.below raw' s old)
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            have back := (returned s replies.symm).1
            rw [accepts, back, trace.sessions]
            exact Nat.lt_succ_self _
        · rcases List.mem_append.mp found with old | new
          · have earlier := trace.below raw' t.accept old
            rw [marks (Nat.ne_of_gt earlier)]
            exact trace.selected raw' old
          · have same := List.mem_singleton.mp new
            injection same with queries replies
            injection queries with queries
            injection queries with queries
            injection queries with queries
            subst queries
            have back := returned t.accept replies.symm
            exact back.2 (by rw [← trace.sessions]; exact back.1.symm)
        · rcases List.mem_append.mp found with old | new
          · exact trace.bundles k bytes old
          · cases List.mem_singleton.mp new
    | build session payload =>
        have prog := idealReg_support setup codec route checks t p created ⟨.build session payload, trivial⟩ x result member
        obtain ⟨accepts, marks, sessions, owners⟩ := prog_build setup codec route checks t p _ created session payload _
          _ prog
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.build session payload))) trivial _ sessions
          (by rw [owners]; exact trace.owners) accepts marks
    | finish owner raw =>
        have prog := idealReg_support setup codec route checks t p created ⟨.finish owner raw, trivial⟩ x result member
        obtain ⟨accepts, marks, sessions, owners⟩ := prog_finish setup codec route checks t p _ created owner raw _ _ prog
        replace owners := owners trace.owners
        dsimp only [detach] at *
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.finish owner raw))) trivial _ sessions owners accepts marks
    | hmac key message =>
        have prog := idealReg_support setup codec route checks t p created ⟨.hmac key message, trivial⟩ x result member
        obtain ⟨backend, sessions, owners⟩ := prog_hmac setup codec route checks t p _ created key message _ _ prog
        dsimp only [detach] at *
        change result.2.backend.2.2 = x.backend.2.2 at backend
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.hmac key message))) trivial _ sessions
          (by rw [owners]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | hash bytes =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have lowered := onNative_native _ x.base result.1 result.2.base native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.hash bytes))) trivial _
          (reg_sessions setup recordCodec checks created.seed (.hash bytes) (fun _ same => by cases same) x.base.native
            (result.1, result.2.base.native) lowered)
          (by rw [reg_shared_owners setup recordCodec checks created.seed (.hash bytes) trivial x.base.native
            (result.1, result.2.base.native) lowered]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | serverSend keyId plaintext =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.serverStep_fields setup recordCodec route _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.serverSend keyId plaintext))) trivial _ fields.2.2.2.2.1
          (by rw [fields.1]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | serverRaw raw =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.serverStep_fields setup recordCodec route _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.serverRaw raw))) trivial _ fields.2.2.2.2.1
          (by rw [fields.1]; exact trace.owners) (by rw [backend]) (by rw [backend])
    | beaconSend owner plaintext =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.beaconStep_fields setup recordCodec owner _ x.base _ native
        have alike := PqxdhDeploymentEligibility.beaconStep_alike setup recordCodec owner _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.beaconSend owner plaintext))) trivial _ fields.2.2.2.2.1
          (poolOwners_alike _ _ _ alike trace.owners) (by rw [backend]) (by rw [backend])
    | beaconRaw owner raw =>
        obtain ⟨backend, native⟩ := onBase_support _ x result member
        have fields := PqxdhDeploymentNative.beaconStep_fields setup recordCodec owner _ x.base _ native
        have alike := PqxdhDeploymentEligibility.beaconStep_alike setup recordCodec owner _ x.base _ native
        exact keyTrace_quiet setup codec checks t p transcript _ _ _ _ trace (.inl (.inr (.beaconRaw owner raw))) trivial _ fields.2.2.2.2.1
          (poolOwners_alike _ _ _ alike trace.owners) (by rw [backend]) (by rw [backend])


end BeaconcryptCore.Computational.CborRawIdealKeymatchNative

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchNative.mixed_handler_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchNative.mixed_handler_trace
