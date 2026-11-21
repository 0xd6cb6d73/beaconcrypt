-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourcePersistence
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape

/-! Internal live-root preservation follows from actual native session insertion, private preparation receipts and source memo persistence. No public eligibility event is narrowed by a cache or successful-prepare assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceLive
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceState (Live MemoCorrect)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativePublicSourceServer (State run layout)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationAuthenticationCompiler.program

private theorem server_roots (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((run setup wire route sign seed scalar selected work).run before)) :
    MemoCorrect setup seed scalar result.2.2.roots ∧
      ∀ message root, before.2.roots message = some root → result.2.2.roots message = some root := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (RegistrationNativePublicSourceEffects.close setup seed scalar
      (simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign)
        ((RegistrationNativePublicFrontend.serverOpen selected work).run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativePublicSourcePersistence.program_stable setup wire route sign seed scalar
    ((RegistrationNativePublicFrontend.serverOpen selected work).run before.1) before.2 inner correct reached

/-- Native successful insertion and all failed accept paths preserve the internal live-root invariant, with exact source memo correctness. -/
theorem accept_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (selected : Bool) (packet : registration.InitPacket)
    (before : State n KemSK source) (result : RustM (Option Nat) × State n KemSK source)
    (live : Live before.1 before.2) (correct : MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((run setup wire route sign seed scalar selected
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    Live result.2.1 result.2.2 ∧ MemoCorrect setup seed scalar result.2.2.roots := by
  obtain ⟨afterCorrect, kept⟩ := server_roots setup wire route sign seed scalar selected
    (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet) before result correct supported
  have reached : (result.1, layout result.2) ∈ support
      ((RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run (layout before)) := by
    rw [← RegistrationNativePublicSourceServer.server_layout setup wire route sign seed scalar selected, support_map]
    exact ⟨result, supported, rfl⟩
  have shape := RegistrationServerOpenReferenceSessionShape.accept setup checks verify seed scalar remember
    (services setup wire route sign seed scalar) packet (layout before) (result.1, layout result.2) reached
  change RegistrationServerOpenReferenceSessionShape.Shape before.1.server.sessions result.1 result.2.1.server.sessions at shape
  refine ⟨?_, afterCorrect⟩
  intro ready member
  rcases shape with unchanged | ⟨appended, replied, sessions⟩
  · rw [unchanged] at member
    obtain ⟨root, stored⟩ := live ready member
    exact ⟨root, kept ready.reference root stored⟩
  · simp only [sessions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with previous | same
    · obtain ⟨root, stored⟩ := live ready previous
      exact ⟨root, kept ready.reference root stored⟩
    · cases same
      have success : (.ok (some before.1.server.sessions.length), result.2) ∈ support
          ((run setup wire route sign seed scalar selected
            (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before) := by
        have equal : result = (.ok (some before.1.server.sessions.length), result.2) := by
          rw [← replied]
        rw [← equal]
        exact supported
      obtain ⟨actual, root, stored, memo, _computed⟩ := RegistrationNativePublicSourceMemo.accept_receipt
        setup wire checks route sign verify seed scalar selected packet before.1.server.sessions.length before result.2 success
      have last : result.2.1.server.sessions[before.1.server.sessions.length]? = some (some ready) := by
        rw [sessions]
        simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]
      rw [last] at stored
      cases stored
      exact ⟨root, memo⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourceLive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceLive.accept_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceLive.accept_live
