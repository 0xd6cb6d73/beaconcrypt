-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderExecution
import BeaconcryptCore.Computational.RegistrationNativeProviderMemoReceipt
import BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFrontend

/-! Actual same-provider acceptance derives its internal live-root invariant. Existing capabilities retain their source-correct memo entries, and the sole newly retained capability carries the root recorded by its actual preparation. No public event requires an external live-token or preparation premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderLive
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (FrontState execute localImpl)
open RegistrationNativePublicSourceState (Live MemoCorrect)
attribute [local irreducible] RegistrationNativeProviderSource.localImpl
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every failed or successful actual accept preserves source-correct roots for all live capabilities under the same arbitrary KEM provider. -/
theorem accept_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (verify : MldsaTranscriptAuth.Verify) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (packet : registration.InitPacket) (before : FrontState n KemSK ProviderState source)
    (result : RustM (Option Nat) × FrontState n KemSK ProviderState source)
    (live : Live before.1 before.2.1) (correct : MemoCorrect setup seed scalar before.2.1.roots)
    (supported : result ∈ support
      ((execute setup wire route sign seed scalar provider
        (RegistrationNativePublicFrontend.serverOpen selected
          (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet))).run before)) :
    Live result.2.1 result.2.2.1 ∧ MemoCorrect setup seed scalar result.2.2.1.roots := by
  obtain ⟨afterCorrect, kept⟩ := RegistrationNativeProviderExecution.roots setup wire route sign seed scalar provider
    (RegistrationNativePublicFrontend.serverOpen selected
      (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)) before result correct supported
  rw [RegistrationNativeProviderAcceptFrontend.serverOpen_run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  cases equal
  have shape := RegistrationNativeProviderSessionShape.accept
    (localImpl setup wire route sign seed scalar provider selected) setup checks verify packet
    (RegistrationNativeProviderAcceptFrontend.unpack before) inner reached
  change RegistrationServerOpenReferenceSessionShape.Shape before.1.server.sessions inner.1 inner.2.1.sessions at shape
  refine ⟨?_, afterCorrect⟩
  intro ready member
  change some ready ∈ inner.2.1.sessions at member
  rcases shape with unchanged | ⟨appended, replied, sessions⟩
  · rw [unchanged] at member
    obtain ⟨root, stored⟩ := live ready member
    exact ⟨root, kept ready.reference root stored⟩
  · simp only [sessions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with previous | same
    · obtain ⟨root, stored⟩ := live ready previous
      exact ⟨root, kept ready.reference root stored⟩
    · cases same
      have success : (.ok (some before.1.server.sessions.length), inner.2) ∈ support
          ((RegistrationNativeProviderAcceptRun.close (localImpl setup wire route sign seed scalar provider selected)
            (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run
              (RegistrationNativeProviderAcceptFrontend.unpack before)) := by
        change (inner.1, inner.2) ∈ support _ at reached
        simpa only [replied] using reached
      obtain ⟨actual, root, stored, memo, _computed⟩ := RegistrationNativeProviderMemoReceipt.accept
        setup checks wire route sign verify seed scalar provider selected packet before.1.server.sessions.length
          (RegistrationNativeProviderAcceptFrontend.unpack before) inner.2 success
      have last : inner.2.1.sessions[before.1.server.sessions.length]? = some (some ready) := by
        rw [sessions]
        simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]
      rw [last] at stored
      cases stored
      exact ⟨root, memo⟩

end BeaconcryptCore.Computational.RegistrationNativeProviderLive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLive.accept_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLive.accept_live
