-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedSafe

/-! The raw Server material controller derives paired provenance before any current-environment publication compilation. Its demand retains arbitrary known or hidden Choice replies, and its complete actual public branch uses only the returned hidden slot. All native lookup, cancellation and failure paths remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordMessage (Message ServerState ServerReady)
open RegistrationNativePairedMaterialSource (wordLift)
open RegistrationNativeSecretWordPairedTrace (Safe handler step)
open RegistrationNativeSecretWordAtomInstallPredicate (GlobalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (Install)
open RegistrationNativeSecretWordAtomInstallTrace (RootFree)
variable {n : Nat} {KemSK Value : Type}

private def commonLift : QueryImpl (RegistrationNativePairedServerService.Common n) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inl (.inr (.inl (.inr query))))

private theorem common_bound (role : PqxdhRecordLiftInterface.Role)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (Install role) cap) :
    (simulateQ (commonLift (KemSK := KemSK)) work).IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  simp [commonLift, GlobalInstall, isQueryBoundP_query_iff]
  intro counted
  rw [ite_eq_left counted]
  decide

private theorem common_quiet (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    (simulateQ (commonLift (KemSK := KemSK)) work).IsQueryBoundP (fun query => ¬RootFree (KemSK := KemSK) query) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [commonLift, RootFree, isQueryBoundP_query_iff]

private theorem common_allowed (choice : RegistrationNativePairedChoice.Choice n)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value)
    (allowed : AllQueriesSatisfy work (RegistrationNativePairedProvenance.Allowed .server choice)) :
    AllQueriesSatisfy (simulateQ (commonLift (KemSK := KemSK)) work)
      (RegistrationNativeSecretWordPairedSafe.Allowed (KemSK := KemSK) .server choice) := by
  apply RegistrationNativeHiddenAllocationCore.simulation _ _ _ _ work allowed
  intro query valid
  cases query with
  | inl publication => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  | inr environment => exact (allQueriesSatisfy_query_iff _ _).mpr valid

private theorem common_program (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    simulateQ (wordLift (KemSK := KemSK)) (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work) =
      simulateQ commonLift work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-- The actual raw Server material stage checks its own returned hidden slot against the same demanded descriptor. -/
theorem admitted (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial) (message : Message) :
    Safe (simulateQ (wordLift (KemSK := KemSK))
      (RegistrationNativeSecretWordServerMaterial.admitted (n := n) encode control initial message)) := by
  intro before result clean supported
  rw [RegistrationNativeSecretWordServerMaterial.admitted, simulateQ_bind, simulateQ_spec_query] at supported
  simp only [wordLift, QueryImpl.compose, RegistrationNativeSecretWordInterface.paired,
    RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query] at supported
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _possible, continued⟩ := supported
  cases chosen with
  | none =>
      exact RegistrationNativeSecretWordPairedTrace.pure_safe _ _ result
        (by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean]) continued
  | some choice =>
      change result ∈ support ((simulateQ handler (simulateQ (wordLift (KemSK := KemSK))
        (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift
          (RegistrationNativePairedServerService.publicBranch encode control initial choice)))).run
            (step (.inl (.inr (.inl (.inl message)))) (some choice) before)) at continued
      rw [common_program] at continued
      exact RegistrationNativeSecretWordPairedSafe.suffix .server choice message _ 1 (by omega)
        ((common_bound .server _ _ (RegistrationNativeSecretWordAtomInstallCaps.server_branch .server encode control initial choice)).mono (by simp))
        (common_quiet _) (common_allowed choice _ (RegistrationNativePairedProvenance.server_branch encode control initial choice))
        (step (.inl (.inr (.inl (.inl message)))) (some choice) before)
        ⟨by simp only [step, RegistrationNativeSecretWordPairedTrace.Fits, decide_true, Bool.not_true, Bool.or_false, clean], Or.inr ⟨rfl, rfl⟩⟩ result continued

private theorem finish (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes)) (before : ServerState) :
    Safe (simulateQ (wordLift (n := n) (KemSK := KemSK)) ((RegistrationNativeSecretWordServerMaterial.finish published).run before)) := by
  cases published with
  | fail error | div => simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | ok published =>
      cases published <;> simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, simulateQ_pure]
      all_goals exact RegistrationNativeSecretWordPairedTrace.pure_safe _

attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

/-- The complete raw native preflight and occupancy controller preserves paired provenance on every continuation. -/
theorem complete (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (ready : ServerReady)
    (application : Slice U8) (before : ServerState) :
    Safe (simulateQ (wordLift (n := n) (KemSK := KemSK))
      ((RegistrationNativeSecretWordServerMaterial.complete wire reservePeer ready application).run before)) := by
  simp only [RegistrationNativeSecretWordServerMaterial.complete, StateT.run]
  split <;> try (rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  split <;> try (rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  split <;> try (rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
  rw [simulateQ_bind]
  apply RegistrationNativeSecretWordPairedTrace.bind_safe
  · apply RegistrationNativeSecretWordPairedSafe.free
    intro role
    simp [RegistrationNativeSecretWordServerMaterial.effect, wordLift, QueryImpl.compose,
      RegistrationNativeSecretWordInterface.paired, RegistrationNativeSecretWordInterface.liftLocal,
      GlobalInstall, Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]
  · intro occupied
    split <;> try (rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _)
    rw [simulateQ_bind]
    apply RegistrationNativeSecretWordPairedTrace.bind_safe
    · unfold RegistrationNativeSecretWordServerMaterial.adHash
      split
      · rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
      · rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
      · rw [simulateQ_bind]
        apply RegistrationNativeSecretWordPairedTrace.bind_safe
        · apply RegistrationNativeSecretWordPairedSafe.free
          intro role
          simp [RegistrationNativeSecretWordServerMaterial.effect, wordLift, QueryImpl.compose,
            RegistrationNativeSecretWordInterface.paired, RegistrationNativeSecretWordInterface.liftLocal,
            GlobalInstall, Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]
        · intro digest
          rw [simulateQ_pure]
          exact RegistrationNativeSecretWordPairedTrace.pure_safe _
    · intro hashed
      cases hashed with
      | fail error | div => rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
      | ok reply => cases reply with
        | Err previous => rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
        | Ok initial =>
          dsimp only
          split
          · rw [simulateQ_bind]
            exact RegistrationNativeSecretWordPairedTrace.bind_safe _ _
              (admitted wire.encodeResponse before.control _ ready.reference) (fun published => finish published before)
          · rw [simulateQ_pure]
            exact RegistrationNativeSecretWordPairedTrace.pure_safe _

/-- Raw build consumes the same one-use Ready and preserves paired provenance for every application cancellation or native completion branch. -/
theorem build (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : ServerState) :
    Safe (simulateQ (wordLift (n := n) (KemSK := KemSK))
      ((RegistrationNativeSecretWordServerMaterial.build wire reservePeer handle application).run before)) := by
  simp only [RegistrationNativeSecretWordServerMaterial.build, StateT.run]
  rcases RegistrationNativeSecretWordServerMaterial.take handle before with ⟨chosen, after⟩
  cases chosen with
  | none => rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
  | some ready => cases application with
    | none => rw [simulateQ_pure]; exact RegistrationNativeSecretWordPairedTrace.pure_safe _
    | some application => exact complete wire reservePeer ready application after

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPairedRawServer.build
