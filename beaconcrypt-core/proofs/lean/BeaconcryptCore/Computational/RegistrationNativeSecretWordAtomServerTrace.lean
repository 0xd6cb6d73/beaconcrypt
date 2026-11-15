-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomCommonTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomSessionCredit

/-! The actual Server material request establishes its same descriptor in the analysis trace before publication or insertion. The compiled material branch can attempt its role once; failure to obtain material cannot issue an insertion. The preexisting trace is retained exactly, including a stale prior current descriptor. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordMessage (Message ServerState ServerReady)
open RegistrationNativeSecretWordInterface (Spec liftLocal)
open RegistrationNativeSecretWordFrontendTrace (State handler begin finish)
open RegistrationNativeSecretWordAtomInstallTrace (atom count)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {KemSK Value : Type}

def compile (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value) (before : Environment) :
    OracleComp (Spec n KemSK) (Value × Environment) :=
  simulateQ (liftLocal selected)
    ((simulateQ (RegistrationNativeSecretWordServerCompiler.service source wire sign) work).run before)

private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem compile_pure (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (value : Value) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (pure value) before = pure (value, before) := by
  simp only [compile, simulateQ_pure, StateT.run_pure]

private theorem compile_bind {Next : Type} (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Value)
    (next : Value → OracleComp (RegistrationNativeSecretWordInterface.WordPairedPublicSpec n) Next) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (work >>= next) before = (do
      let result ← compile selected source wire sign work before
      compile selected source wire sign (next result.1) result.2) := by
  simp only [compile, simulateQ_bind, StateT.run_bind]

private theorem compile_effect (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign (RegistrationNativeSecretWordServerMaterial.effect query) before =
      (fun reply => (reply, before)) <$> ((Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr query))))) : OracleComp (Spec n KemSK) _) := by
  simp only [compile, RegistrationNativeSecretWordServerMaterial.effect, simulateQ_spec_query,
    RegistrationNativeSecretWordServerCompiler.service, RegistrationNativeCommonCompiler.common, StateT.run_lift,
    bind_pure_comp, simulateQ_map, RegistrationNativeSecretWordInterface.effect, liftLocal]
  rfl

private theorem pure_count (role : Role) (value : Value) (before : State) (result : Value × State)
    (supported : result ∈ support ((simulateQ (handler (n := n) (KemSK := KemSK)) (pure value)).run before)) :
    count role result.2 ≤ count role before := by
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact Nat.le_refl _

private theorem common_compile (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign
      (simulateQ RegistrationNativeSecretWordServerMaterial.commonLift work) before =
      RegistrationNativeSecretWordAtomCommonTrace.compile selected source wire.frameWrite sign work before := by
  unfold compile RegistrationNativeSecretWordAtomCommonTrace.compile
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeSecretWordServerCompiler.service (n := n) (KemSK := KemSK) source wire sign ∘ₛ
      RegistrationNativeSecretWordServerMaterial.commonLift =
      RegistrationNativeCommonCompiler.common RegistrationNativeSecretWordInterface.effect source wire.frameWrite sign := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativeSecretWordServerMaterial.commonLift,
      simulateQ_spec_query, RegistrationNativeSecretWordServerCompiler.service]
  rw [same]

private theorem admitted_run (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : Message) (before : Environment) :
    compile (n := n) (KemSK := KemSK) selected source wire sign
      (RegistrationNativeSecretWordServerMaterial.admitted wire.encodeResponse control initial reference) before = (do
        let chosen ← ((Spec n KemSK).query (.inl (.inr (.inl (.inl reference)))) : OracleComp (Spec n KemSK) (Option (RegistrationNativePairedChoice.Choice n)))
        match chosen with
        | none => pure (.ok (.Err control), before)
        | some choice => RegistrationNativeSecretWordAtomCommonTrace.compile selected source wire.frameWrite sign (RegistrationNativePairedServerService.publicBranch wire.encodeResponse control initial choice) before) := by
  simp only [compile, RegistrationNativeSecretWordServerMaterial.admitted, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, RegistrationNativeSecretWordServerCompiler.service, StateT.run_lift, bind_pure_comp,
    simulateQ_bind, RegistrationNativeSecretWordInterface.demand, liftLocal, simulateQ_spec_query, bind_map_left]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => simp only [simulateQ_pure, StateT.run_pure]
  | some choice => exact common_compile selected source wire sign _ before

/-- The actual material demand is the same descriptor recorded by every later own-role attempt, with at most one such attempt. -/
theorem admitted (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : Message) (before : Environment) (trace : State)
    (result : (RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes) × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) selected source wire sign
      (RegistrationNativeSecretWordServerMaterial.admitted wire.encodeResponse control initial reference) before)).run trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * atom (some reference) := by
  rw [admitted_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, begin, finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _possible, continued⟩ := supported
  cases chosen with
  | none =>
      change result ∈ support (pure ((.ok (.Err control), before), ⟨some reference, trace.events ++ [.demand reference]⟩) : OracleComp (Spec n KemSK) _) at continued
      rw [mem_support_pure_iff] at continued
      cases continued
      simp only [count, List.countP_append, List.countP_singleton,
        RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero]
      omega
  | some choice =>
      change result ∈ support ((simulateQ handler (RegistrationNativeSecretWordAtomCommonTrace.compile selected source wire.frameWrite sign (RegistrationNativePairedServerService.publicBranch wire.encodeResponse control initial choice) before)).run ⟨some reference, trace.events ++ [.demand reference]⟩) at continued
      have bounded := RegistrationNativeSecretWordAtomCommonTrace.server role selected source wire.frameWrite sign
        wire.encodeResponse control initial choice before ⟨some reference, trace.events ++ [RegistrationNativeSecretWordFrontendTrace.Event.demand reference]⟩ result continued
      simpa only [count, List.countP_append, List.countP_singleton,
        RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero] using bounded.2

private theorem finish_count (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : ServerState) (env : Environment) (trace : State)
    (result : ((RegistrationNativeSecretWordServerMaterial.Result × ServerState) × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.finish published).run before) env)).run trace)) :
    count role result.2 ≤ count role trace := by
  cases published with
  | fail error | div =>
      simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, compile_pure] at supported
      exact pure_count role _ trace result supported
  | ok published =>
      cases published <;> simp only [RegistrationNativeSecretWordServerMaterial.finish, StateT.run, compile_pure] at supported
      all_goals exact pure_count role _ trace result supported

/-- The actual shared transcript hash preserves the complete analysis trace and its current descriptor. It still emits its public hash effect. -/
private theorem adHash_trace (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (pending : registration.ServerAdHash) (before : Environment) (trace : State)
    (result : (RegistrationServerAdHash.Result × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) selected source wire sign
      (RegistrationNativeSecretWordServerMaterial.adHash pending) before)).run trace)) :
    result.2 = trace := by
  unfold RegistrationNativeSecretWordServerMaterial.adHash at supported
  cases requested : pending.request with
  | fail error | div =>
      simp only [requested, compile_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok request =>
      simp only [requested] at supported
      rw [compile_bind, compile_effect, simulateQ_bind, StateT.run_bind] at supported
      simp only [simulateQ_map, StateT.run, map_apply, simulateQ_spec_query, handler, begin, finish,
        bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨digest, _queried, supported⟩ := supported
      simp only [compile_pure, simulateQ_pure] at supported
      cases supported
      rfl

attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

/-- Native lookup, preflight and reservation can only skip the actual material stage; its own descriptor bounds every later role attempt. -/
theorem complete (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePeer : Bool) (ready : ServerReady) (application : Slice U8)
    (before : ServerState) (env : Environment) (trace : State)
    (result : ((RegistrationNativeSecretWordServerMaterial.Result × ServerState) × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.complete wire reservePeer ready application).run before) env)).run trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * atom (some ready.reference) := by
  simp only [RegistrationNativeSecretWordServerMaterial.complete, StateT.run] at supported
  split at supported <;> try (rw [compile_pure] at supported; have same := pure_count role _ trace result supported; omega)
  split at supported <;> try (rw [compile_pure] at supported; have same := pure_count role _ trace result supported; omega)
  split at supported <;> try (rw [compile_pure] at supported; have same := pure_count role _ trace result supported; omega)
  rw [compile_bind, compile_effect, simulateQ_bind, bind_apply] at supported
  simp only [simulateQ_map, map_apply, simulateQ_spec_query, handler, begin, finish,
    bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨occupied, _possible, continued⟩ := supported
  split at continued <;> try (rw [compile_pure] at continued; have same := pure_count role _ trace result continued; omega)
  rw [compile_bind, simulateQ_bind, bind_apply, mem_support_bind_iff] at continued
  obtain ⟨hashed, hashSupport, continued⟩ := continued
  have unchanged := adHash_trace selected source wire sign _ env trace hashed hashSupport
  rcases hashed with ⟨⟨reply, reachedEnv⟩, reachedTrace⟩
  dsimp only at unchanged
  subst reachedTrace
  cases reply with
  | fail error | div =>
      rw [compile_pure] at continued
      have same := pure_count role _ trace result continued
      omega
  | ok answer => cases answer with
    | Err previous =>
        rw [compile_pure] at continued
        have same := pure_count role _ trace result continued
        omega
    | Ok initial =>
        dsimp only at continued
        split_ifs at continued with reserved
        · rw [compile_bind, simulateQ_bind, bind_apply, mem_support_bind_iff] at continued
          obtain ⟨published, material, finished⟩ := continued
          have first := admitted role selected source wire sign before.control _ ready.reference reachedEnv trace published material
          have last := finish_count role selected source wire sign published.1.1 before published.1.2 published.2 result finished
          exact last.trans first
        · rw [compile_pure] at continued
          have same := pure_count role _ trace result continued
          omega

/-- The actual build takes its one-use Ready before all cancellations and subsequent callbacks; only that moved Ready can fund an atom installation attempt. -/
theorem build (role : Role) (selected : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8))
    (before : ServerState) (env : Environment) (trace : State)
    (result : ((RegistrationNativeSecretWordServerMaterial.Result × ServerState) × Environment) × State)
    (supported : result ∈ support ((simulateQ handler (compile (n := n) (KemSK := KemSK) selected source wire sign
      ((RegistrationNativeSecretWordServerMaterial.build wire reservePeer handle application).run before) env)).run trace)) :
    count role result.2 ≤ count role trace + (if role = .server then 1 else 0) *
      RegistrationNativeSecretWordAtomSessionCredit.weight (RegistrationNativeSecretWordServerMaterial.take handle before).1 := by
  simp only [RegistrationNativeSecretWordServerMaterial.build, StateT.run] at supported
  rcases formed : RegistrationNativeSecretWordServerMaterial.take handle before with ⟨chosen, after⟩
  rw [formed] at supported
  change count role result.2 ≤ count role trace + (if role = .server then 1 else 0) * RegistrationNativeSecretWordAtomSessionCredit.weight chosen
  cases chosen with
  | none =>
      rw [compile_pure] at supported
      simpa only [RegistrationNativeSecretWordAtomSessionCredit.weight, Nat.mul_zero, Nat.add_zero] using pure_count role _ trace result supported
  | some ready =>
      cases application with
      | none =>
          rw [compile_pure] at supported
          have same := pure_count role _ trace result supported
          omega
      | some application =>
          have bounded := complete role selected source wire sign reservePeer ready application after env trace result supported
          have word : atom (some ready.reference) = RegistrationNativeSecretWordAtomSessionCredit.weight (some ready) := by
            cases formed : ready.reference.kem <;> simp only [atom, RegistrationNativeSecretWordAtomSessionCredit.weight, formed]
          simpa only [word] using bounded

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerTrace.build
