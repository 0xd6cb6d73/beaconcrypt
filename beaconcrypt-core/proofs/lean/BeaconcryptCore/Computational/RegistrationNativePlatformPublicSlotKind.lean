-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedSafe
/-! A candidate-independent source monitor checks the constructor kind of every actual role installation against the immediately preceding raw material-demand reply. It stores only an optional public slot index and a mismatch bit, retaining every real query and reply. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind
open PqxdhRecordLiftInterface (Role KernelRef EnvEffects)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativePairedSafe (GlobalInstall)
variable {n : Nat} {KemSK A B : Type}

structure State (n : Nat) where
  pending : Option (Fin n)
  bad : Bool

def origin : KernelRef n → Option (Fin n)
  | .known _ => none
  | .hidden slot => some slot

def choiceOrigin : Choice n → Option (Fin n)
  | .known _ => none
  | .hidden reference => some reference.slot

def Fits : (Spec n KemSK).Domain → State n → Prop
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer _ _ kernel)))))), before => origin kernel = before.pending
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon _ _ kernel)))))), before => origin kernel = before.pending
  | _, _ => True
noncomputable instance (query : (Spec n KemSK).Domain) (before : State n) : Decidable (Fits query before) := Classical.propDecidable _

def update : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query → Option (Fin n) → Option (Fin n)
  | .inl (.inl _), _, _ => none
  | .inl (.inr (.inl (.inl _))), reply, _ => reply.bind choiceOrigin
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer ..)))))), _, _ => none
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon ..)))))), _, _ => none
  | _, _, previous => previous

noncomputable def step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : State n) : State n :=
  ⟨update query reply before.pending,before.bad || !decide (Fits query before)⟩

noncomputable def handler : QueryImpl (Spec n KemSK) (StateT (State n) (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply,step query reply before)) <$> (Spec n KemSK).query query

def Safe (work : OracleComp (Spec n KemSK) A) : Prop :=
  ∀ before result,before.bad=false → result ∈ support ((simulateQ handler work).run before) → result.2.bad=false

def Kernel (choice : Choice n) (kernel : KernelRef n) : Prop := origin kernel = choiceOrigin choice

def Effect (role : Role) (choice : Choice n) : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ kernel) => role=.server ∧ Kernel choice kernel
  | .inr (.installBeacon _ _ kernel) => role=.beacon ∧ Kernel choice kernel
  | _ => True

/-- Pure early failures retain the clean monitor state. -/
theorem pure_safe (value : A) : Safe (n := n) (KemSK := KemSK) (pure value) := by
  intro before result clean supported
  simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
  cases supported
  exact clean

/-- Adaptive source composition keeps the actual reached pending slot and mismatch bit. -/
theorem bind_safe (work : OracleComp (Spec n KemSK) A) (next : A → OracleComp (Spec n KemSK) B)
    (first : Safe work) (later : ∀ value,Safe (next value)) : Safe (work >>= next) := by
  intro before result clean supported
  simp only [simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨middle,called,continued⟩ := supported
  exact later middle.1 middle.2 result (first before middle clean called) continued

def Noninstall (query : (Spec n KemSK).Domain) : Prop := ∀ role,¬GlobalInstall (KemSK := KemSK) role query

private theorem fits_noninstall (request : (Spec n KemSK).Domain) (before : State n) (free : Noninstall (KemSK := KemSK) request) : Fits request before := by
  rcases request with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · trivial
  · trivial
  · trivial
  · rcases environment with coin | capability
    · trivial
    · cases capability with
      | installServer keyId binding kernel => exact (free .server rfl).elim
      | installBeacon owner shell kernel => exact (free .beacon rfl).elim
      | _ => trivial
  all_goals trivial

private theorem query_safe (request : (Spec n KemSK).Domain) (free : Noninstall (KemSK := KemSK) request) :
    Safe (liftM ((Spec n KemSK).query request) : OracleComp (Spec n KemSK) _) := by
  intro before result clean supported
  simp only [simulateQ_spec_query,handler,StateT.run,support_map] at supported
  obtain ⟨reply,_called,rfl⟩ := supported
  simp only [step,fits_noninstall request before free,decide_true,Bool.not_true,Bool.or_false,clean]

/-- Every genuinely noninstalling source program preserves clean kind matching, including arbitrary intervening demand, preparation and public coin replies. -/
theorem noninstall_safe (work : OracleComp (Spec n KemSK) A) (free : work.AllQueriesSatisfy (Noninstall (KemSK := KemSK))) : Safe work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe value
  | query_bind request next ih =>
      obtain ⟨first,later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp free
      exact bind_safe _ _ (query_safe request first) (fun reply => ih reply (later reply))

private theorem bound_noninstall (work : OracleComp (Spec n KemSK) A)
    (free : ∀ role,work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0) : work.AllQueriesSatisfy (Noninstall (KemSK := KemSK)) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind request next ih =>
      have receipt := fun role => (isQueryBoundP_query_bind_iff _ _ _ _).mp (free role)
      refine ⟨fun role => (receipt role).1.resolve_right (by omega),?_⟩
      intro reply
      exact ih reply (fun role => by simpa only [Nat.zero_sub,ite_self] using (receipt role).2 reply)

/-- Zero actual installation bills for both roles imply monitor safety without an assumption about the pending slot. -/
theorem free_safe (work : OracleComp (Spec n KemSK) A)
    (free : ∀ role,work.IsQueryBoundP (GlobalInstall (KemSK := KemSK) role) 0) : Safe work :=
  noninstall_safe work (bound_noninstall work free)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.pure_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.bind_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.bind_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.noninstall_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.noninstall_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.free_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotKind.free_safe
