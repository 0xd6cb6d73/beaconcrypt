-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCertified

/-! Structural support transport connects the literal initialized prephase to the saved callback's every-reply resource certificates. It applies under arbitrary ordinary CCA replies and arbitrary public challenge keys. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport
open PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemCutBounds
variable {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ} {State Result : Type}

/-- Any successful optional simulated result came from the original oracle program; stopping may remove results but cannot invent a callback. Full reached state is allowed and retained in the premise. -/
theorem successful_support (impl : QueryImpl source (OptionT (StateT State (OracleComp target))))
    (work : OracleComp source Result) (before after : State) (result : Result)
    (reached : (some result, after) ∈ support (((simulateQ impl work).run).run before)) :
    result ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
      Option.some.injEq] at reached
    exact (mem_support_pure_iff _ _).mpr reached.1
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at reached
    obtain ⟨⟨answer, middle⟩, _, reached⟩ := reached
    cases answer with
    | none => simp at reached
    | some answer =>
      exact (mem_support_bind_iff _ _ _).mpr ⟨answer, mem_support_query query answer,
        ih answer middle after reached⟩

variable {KemSK Reader Response A : Type} {baseSpec : OracleSpec ι}

/-- Every active cut keeps an all-reply bound for the original remaining source program; failed initialization and a stopped/complete prefix need no continuation allowance. -/
def ContextBound (predicate : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain → Prop)
    [DecidablePred predicate] (cap : Nat) {count : Nat} : Context KemSK A Result count → Prop
  | .ready _ _ (some cut) _ _ => Residual predicate cap cut
  | _ => True

/-- The exact executable initialized prephase supplies the saved all-reply continuation bound from the actual source command compiler, independently of the challenge key's origin or any oracle reply. -/
theorem pre_bound (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Result) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat) (challengeKey : PqxdhKemIndCca.MlKem768PublicKey)
    (predicate : (PqxdhRegistrationJointKemEncapsulation.Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (cap : Nat)
    (bounded : ∀ created : PqxdhRegistrationJointServerBirth.ClientCreated Unit,
      (PqxdhRegistrationJointKemEncapsulation.commands setup codec checks
        created.server.server.metadata.identityIndex created.publicIdentity client []
        (PqxdhRegistrationJointInitializedAccept.initial created)).IsQueryBoundP predicate cap)
    (context : Context KemSK A Result count)
    (reached : context ∈ support (pre setup codec checks ensureInit supplied client runtime count selected occurrence challengeKey)) :
    ContextBound predicate cap context := by
  unfold pre at reached
  rw [mem_support_bind_iff] at reached
  obtain ⟨⟨born, after⟩, _, reached⟩ := reached
  cases born with
  | none =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    trivial
  | some created =>
    rw [mem_support_bind_iff] at reached
    obtain ⟨others, _, reached⟩ := reached
    rw [mem_support_bind_iff] at reached
    obtain ⟨⟨cut, state⟩, scanned, reached⟩ := reached
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    cases cut with
    | none => trivial
    | some cut =>
      exact residual setup _ occurrence predicate cap (bounded created) cut
        (successful_support _ _ _ state cut scanned)

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport.successful_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport.successful_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport.pre_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutSupport.pre_bound
