-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCutInterpreted

/-! A saved source cut carries resource facts proved from the same executable prephase. These erased facts bound every postchallenge reply without changing source behavior or consulting an unavailable selected secret. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills
open PqxdhRegistrationJointKemChallenge PqxdhRegistrationJointKemCutBounds
open PqxdhRegistrationJointKemCutSupport PqxdhRegistrationJointKemProgramBills
open PqxdhDynamicKemJointBounds (IsIdentityCreate IsDecapsulation IsUniform)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

structure Certificate {count : Nat} (context : Context KemSK A Result count)
    (qCreate qD qUniform qEncap : Nat) : Prop where
  creates : ContextBound (Count (KemSK := KemSK) IsIdentityCreate) qCreate context
  decaps : ContextBound (Count (KemSK := KemSK) IsDecapsulation) qD context
  uniform : ContextBound (Count (KemSK := KemSK) IsUniform) qUniform context
  encaps : ContextBound (PqxdhRegistrationJointKemExposedCounts.IsEncapsulation (KemSK := KemSK)) qEncap context

/-- Every valid saved adversary context has all four source-derived resource certificates. The proof uses its exact executable prephase support at its recorded arbitrary public key. -/
theorem saved (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (checks : PqxdhServerAuthExperiment.Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (client : OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Bool) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (occurrence : Nat)
    (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (context : PqxdhRegistrationJointKemCertified.Saved setup codec checks ensureInit supplied client runtime count selected occurrence) :
    Certificate context.2.val (budget (.inl 1)) (budget (.inl 5))
      (PqxdhRegistrationJointOpenUniform.total caps budget) (budget (.inl 3)) := by
  have bills (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :=
    commands setup codec checks caps bounded created.server.server.metadata.identityIndex created.publicIdentity
      client budget certified [] (PqxdhRegistrationJointInitializedAccept.initial created)
  constructor
  · exact pre_bound setup codec checks ensureInit supplied client runtime count selected occurrence context.1
      _ _ (fun created => (bills created).creates) context.2.val context.2.property
  · exact pre_bound setup codec checks ensureInit supplied client runtime count selected occurrence context.1
      _ _ (fun created => (bills created).decaps) context.2.val context.2.property
  · exact pre_bound setup codec checks ensureInit supplied client runtime count selected occurrence context.1
      _ _ (fun created => (bills created).uniform) context.2.val context.2.property
  · exact pre_bound setup codec checks ensureInit supplied client runtime count selected occurrence context.1
      _ _ (fun created => (bills created).encaps) context.2.val context.2.property

/-- The exact remaining source program inherits every cap for every possible candidate reply; no source state or prior callback is reconstructed. -/
theorem pending {count : Nat} (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (request : PqxdhRegistrationJointKemCut.Request)
    (next : PqxdhRegistrationJointKemCut.Reply → OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK)
      (PqxdhRegistrationJointKemCommands.Outcome KemSK Result))
    (state : PqxdhDynamicKemJointSource.State KemSK) (runtime : A)
    (qCreate qD qUniform qEncap : Nat)
    (certificate : Certificate (Context.ready created others (some (.pending request next)) state runtime)
      qCreate qD qUniform qEncap) (reply : PqxdhRegistrationJointKemCut.Reply) :
    Bounds (next reply) qCreate qD qUniform qEncap :=
  ⟨certificate.creates reply, certificate.decaps reply, certificate.uniform reply, certificate.encaps reply⟩

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills.saved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills.saved

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills.pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemSavedBills.pending
