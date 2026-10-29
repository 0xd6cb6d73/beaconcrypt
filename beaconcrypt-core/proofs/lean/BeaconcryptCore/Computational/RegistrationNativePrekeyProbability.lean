-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePrekeySplit
import BeaconcryptCore.Computational.RegistrationNativeStartupTargets

/-! The real-source origin loss is paid once outside the sole canonical parsed-accept by owner sum. Every term of that sum carries the same public prekey equality in its decision, ready for literal transport through later computational hops. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePrekeyProbability
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Budget)
open PqxdhEd25519EufCma (Ed25519PublicKey)
open RegistrationNativeStartupTargets (outcome profile_outcome)
open RegistrationNativePrekeyEvents (GoodAt)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- A successful original native startup produces either a real source origin event or a canonical target with its literal public prekey equality. -/
theorem outcome_split (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : some observed ∈ support (outcome setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary))
    (winning : RegistrationNativeEvents.CEAppWin setup.source.crypto wire serverKeyId budget claim observed) :
    RegistrationNativeIdentityOriginEvents.Changed setup.joint wire observed.2.1.transcript observed.2.2.beacons ∨
      ∃ target : Fin budget.accept × Fin budget.capacity, GoodAt setup.source.crypto wire serverKeyId budget target claim observed := by
  simp only [outcome, mem_support_bind_iff] at supported
  obtain ⟨initialized, started, continued⟩ := supported
  cases initialized with
  | none => simp only [support_pure, Set.mem_singleton_iff, reduceCtorEq] at continued
  | some initial =>
      simp only [support_map, Set.mem_image, Option.some.injEq] at continued
      obtain ⟨actual, reached, rfl⟩ := continued
      have sender := (RegistrationNativeKemCandidateStartup.start_facts setup source ensureInit identityIndex serverKeyId initial started).2.2
      rw [← sender] at winning ⊢
      rcases RegistrationNativePrekeySplit.ceapp_split setup checks wire route representation initial.created initial.credential readback shortRejects bounds .P
        (adversary initial.public) initial.state budget claim actual reached winning with changed | good
      · exact Or.inl changed
      · exact Or.inr (RegistrationNativePrekeyEvents.good_selected setup.source.crypto wire _ bounds
          (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          .P (adversary initial.public) budget (bounded initial.public) initial.state claim actual reached good)

/-- The original broad native CEAPP probability pays the real joint Ed-origin bound once and one canonical target sum with its complementary public pin decision. -/
theorem broad_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (readback : RegistrationNativeWire.InitReadBack wire)
    (shortRejects : ∀ (publicKey : Ed25519PublicKey) bytes, bytes.length < 64 → setup.source.crypto.verify publicKey.toList bytes = none)
    (bounds : FreshBounds) (budget : Budget)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
    (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (count : Nat) (room : budget.create ≤ count + 1)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery) :
    Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      (∑ target : Fin (count + 1), PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityOriginBound.reduction (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (fun _ => false) count fallback ordinaryFallback target)) +
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim))}[won = true] := by
  classical
  have split : Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
      (RegistrationNativeEvents.ceAppEvent setup.source.crypto wire serverKeyId budget claim))}[won = true] ≤
      Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
        (RegistrationNativeIdentityOriginEvents.event setup.joint wire))}[won = true] +
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let won ← (RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds .P adversary
          (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim))}[won = true] := by
    simp only [profile_outcome, prEvent_map]
    calc
      _ ≤ Pr{let observed ← outcome (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds adversary}[
          observed.elim false (RegistrationNativeIdentityOriginEvents.event setup.joint wire) = true ∨
          ∃ target ∈ (Finset.univ : Finset (Fin budget.accept × Fin budget.capacity)),
            observed.elim false (RegistrationNativePrekeyEvents.targetEvent setup.source.crypto wire serverKeyId budget target claim) = true] := by
        apply prEvent_mono_of_support
        intro observed supported winning
        cases observed with
        | none => cases winning
        | some actual =>
            have original : RegistrationNativeEvents.CEAppWin setup.source.crypto wire serverKeyId budget claim actual := of_decide_eq_true winning
            rcases outcome_split setup checks wire route representation source ensureInit identityIndex serverKeyId readback shortRejects bounds budget adversary bounded claim actual supported original with changed | selected
            · exact Or.inl (decide_eq_true changed)
            · obtain ⟨target, good⟩ := selected
              exact Or.inr ⟨target, Finset.mem_univ target, decide_eq_true good⟩
      _ ≤ _ := (prEvent_or_le _ _ _).trans (add_le_add le_rfl (prEvent_exists_finset_le Finset.univ _ _))
  exact split.trans (add_le_add (RegistrationNativeIdentityOriginProbability.changed_prekey_bound setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds .P adversary budget bounded count room fallback ordinaryFallback) le_rfl)
end BeaconcryptCore.Computational.RegistrationNativePrekeyProbability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyProbability.outcome_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyProbability.outcome_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyProbability.broad_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyProbability.broad_bound
