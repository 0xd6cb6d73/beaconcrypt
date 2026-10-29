-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemStartupGame

/-! The actual optional native startup and full original raw ledger have one ordinary selected-KEM hop. Startup remains inside one executable adversary; its bootstrap omits the private KEM pool. No accepted-target, mark, parser or whole-game simulation premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemStartupSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open PqxdhKemIndCca
open PqxdhInitializerSecrecy
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

private theorem silent_branch (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK)) (real : Bool) :
    EvalDistEq (RegistrationNativeKemMixture.branch baseImpl kem (RegistrationNativeKemStartupGame.silent kem) real)
      (pure false : ProbComp Bool) := by
  simp only [RegistrationNativeKemMixture.branch, RegistrationNativeKemStartupGame.silent,
    oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, simulateQ_bind, simulateQ_pure,
    pure_bind, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftProbComp]
  refine (OracleComp.EvalDistEq.bind_congr_of_support _ (fun chosen _ => ?_)).trans
    (OracleComp.EvalDistEq.bind_const _ _)
  exact (OracleComp.EvalDistEq.bind_congr_of_support _
    (fun pair _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)

noncomputable def real (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool) : ProbComp Bool :=
  RegistrationNativeExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
    bounds mode work (fun observed => decision (observed.1, observed.2.1))

/-- Real-candidate correctness pays one ordinary KEM error across the entire actual optional startup distribution. -/
theorem real_error (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : ∀ publicState, RegistrationNativeInterface.Respects budget (work publicState))
    (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    discreteDistance (real (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work decision)
      (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode work budget parsed selected index decision true) ≤
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  have startup := RegistrationNativeKemStartupGame.branch_startup (n := n) setup checks wire route representation source
    ensureInit identityIndex serverKeyId bounds mode work budget parsed selected index decision true
  rw [discreteDistance_congr (EvalDistEq.refl _) startup]
  unfold real RegistrationNativeExperiment.profile
  apply discreteDistance_bind_left_le_const
  intro maybeInitial supported
  cases maybeInitial with
  | none =>
      change discreteDistance (pure false : ProbComp Bool)
        (RegistrationNativeKemMixture.branch setup.baseImpl setup.kem (RegistrationNativeKemStartupGame.silent setup.kem) true) ≤ _
      rw [discreteDistance_congr (EvalDistEq.refl _)
        (silent_branch setup.baseImpl setup.kem true), discreteDistance_self]
      exact ENNReal.toReal_nonneg
  | some initial =>
      have original := RegistrationNativeKemFullTotal.initialized_source setup checks wire route representation source
        ensureInit identityIndex serverKeyId initial supported bounds mode (work initial.public) budget
        (bounded initial.public) parsed selected decision
      have reconstruction := RegistrationNativeKemTotalSource.source_real setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (RegistrationNativeKemFullTotal.client setup checks wire initial.created.server.server.metadata.sender
          bounds mode (work initial.public) parsed decision) budget.create selected index
      have same := original.trans reconstruction.symm
      change discreteDistance (RegistrationNativeKemFullTotal.real setup checks wire route representation source initial
          bounds mode (work initial.public) decision)
        (RegistrationNativeKemTotalGame.branch setup.baseImpl setup.kem
          (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
          (pure (RegistrationNativeKemServerState.project initial.state))
          (RegistrationNativeKemFullTotal.client setup checks wire initial.created.server.server.metadata.sender
            bounds mode (work initial.public) parsed decision) budget.create selected index true) ≤ _
      rw [discreteDistance_comm, RegistrationNativeKemTotalCorrectness.branch_source,
        discreteDistance_congr (EvalDistEq.refl _) same]
      exact RegistrationNativeKemTotalCorrectness.branch_real_error setup.baseImpl setup.kem functional _ _ _ _ _ _

/-- One concrete ordinary IND-CCA adversary bounds the actual complete native profile's selected-KEM hop, with one correctness error and no startup mixture loss. -/
theorem source_close (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : ∀ publicState, RegistrationNativeInterface.Respects budget (work publicState))
    (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) :
    (real (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work decision).boolDistance
      (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode work budget parsed selected index decision false) ≤
      (setup.kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl setup.baseImpl))
        (RegistrationNativeKemStartupGame.adversary (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
          bounds mode work budget parsed selected index decision).toINDCCA).toReal +
      RegistrationNativeKemTotalCorrectness.correctnessError setup.baseImpl setup.kem := by
  have close := (boolDistance_le_discreteDistance _ _).trans
    (real_error (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode
      functional work budget bounded parsed selected index decision)
  have hop := RegistrationNativeKemMixture.branch_distance setup.baseImpl setup.kem
    (RegistrationNativeKemStartupGame.sample (n := n) setup source ensureInit identityIndex serverKeyId)
    (RegistrationNativeKemStartupGame.family (n := n) setup checks wire route representation source bounds mode work budget parsed selected index decision)
  have triangle := ProbComp.boolDistance_triangle
    (real (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work decision)
    (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision true)
    (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision false)
  change (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision true).boolDistance
    (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision false) = (setup.kem.IND_CCA_Advantage _
    (RegistrationNativeKemStartupGame.adversary (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision).toINDCCA).toReal at hop
  rw [hop] at triangle
  linarith

end BeaconcryptCore.Computational.RegistrationNativeKemStartupSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStartupSource.real_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStartupSource.real_error
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemStartupSource.source_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemStartupSource.source_close
