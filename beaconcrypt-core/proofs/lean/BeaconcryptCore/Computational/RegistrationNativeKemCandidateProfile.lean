-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateSource
import BeaconcryptCore.Computational.RegistrationNativeKemStartupGame

/-! Both concrete whole-startup KEM branches are the explicit native private source. Only the selected created handle's challenge-ciphertext decapsulation is changed in the postphase; all original startup, raw ledger and unrestricted prephase effects remain. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateProfile
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
  refine (OracleComp.EvalDistEq.bind_congr_of_support _ (fun _chosen _ => ?_)).trans
    (OracleComp.EvalDistEq.bind_const _ _)
  exact (OracleComp.EvalDistEq.bind_congr_of_support _
    (fun _pair _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
  (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
  (decision : Value × RegistrationNativeLedger.State → Bool)

noncomputable def profile (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin budget.capacity) (index : Nat)
    (decision : Value × RegistrationNativeLedger.State → Bool) (real : Bool) : ProbComp Bool := do
  let initial ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  match initial with
  | none => pure false
  | some initial =>
      RegistrationNativeKemCandidateSource.total setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (RegistrationNativeKemFullTotal.client setup checks wire initial.created.server.server.metadata.sender
          bounds mode (work initial.public) parsed decision) budget.create selected index real

/-- The concrete whole-startup KEM hybrid is the literal candidate-source native program, with no correctness, event-mark or source-simulation assumption. -/
theorem hybrid_source (real : Bool) :
    EvalDistEq (RegistrationNativeKemStartupGame.hybrid (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode work budget parsed selected index decision real)
      (profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId bounds mode work
        budget parsed selected index decision real) := by
  refine (RegistrationNativeKemStartupGame.branch_startup (n := n) setup checks wire route representation source ensureInit
    identityIndex serverKeyId bounds mode work budget parsed selected index decision real).trans ?_
  unfold profile
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro initial _generated
  cases initial with
  | none => exact silent_branch setup.baseImpl setup.kem real
  | some initial =>
      change EvalDistEq (RegistrationNativeKemTotalGame.branch setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation initial.created initial.credential)
        (pure (RegistrationNativeKemServerState.project initial.state))
        (RegistrationNativeKemFullTotal.client setup checks wire initial.created.server.server.metadata.sender
          bounds mode (work initial.public) parsed decision) budget.create selected index real) _
      rw [RegistrationNativeKemCandidateSource.total_branch]

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateProfile.hybrid_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateProfile.hybrid_source
