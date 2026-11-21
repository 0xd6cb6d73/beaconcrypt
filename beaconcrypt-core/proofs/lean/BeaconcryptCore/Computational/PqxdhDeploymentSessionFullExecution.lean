-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentSessionResume
import BeaconcryptCore.Computational.PqxdhDeploymentSessionSecurity

/-! A private root-labelled prefix is followed by its retained real continuation. The complete source run, its actual output and final native state remain present in the same execution as the root agreement receipts. The suffix is never answered by frozen defaults. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhDeploymentServerAuthEmbed (SourceSpec dflt stopAt)
open PqxdhDeploymentServerAuthLocal (State base Bad)
open PqxdhDeploymentSessionCoupling (initial audited auditedView ReducedResult)
open PqxdhDeploymentSessionResume (Journal cut)
open PqxdhRegistrationR1Restriction (eraseShared)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- The original source handler with only its unused analysis histories erased after each callback. Every real native field and both primitive caches remain. -/
noncomputable def normalized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) : QueryImpl (SourceSpec KemSK) (StateT (State KemSK) ProbComp) :=
  fun query state => Prod.map id eraseShared <$> (base setup codec checks seed query).run state

/-- Normalizing unused histories commutes with every complete adaptive source program. -/
theorem normalized_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (state : State KemSK) :
    Prod.map id eraseShared <$> (simulateQ (base setup codec checks seed) program).run state =
      (simulateQ (normalized setup codec checks seed) program).run (eraseShared state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ eraseShared
    (PqxdhDeploymentServerAuthLocal.base_stable setup codec checks seed) program state

/-- Private prefix output: the actual residual program and the original source journal. -/
abbrev CutResult (KemSK Result : Type) := OracleComp (SourceSpec KemSK) Result × Journal (SourceSpec KemSK)

/-- Full root-labelled source output, before the real residual continuation is resumed. -/
abbrev PrefixAudit (KemSK Result : Type) :=
  PqxdhRegistrationR1RootAudit.RootAudit KemSK (ReducedResult KemSK (CutResult KemSK Result))

/-- Execute the same root-labelled prefix and then every remaining real source callback from its native snapshot. The actual original result and final native state are returned jointly with the private receipt. -/
noncomputable def full (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) :
    ProbComp (PrefixAudit KemSK Result × (Result × State KemSK)) := do
  let audit ← audited setup codec checks seed c (cut (stopAt c) [] program)
  let snapshot := auditedView setup audit
  let final ← (simulateQ (normalized setup codec checks seed) snapshot.1.1.1).run snapshot.2
  pure (audit, final)

/-- Retaining the private actual prefix receipts and resuming the real suffix preserves the complete original source execution in distribution. -/
theorem full_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result)
    (unread : program.IsQueryBoundP (Bad (KemSK := KemSK)) 0) :
    EvalDistEq (Prod.snd <$> full setup codec checks seed c program)
      (Prod.map id eraseShared <$> (simulateQ (base setup codec checks seed) program).run (initial setup seed)) := by
  have coupled := (PqxdhDeploymentSessionCoupling.frozen_root_state setup codec checks seed c
    (cut (stopAt c) [] program)
    (PqxdhDeploymentSessionResume.cut_query_bound (stopAt c) [] program Bad 0 unread)).bind_left
      (fun result : (CutResult KemSK Result × Journal (SourceSpec KemSK)) × State KemSK =>
        (simulateQ (normalized setup codec checks seed) result.1.1.1).run result.2)
  rw [normalized_run, show eraseShared (initial setup seed) = initial setup seed from rfl,
    PqxdhDeploymentSessionResume.resume_frozen] at coupled
  rw [normalized_run, show eraseShared (initial setup seed) = initial setup seed from rfl]
  simpa only [full, map_bind, map_pure, bind_pure, bind_map_left] using coupled.symm

/-- Executing the actual suffix neither conditions nor discards any private prefix receipt. -/
theorem full_audit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) :
    EvalDistEq (Prod.fst <$> full setup codec checks seed c program)
      (audited setup codec checks seed c (cut (stopAt c) [] program)) := by
  simp only [full, map_bind, map_pure]
  refine (EvalDistEq.bind_congr_of_support (g := pure) _
    (fun audit _ => OracleComp.EvalDistEq.bind_const _ _)).trans ?_
  simpa only [bind_pure] using (EvalDistEq.refl (audited setup codec checks seed c (cut (stopAt c) [] program)))

/-- The reduction's private query journal has no effect when its returned value is discarded. -/
theorem discard_record {Value : Type} (work : OracleComp ServerAuthSpec Value) :
    (fun _ => ()) <$> PqxdhServerAuthApiJournal.record work = (fun _ => ()) <$> work := by
  simpa only [Functor.map_map] using
    congrArg (Functor.map (fun _ : Value => ())) (PqxdhServerAuthApiJournal.erase work)

/-- Exposing the actual residual as private analysis output leaves the existing stopped source reduction unchanged. -/
theorem embedded_cut_unit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput) :
    (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.embedded setup codec c (cut (stopAt c) [] program) input =
      (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.embedded setup codec c program input := by
  have same := congrArg (fun work =>
      (simulateQ (PqxdhDeploymentServerAuthEmbed.embed setup codec c input) work).run'
        (PqxdhDeploymentServerAuthEmbed.Emb.empty (KemSK := KemSK)))
    (PqxdhDeploymentSessionResume.frozen_cut_unit dflt (stopAt c) program)
  simpa only [PqxdhDeploymentServerAuthEmbed.embedded, StateT.run'_eq,
    simulateQ_map, StateT.run_map, Functor.map_map] using same

/-- The complete CE-A1 adversary is unchanged when its actual residual continuation is retained privately. Consequently every existing primitive reduction and resource bill remains the original one. -/
theorem adversary_cut_unit (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (c : Nat) (program : OracleComp (SourceSpec KemSK) Result) (input : AuthInput) :
    (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.adversary setup codec c (cut (stopAt c) [] program) input =
      (fun _ => ()) <$> PqxdhDeploymentServerAuthEmbed.adversary setup codec c program input := by
  simpa only [PqxdhDeploymentServerAuthEmbed.adversary, discard_record] using
    embedded_cut_unit setup codec c program input

end BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.normalized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.normalized_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.full_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.full_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.full_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.full_audit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.discard_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.discard_record

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.embedded_cut_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.embedded_cut_unit

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.adversary_cut_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentSessionFullExecution.adversary_cut_unit
