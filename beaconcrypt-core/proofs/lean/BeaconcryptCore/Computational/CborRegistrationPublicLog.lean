-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleRegistration

/-! Registration's compiler log is public bookkeeping: it is determined by the original log, the chosen command and its returned value. No kernel or private source field is needed to maintain it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRegistrationPublicLog
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local Log)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

def update (before : Log) : (query : Spec.Domain) → Spec.Range query → Log
  | .inl _, _ => before
  | .inr (.create pin keyId), answer =>
      match PqxdhDeploymentInterface.parsePin pin, answer with
      | some word, some _ => { before with owners := before.owners ++ [(word, keyId)] }
      | _, _ => before
  | .inr command, answer => PqxdhDeploymentCompile.logReply before command answer

/-- The source requests and replies of a registration command are independent of the local kernel copies. -/
noncomputable def requests (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) :
    OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) (Spec.Range query) :=
  Prod.fst <$> (PqxdhDeploymentCompile.compileImpl setup codec route query).run Local.empty

/-- Exact program syntax, on all possible typed source replies. The creation index comes from the actual source request; only its public pin pair is appended locally. -/
theorem compile_registration (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain)
    (registration : CborSplitCompiler.recordCommand query = false) (copies : Local) :
    (PqxdhDeploymentCompile.compileImpl setup codec route query).run copies =
      (fun answer => (answer, { copies with log := update copies.log query answer })) <$>
        requests setup codec route query := by
  rcases query with coin | command
  · simp [requests, PqxdhDeploymentCompile.compileImpl, StateT.run, StateT.lift,
      Functor.map_map, update]
  · cases command
    case create pin keyId =>
      cases parsed : PqxdhDeploymentInterface.parsePin pin <;>
        simp [requests, PqxdhDeploymentCompile.compileImpl, StateT.run, parsed,
          Functor.map_map, update, map_pure]
    all_goals try simp [CborSplitCompiler.recordCommand] at registration
    all_goals simp [requests, PqxdhDeploymentCompile.compileImpl, PqxdhDeploymentCompile.forwardLogged,
      StateT.run, StateT.lift, Functor.map_map, update, PqxdhDeploymentCompile.logReply, bind_pure_comp]

end BeaconcryptCore.Computational.CborRegistrationPublicLog

/-- info: 'BeaconcryptCore.Computational.CborRegistrationPublicLog.compile_registration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationPublicLog.compile_registration
