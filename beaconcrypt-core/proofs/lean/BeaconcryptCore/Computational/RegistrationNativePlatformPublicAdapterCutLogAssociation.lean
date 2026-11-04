-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal
/-! Chronological source observations commute with the private hash-cut state without changing either one. Each recorded hash retains its actual reply and installs that same cut; each signing request retains its explicit metadata. The protocol's request-only source equality is applied only afterward. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation
open RegistrationNativePlatformPublicAdapterSourceTrace (recorded)
local notation "Cut"=>RegistrationNativePlatformCutJournal.State
variable {S Log A Q :Type} {spec :OracleSpec Q} {m :Type→Type} [Monad m] [LawfulMonad m]

def associate (before :Cut S×List Log) :Cut (S×List Log):=((before.1.1,before.2),before.1.2)

theorem lift_query (implementation :QueryImpl spec (StateT S m))
    (observe :(query :spec.Domain)→spec.Range query→List Log) (query :spec.Domain) (before :Cut S×List Log) :
    Prod.map id associate <$>
      (recorded (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation query)) observe query).run before=
      (RegistrationNativePlatformCutJournal.liftNative (recorded implementation observe query)).run (associate before) :=by
  simp only [recorded,RegistrationNativePlatformCutJournal.liftNative,StateT.run,Functor.map_map,Prod.map,id_eq,associate]

theorem forward_query (implementation :QueryImpl RegistrationSigningShared.Spec (StateT S m))
    (observe :(query :RegistrationSigningShared.Spec.Domain)→RegistrationSigningShared.Spec.Range query→List Log)
    (query :RegistrationSigningShared.Spec.Domain) (before :Cut S×List Log) :
    Prod.map id associate <$>
      (recorded (RegistrationNativePlatformCutJournal.forward implementation) observe query).run before=
      (RegistrationNativePlatformCutJournal.forward (recorded implementation observe) query).run (associate before) :=by
  cases query with
  | hash request=>
    change Prod.map id associate <$>
      ((fun result=>(result.1,(result.2,before.2++observe (.hash request) result.1))) <$>
        (RegistrationNativePlatformCutJournal.hash implementation request).run before.1)=
      (RegistrationNativePlatformCutJournal.hash (recorded implementation observe) request).run (associate before)
    rw [RegistrationNativePlatformCutJournal.hash_run,RegistrationNativePlatformCutJournal.hash_run]
    simp only [recorded,StateT.run,Functor.map_map,Prod.map,id_eq,associate]
  | sign request payload digest=>exact lift_query implementation observe (.sign request payload digest) before

theorem lift_program (implementation :QueryImpl spec (StateT S m))
    (observe :(query :spec.Domain)→spec.Range query→List Log) (work :OracleComp spec A) (before :Cut S×List Log) :
    Prod.map id associate <$>
      (simulateQ (recorded (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation query)) observe) work).run before=
      (simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (recorded implementation observe query)) work).run (associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ associate (lift_query implementation observe) work before

theorem forward_program (implementation :QueryImpl RegistrationSigningShared.Spec (StateT S m))
    (observe :(query :RegistrationSigningShared.Spec.Domain)→RegistrationSigningShared.Spec.Range query→List Log)
    (work :OracleComp RegistrationSigningShared.Spec A) (before :Cut S×List Log) :
    Prod.map id associate <$>
      (simulateQ (recorded (RegistrationNativePlatformCutJournal.forward implementation) observe) work).run before=
      (simulateQ (RegistrationNativePlatformCutJournal.forward (recorded implementation observe)) work).run (associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ associate (forward_query implementation observe) work before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_program
