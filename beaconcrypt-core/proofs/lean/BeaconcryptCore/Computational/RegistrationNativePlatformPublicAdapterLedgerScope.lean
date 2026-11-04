-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativeLedger
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope
open BeaconcryptCore.Refinement
namespace Source
abbrev Spec :=RegistrationNativePlatformPublicAdapterInterface.Spec
abbrev ModeSpec :=RegistrationNativePlatformPublicAdapterInterface.ModeSpec
end Source

def Allowed :RegistrationNativeInterface.Spec.Domain →Prop
  | .inl _=>True
  | .inr (.create ed ml _)=>ed.length≤Usize.max ∧ml.length≤Usize.max
  | .inr (.accept raw) | .inr (.finish _ raw) | .inr (.serverRaw raw) | .inr (.beaconRaw _ raw)=>raw.length≤Usize.max
  | .inr (.build _ payload)=>∀bytes,payload=some bytes →bytes.length≤Usize.max
  | _=>True

def FullAllowed :RegistrationNativeInterface.FullSpec.Domain →Prop
  | .inl query=>Allowed query
  | .inr _=>True

private theorem bytes_bound (raw :Slice U8) : (TranscriptAuthParts.absSlice raw).length≤Usize.max :=by
  simpa only [TranscriptAuthParts.absSlice,List.length_map] using raw.property

theorem source_core (query :Source.Spec.Domain) :
    Allowed (RegistrationNativePlatformPublicAdapterInterface.nativeCore query) :=by
  rcases query with coin|command
  · trivial
  · cases command with
    | create ed ml _=>exact ⟨bytes_bound ed,bytes_bound ml⟩
    | accept raw | finish _ raw | serverRaw raw | beaconRaw _ raw=>exact bytes_bound raw
    | build _ payload=>
      cases payload with
      | none=>simp [RegistrationNativePlatformPublicAdapterInterface.nativeCore,RegistrationNativePlatformPublicAdapterInterface.nativeCommand,Allowed]
      | some raw=>
        intro bytes same
        cases Option.some.inj same
        exact bytes_bound raw
    | bundle _ | hmac _ _ | hash _ | serverSend _ _ | beaconSend _ _=>trivial

private theorem map_scope {I A B :Type} {spec :OracleSpec I} {P :I →Prop}
    (work :OracleComp spec A) (observe :A →B) (safe :AllQueriesSatisfy work P) :
    AllQueriesSatisfy (observe <$>work) P :=by
  simpa only [allQueriesSatisfy_def,isQueryBound_map_iff] using safe

private theorem transfer {I J A :Type} {spec :OracleSpec I} {target :OracleSpec J}
    (implementation :QueryImpl spec (OracleComp target)) (work :OracleComp spec A)
    {P :I →Prop} {Q :J →Prop} (safe :AllQueriesSatisfy work P)
    (leaves :∀query,P query →AllQueriesSatisfy (implementation query) Q) :
    AllQueriesSatisfy (simulateQ implementation work) Q :=by
  induction work using OracleComp.inductionOn with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at safe
    rw [simulateQ_bind,simulateQ_spec_query]
    exact allQueriesSatisfy_bind (leaves query safe.1) (fun reply=>ih reply (safe.2 reply))

private theorem transfer_state {I J S A :Type} {spec :OracleSpec I} {target :OracleSpec J}
    (implementation :QueryImpl spec (StateT S (OracleComp target))) (work :OracleComp spec A)
    {P :I →Prop} {Q :J →Prop} (safe :AllQueriesSatisfy work P)
    (leaves :∀query,P query →∀before,AllQueriesSatisfy ((implementation query).run before) Q) (before :S) :
    AllQueriesSatisfy ((simulateQ implementation work).run before) Q :=by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>
    rw [allQueriesSatisfy_query_bind_iff] at safe
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    exact allQueriesSatisfy_bind (leaves query safe.1 before) (fun result=>ih result.1 (safe.2 result.1) result.2)

private theorem universal {I A :Type} {spec :OracleSpec I} (work :OracleComp spec A) :
    AllQueriesSatisfy work (fun _=>True) :=by
  induction work using OracleComp.inductionOn with
  | pure value=>exact allQueriesSatisfy_pure _ _
  | query_bind query next ih=>exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨True.intro,ih⟩

private def fullAdapter (mode :PqxdhDeploymentInterface.Mode) :
    QueryImpl (Source.ModeSpec mode) (OracleComp RegistrationNativeInterface.FullSpec) :=fun query=>do
  let reply←(RegistrationNativeInterface.FullSpec.query (RegistrationNativePlatformPublicAdapterInterface.nativeQuery query) :OracleComp RegistrationNativeInterface.FullSpec _)
  pure (RegistrationNativeInterface.project mode (RegistrationNativePlatformPublicAdapterInterface.nativeQuery query) reply)

private theorem fullAdapter_scope (mode :PqxdhDeploymentInterface.Mode) (query :(Source.ModeSpec mode).Domain) :
    AllQueriesSatisfy (fullAdapter mode query) FullAllowed :=by
  unfold fullAdapter
  apply allQueriesSatisfy_bind
  · rw [allQueriesSatisfy_query_iff]
    rcases query with core|secrecy
    · exact source_core core
    · trivial
  · intro reply
    exact allQueriesSatisfy_pure _ _

private theorem as_mode_compile {A :Type} (mode :PqxdhDeploymentInterface.Mode) (work :OracleComp (Source.ModeSpec mode) A) :
    RegistrationNativeInterface.asModeO mode (RegistrationNativePlatformPublicAdapterInterface.compile mode work)=
      simulateQ (fullAdapter mode) work :=by
  cases mode with
  | O=>
    unfold RegistrationNativePlatformPublicAdapterInterface.compile RegistrationNativeInterface.asModeO
    apply congrArg (fun impl=>simulateQ impl work)
    funext query
    simp only [RegistrationNativePlatformPublicAdapterInterface.modeAdapter,fullAdapter,RegistrationNativeInterface.project,bind_pure]
  | P=>
    unfold RegistrationNativePlatformPublicAdapterInterface.compile RegistrationNativeInterface.asModeO
    change simulateQ RegistrationNativeInterface.observeFull
      (simulateQ (RegistrationNativePlatformPublicAdapterInterface.modeAdapter .P) work)=_
    rw [←QueryImpl.simulateQ_compose]
    apply congrArg (fun impl=>simulateQ impl work)
    funext query
    rcases query with (coin|command)|secrecy
    · rfl
    · cases command <;> rfl
    · rfl

theorem as_mode {A :Type} (mode :PqxdhDeploymentInterface.Mode) (work :OracleComp (Source.ModeSpec mode) A) :
    AllQueriesSatisfy (RegistrationNativeInterface.asModeO mode (RegistrationNativePlatformPublicAdapterInterface.compile mode work)) FullAllowed :=by
  rw [as_mode_compile]
  exact transfer _ work (universal work) (fun query _=>fullAdapter_scope mode query)

private theorem secrecy_scope {Reader Response :Type} (crypto :Pqxdh.Crypto) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (secrecy :PqxdhDeploymentInterface.Secrecy)
    (before :PqxdhDeploymentSecrecy.Ledger) :
    AllQueriesSatisfy
      (simulateQ RegistrationNativeLedger.legacyLift ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before)) Allowed :=by
  classical
  have legacy :AllQueriesSatisfy ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before)
      (fun query=>PqxdhDeploymentSecrecy.coinOrSend query=true) :=by
    apply (isQueryBoundP_zero_iff _ _).mp
    simpa only [Bool.not_eq_true] using PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy before
  apply transfer _ _ legacy
  intro query safe
  rcases query with coin|command
  · rw [RegistrationNativeLedger.legacyLift,allQueriesSatisfy_query_iff]
    trivial
  · cases command <;>simp_all only [PqxdhDeploymentSecrecy.coinOrSend,Bool.false_eq_true,
      RegistrationNativeLedger.legacyLift,allQueriesSatisfy_query_iff,Allowed]

private theorem ledger_scope {Reader Response :Type} (crypto :Pqxdh.Crypto) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (query :RegistrationNativeInterface.FullSpec.Domain)
    (safe :FullAllowed query) (before :RegistrationNativeLedger.State) :
    AllQueriesSatisfy ((RegistrationNativeLedger.handler crypto codec serverKid bounds query).run before) Allowed :=by
  rcases query with core|secrecy
  · exact map_scope _ _ ((allQueriesSatisfy_query_iff core Allowed).mpr safe)
  · exact map_scope _ _ (secrecy_scope crypto codec serverKid bounds secrecy before.ledger)

theorem full {Reader Response A :Type} (crypto :Pqxdh.Crypto) (codec :PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (Source.ModeSpec mode) A) :
    AllQueriesSatisfy (RegistrationNativeLedger.wrap crypto codec serverKid bounds
      (RegistrationNativeInterface.asModeO mode (RegistrationNativePlatformPublicAdapterInterface.compile mode work))) Allowed :=
  transfer_state _ _ (as_mode mode work) (ledger_scope crypto codec serverKid bounds) _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.source_core' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.source_core

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.as_mode' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.as_mode

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerScope.full
