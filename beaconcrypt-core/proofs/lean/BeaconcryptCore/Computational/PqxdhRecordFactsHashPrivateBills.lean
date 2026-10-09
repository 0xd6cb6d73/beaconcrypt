-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashSource
import BeaconcryptCore.Computational.PqxdhRecordFactsHashBase
import BeaconcryptCore.Computational.PqxdhRecordFactsHashKnown
import BeaconcryptCore.Computational.PqxdhRecordFactsHashLocal
import BeaconcryptCore.Computational.PqxdhRecordFactsHashSealBills

/-! Private digest-query bills of the concrete source compiler. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (Spec)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Exactly the label/suffix private digest addresses, independently of ordinary hashes and finite coins. -/
def privateQuery : (Spec n).Domain → Bool
  | .inl (.inl _) => true
  | _ => false

/-- Every finite-coin program has zero private digest queries; its full coin cost remains a separate bill. -/
theorem coins_private {X : Type} (work : ProbComp X) :
    (OracleComp.liftComp work (Spec n)).IsQueryBoundP (fun query => privateQuery query) 0 := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind coin next ih =>
      rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
      change ((liftM ((Spec n).query (.inr coin)) : OracleComp (Spec n) _) >>= _).IsQueryBoundP _ 0
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [privateQuery]), ih⟩

/-- The ordinary shared compiler never emits a private digest address. -/
theorem shared_query_private (query : AdaptiveCtxSharedHash.HashSpec.Domain) (state : CtxPrivate n) :
    ((PqxdhRecordFactsHashShared.compile query).run state).IsQueryBoundP (fun query => privateQuery query) 0 := by
  cases query with
  | inl coin => simp [PqxdhRecordFactsHashShared.compile, StateT.run, IsQueryBoundP, privateQuery]
  | inr address =>
      rcases address with ⟨⟨⟩, bytes⟩
      simp [PqxdhRecordFactsHashShared.compile, StateT.run, IsQueryBoundP, privateQuery]

/-- Arbitrary adaptive ordinary/hash work, including all native callbacks, still emits no private digest request. -/
theorem shared_program_private {X : Type} (client : OracleComp AdaptiveCtxSharedHash.HashSpec X)
    (state : CtxPrivate n) :
    ((simulateQ PqxdhRecordFactsHashShared.compile client).run state).IsQueryBoundP
      (fun query => privateQuery query) 0 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact isQueryBoundP_bind (shared_query_private query state) (fun result _ => ih result.1 result.2)

/-- The actual complete native program can make ordinary queries and finite draws but no private digest query. -/
theorem native_private (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    {X : Type} (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : CtxPrivate n) :
    (PqxdhRecordFactsHashShared.nativeProgram setup codec client state).IsQueryBoundP
      (fun query => privateQuery query) 0 := by
  rw [PqxdhRecordFactsHashShared.nativeProgram, isQueryBoundP_map_iff]
  exact shared_program_private _ state

/-- Each source request contributes at most its hidden-sealing indicator to the complete concrete compiler's private digest bill. -/
theorem query_private (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) :
    ((PqxdhRecordFactsHashSource.compiler modes replace setup codec query).run state).IsQueryBoundP
      (fun query => privateQuery query) (PqxdhRecordFactsHashSealBills.sealCost query) := by
  cases query with
  | allocate slot =>
      change (PqxdhRecordFactsHashBase.allocate slot state).IsQueryBoundP _ 0
      rw [PqxdhRecordFactsHashBase.allocate, isQueryBoundP_map_iff]
      exact coins_private _
  | coin coin =>
      simp [PqxdhRecordFactsHashSource.compiler, PqxdhRecordFactsHashBase.coin, StateT.run,
        PqxdhRecordFactsHashSealBills.sealCost, IsQueryBoundP, privateQuery]
  | hash bytes => exact shared_query_private (.inr ((), bytes)) state
  | charge kind => trivial
  | lookup coordinate => exact coins_private (PqxdhRecordFactsHashLocal.lookupWork coordinate state)
  | opening pending => trivial
  | sealing pending =>
      apply IsQueryBoundP.of_imp (p' := fun query => PqxdhRecordFactsPrivateCacheSourceDraw.digestQuery query)
      · intro query isPrivate
        cases query with
        | inl address => rfl
        | inr coin => simp [privateQuery] at isPrivate
      · exact PqxdhRecordFactsPrivateCacheSourceDraw.hiddenSeal_digest_queries modes setup.source.crypto
          codec.frameWrite replace pending state
  | knownSend kernel context => exact native_private setup codec _ state
  | knownReceive kernel target context => exact native_private setup codec _ state
  | publish tag => trivial

/-- All nine nonsealing service constructors make zero private digest requests, including arbitrary caller-known native callbacks. -/
theorem nonsealing_private (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n)
    (nonseal : PqxdhRecordFactsPrivateCacheSourceDrawMemo.NonSealing query) (state : CtxPrivate n) :
    ((PqxdhRecordFactsHashSource.compiler modes replace setup codec query).run state).IsQueryBoundP
      (fun query => privateQuery query) 0 := by
  have bounded := query_private modes replace setup codec query state
  cases query <;> first | exact bounded | exact False.elim nonseal

/-- A weighted total source-sealing bill transports through the complete adaptive compiler with coefficient one. -/
theorem program_private {X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X) (cap : Nat)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted PqxdhRecordFactsHashSealBills.sealCost client cap)
    (state : CtxPrivate n) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec) client).run state).IsQueryBoundP
      (fun query => privateQuery query) cap :=
  PqxdhRecordLiftCtxBills.run_bound _ (fun query => privateQuery query)
    PqxdhRecordFactsHashSealBills.sealCost (query_private modes replace setup codec) client cap bounded state

open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)

/-- The complete initialized source compiler has at most `budget.sends` private digest requests, across all sessions and all adaptive replies. -/
theorem source_private {E X : Type} (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary) :
    ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial)).IsQueryBoundP
      (fun query => privateQuery query) budget.sends :=
  program_private modes replace setup codec _ budget.sends
    (PqxdhRecordFactsHashSealBills.program_seals env setup.source.crypto codec route serverKid bounds mode
      budget adversary respects) _

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.coins_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms coins_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.shared_query_private' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms shared_query_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.shared_program_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shared_program_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.native_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms native_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.query_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms query_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.nonsealing_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms nonsealing_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.program_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms program_private
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills.source_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms source_private

end BeaconcryptCore.Computational.PqxdhRecordFactsHashPrivateBills
