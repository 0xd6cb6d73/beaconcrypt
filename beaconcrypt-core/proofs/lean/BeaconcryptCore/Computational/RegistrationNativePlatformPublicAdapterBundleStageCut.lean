-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageLog
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCutLogAssociation
/-! The actual Bundle publication retains its exact chronological source hash cut. This instrumented source execution retains that cut and the chronological leaf log jointly. Both projections preserve the original packet; no signing metadata is reconstructed from a later native audit. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterSourceTrace (recorded)
local notation "Cut"=>RegistrationNativePlatformCutJournal.State
abbrev Spec (E :Type):=RegistrationNativePlatformWriter.Spec E
variable {S T A E Log :Type} {m :Type→Type} [Monad m] [LawfulMonad m]

noncomputable def lifted (implementation :QueryImpl (Spec E) (StateT S m)) :QueryImpl (Spec E) (StateT (Cut S) m)
  | .inl (.inl query)=>RegistrationNativePlatformCutJournal.forward (fun query=>implementation (.inl (.inl query))) query
  | query=>RegistrationNativePlatformCutJournal.liftNative (implementation query)

theorem query_source (implementation :QueryImpl (Spec E) (StateT S m))
    (query :(Spec E).Domain) (before :Cut S) :
    Prod.map id Prod.fst <$> (lifted implementation query).run before=(implementation query).run before.1 :=by
  cases query with
  | inl query=>cases query with
    | inl query=>cases query with
      | hash request=>
        change Prod.map id Prod.fst <$> (RegistrationNativePlatformCutJournal.hash (fun query=>implementation (.inl (.inl query))) request).run before=_
        rw [RegistrationNativePlatformCutJournal.hash_run]
        simp only [Functor.map_map,Prod.map,id_eq]
        exact id_map _
      | sign request payload digest=>
        simp only [lifted,RegistrationNativePlatformCutJournal.forward,RegistrationNativePlatformCutJournal.liftNative,StateT.run,Functor.map_map,Prod.map,id_eq]
        exact id_map _
    | inr request=>
      simp only [lifted,RegistrationNativePlatformCutJournal.liftNative,StateT.run,Functor.map_map,Prod.map,id_eq]
      exact id_map _
  | inr request=>
    simp only [lifted,RegistrationNativePlatformCutJournal.liftNative,StateT.run,Functor.map_map,Prod.map,id_eq]
    exact id_map _

theorem logged_source (implementation :QueryImpl (Spec E) (StateT S m))
    (observe :(query :(Spec E).Domain)→(Spec E).Range query→List Log)
    (work :OracleComp (Spec E) A) (before :Cut S×List Log) :
    Prod.map id (Prod.map Prod.fst id) <$>
      (simulateQ (recorded (lifted implementation) observe) work).run before=
      (simulateQ (recorded implementation observe) work).run (before.1.1,before.2) :=
  RegistrationNativePlatformPublicAdapterSourceTrace.source _ _ Prod.fst (query_source implementation) observe work before

theorem associate_query (implementation :QueryImpl (Spec E) (StateT S m))
    (observe :(query :(Spec E).Domain)→(Spec E).Range query→List Log)
    (query :(Spec E).Domain) (before :Cut S×List Log) :
    Prod.map id RegistrationNativePlatformPublicAdapterCutLogAssociation.associate <$>
      (recorded (lifted implementation) observe query).run before=
      (lifted (recorded implementation observe) query).run
        (RegistrationNativePlatformPublicAdapterCutLogAssociation.associate before) :=by
  cases query with
  | inl query=>cases query with
    | inl query=>exact RegistrationNativePlatformPublicAdapterCutLogAssociation.forward_query (fun query=>implementation (.inl (.inl query))) (fun query reply=>observe (.inl (.inl query)) reply) query before
    | inr request=>exact RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query implementation observe (.inl (.inr request)) before
  | inr request=>exact RegistrationNativePlatformPublicAdapterCutLogAssociation.lift_query implementation observe (.inr request) before

theorem associate_program (implementation :QueryImpl (Spec E) (StateT S m))
    (observe :(query :(Spec E).Domain)→(Spec E).Range query→List Log)
    (work :OracleComp (Spec E) A) (before :Cut S×List Log) :
    Prod.map id RegistrationNativePlatformPublicAdapterCutLogAssociation.associate <$>
      (simulateQ (recorded (lifted implementation) observe) work).run before=
      (simulateQ (lifted (recorded implementation observe)) work).run
        (RegistrationNativePlatformPublicAdapterCutLogAssociation.associate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (associate_query implementation observe) work before

omit [LawfulMonad m] in
private theorem publication_hash_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) :
    RegistrationNativePlatformBeaconPublication.fromHash left encode pending =
      RegistrationNativePlatformBeaconPublication.fromHash right encode pending := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  cases requested : pending.request <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok request => rw [hashes request]

omit [LawfulMonad m] in
private theorem publication_ed_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (signatures : ∀ request, left (.inr request) = right (.inr request))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) :
    RegistrationNativePlatformBeaconPublication.fromEd left encode pending =
      RegistrationNativePlatformBeaconPublication.fromEd right encode pending := by
  conv_lhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  conv_rhs => rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  cases requested : pending.request <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok request =>
    rw [signatures request]
    apply bind_congr
    intro reply
    cases resumed : pending.resume reply with
    | fail error | div => rfl
    | ok effect => cases effect with
      | Ed25519SigningRequested next => exact publication_ed_same left right hashes signatures encode next
      | HashRequested next => exact publication_hash_same left right hashes encode next
      | _ => rfl
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

omit [LawfulMonad m] in
private theorem publication_begin_same {Encoded : Type}
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (hashes : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (signatures : ∀ request, left (.inr request) = right (.inr request))
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    RegistrationNativePlatformBeaconPublication.begin left encode control inputs scalar pin =
      RegistrationNativePlatformBeaconPublication.begin right encode control inputs scalar pin := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  cases started : registration.begin_beacon_init control inputs scalar pin <;>
    simp only [RegistrationNativePlatformBeaconPublication.continueWith]
  case ok effect =>
    cases effect <;> first
      | rfl
      | exact publication_ed_same left right hashes signatures encode _

/-- The actual Beacon publication retains the chronological source hash cut and log through its exact Ed-signing, hashing and writer stages. -/
theorem actual (implementation :QueryImpl (Spec E) (StateT S m))
    (fallback :registration.MldsaSigningRequest→StateT S m RegistrationSigningShared.SignReply)
    (control :pqxdh.BeaconFresh) (inputs :pqxdh.BeaconStartInputs) (scalar :pqxdh.BeaconCoins)
    (pin :session.ServerAuthenticationPin) :
    simulateQ (lifted implementation) (RegistrationNativePlatformWriter.begin E control inputs scalar pin)=
      RegistrationNativePlatformBeaconPublication.begin
        (RegistrationNativePlatformCutJournal.extended
          (RegistrationNativePlatformCutJournal.source (fun query=>implementation (.inl (.inl query))) fallback)
          (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation (.inl (.inr query)))))
        (fun signed=>simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation (.inr query)))
          (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
            (RegistrationNativePlatformWriter.initPacket signed)).run)
        control inputs scalar pin :=by
  rw [RegistrationNativePlatformWriter.begin_interpret]
  rw [publication_begin_same
    (fun request => lifted implementation (.inl request))
    (RegistrationNativePlatformCutJournal.extended
      (RegistrationNativePlatformCutJournal.forward (fun query => implementation (.inl (.inl query))))
      (fun query => RegistrationNativePlatformCutJournal.liftNative (implementation (.inl (.inr query)))))
    (fun _ => rfl) (fun _ => rfl)]
  apply StateT.ext
  intro before
  exact (RegistrationNativePlatformCutJournal.beacon_begin
    (fun query=>implementation (.inl (.inl query))) fallback
    (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation (.inl (.inr query))))
    (fun signed=>simulateQ (fun query=>RegistrationNativePlatformCutJournal.liftNative (implementation (.inr query)))
      (AdapterRegistrationWriterRequestExtraction.encodeInit (E:=E) (m:=AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket signed)).run)
    control inputs scalar pin before).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.logged_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.logged_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.associate_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.associate_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.associate_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.associate_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleStageCut.actual
