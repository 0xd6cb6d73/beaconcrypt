-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCaps
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationService

/-! Actual Server completion can query occupancy and install a Server peer, but never appends a Beacon owner. This includes the real known and hidden publication branches, rejected encodings and failed allocation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedServerService
open RegistrationNativeHiddenServerAllocationCaps (EffectAllowed LocalAllowed)
open RegistrationNativeHiddenAllocationCore (simulation mapped)
variable {n : Nat} {KemSK Value Encoded : Type}

def CommonAllowed : (Common n).Domain → Prop
  | .inr effect => EffectAllowed effect
  | _ => True
def PublicAllowed : (PublicSpec n).Domain → Prop
  | .inr query => CommonAllowed query
  | _ => True

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem known_install (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (knownInstall (n := n) control published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error => simp only [knownInstall, prepared]; trivial
  | div => simp only [knownInstall, prepared]; trivial
  | ok reply => cases reply with
    | Err previous => simp only [knownInstall, prepared]; trivial
    | Ok pending =>
        rw [knownInstall_native control published pending prepared]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)

private theorem hidden_install (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : registration.PublishedServerResponse Encoded) :
    AllQueriesSatisfy (RegistrationHiddenInstall.install control slot published) EffectAllowed := by
  cases prepared : peer.begin_peer_insert control published with
  | fail error => simp only [RegistrationHiddenInstall.install, prepared]; trivial
  | div => simp only [RegistrationHiddenInstall.install, prepared]; trivial
  | ok reply => cases reply with
    | Err previous => simp only [RegistrationHiddenInstall.install, prepared]; trivial
    | Ok pending =>
        rw [RegistrationHiddenInstall.install_native control slot published pending prepared]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)

private theorem known_after (control : pqxdh.ServerState)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (knownAfter (n := n) control published) EffectAllowed := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok published => exact known_install control published

private theorem hidden_after (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (published : RustM (RegistrationWorldServerPublication.Result Encoded)) :
    AllQueriesSatisfy (RegistrationHiddenInstall.after control slot published) EffectAllowed := by
  cases published with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok published => exact hidden_install control slot published

private theorem publication (work : OracleComp RegistrationBoundPublication.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationHiddenInstall.publicationLift (n := n)) work) CommonAllowed := by
  exact simulation RegistrationHiddenInstall.publicationLift (fun _ => True) CommonAllowed
    (fun _query _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem effects (work : OracleComp (EnvEffects n) Value) (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ RegistrationHiddenInstall.effectLift work) CommonAllowed :=
  simulation RegistrationHiddenInstall.effectLift EffectAllowed CommonAllowed
    (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) work safe

private theorem branch (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) :
    AllQueriesSatisfy (publicBranch encode control initial choice) CommonAllowed := by
  cases choice with
  | known output =>
      simp only [publicBranch, knownStage]
      exact allQueriesSatisfy_bind (publication _) (fun published => effects _ (known_after control published))
  | hidden reference =>
      simp only [publicBranch, hiddenStage]
      exact allQueriesSatisfy_bind (publication _) (fun published => effects _ (hidden_after control reference.slot published))

private theorem admitted (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) :
    AllQueriesSatisfy (publicAdmitted (n := n) encode control initial message) PublicAllowed := by
  unfold publicAdmitted
  apply allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  intro reply
  cases reply with
  | none => trivial
  | some choice =>
      exact simulation publicCommon CommonAllowed PublicAllowed
        (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) _ (branch encode control initial choice)

private theorem complete (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8)
    (before : RegistrationServerMaterialFrontend.State) :
    AllQueriesSatisfy ((RegistrationServerMaterialFrontend.complete (n := n) wire reservePeer ready application).run before) PublicAllowed := by
  simp only [RegistrationServerMaterialFrontend.complete, StateT.run]
  cases actual : peer.begin_completion_lookup before.control before.pin (RegistrationServerMaterialFrontend.token ready) application with
  | fail error => trivial
  | div => trivial
  | ok reply => cases reply with
    | Err previous => trivial
    | Ok lookup =>
      cases requested : lookup.request with
      | fail error => trivial
      | div => trivial
      | ok keyId =>
        simp only [requested]
        split
        · have occupancy : AllQueriesSatisfy
              (RegistrationServerMaterialFrontend.effect (n := n) (.inr (.peerPresent keyId))) PublicAllowed :=
                (allQueriesSatisfy_query_iff _ _).mpr rfl
          apply allQueriesSatisfy_bind occupancy
          intro occupied
          cases resumed : lookup.resume occupied with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err previous => trivial
            | Ok selected =>
              simp only []
              apply allQueriesSatisfy_bind
              · unfold RegistrationServerMaterialFrontend.adHash
                cases requestedHash : selected.request with
                | fail error | div => dsimp only; trivial
                | ok request =>
                    dsimp only
                    have hashing : AllQueriesSatisfy (RegistrationServerMaterialFrontend.effect (n := n)
                        (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))) PublicAllowed :=
                      (allQueriesSatisfy_query_iff _ _).mpr rfl
                    exact allQueriesSatisfy_bind hashing (fun _ => by trivial)
              · intro hashed
                cases hashed with
                | fail error | div => trivial
                | ok reply => cases reply with
                  | Err previous => trivial
                  | Ok initial =>
                    dsimp only
                    split
                    · apply allQueriesSatisfy_bind (admitted wire.encodeResponse before.control
                        (RegistrationBoundKeySchedule.publicInitial initial) ready.reference)
                      intro published
                      cases published with
                      | fail error => trivial
                      | div => trivial
                      | ok reply => cases reply <;> trivial
                    · trivial
        · trivial

private theorem material_build (wire : RegistrationNativeWire.Wire) (reservePeer : Bool) (handle : Nat)
    (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State) :
    AllQueriesSatisfy ((RegistrationServerMaterialFrontend.build (n := n) wire reservePeer handle application).run before) PublicAllowed := by
  simp only [RegistrationServerMaterialFrontend.build, StateT.run]
  cases taken : RegistrationServerMaterialFrontend.take handle before with
  | mk ready current => cases ready with
    | none => trivial
    | some ready => cases application with
      | none => trivial
      | some application => exact complete wire reservePeer ready application current

/-- Publication and admitted non-append effects retain their footprint in the actual current-environment compiler. -/
theorem service_safe (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (PublicSpec n).Domain) (before : RegistrationServerReferenceCompiler.Environment)
    (allowed : PublicAllowed query) :
    AllQueriesSatisfy ((RegistrationNativeCommonCompiler.service
      (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) RegistrationServerOpenReferenceCompiler.demand
      source writer sign query).run before) (LocalAllowed (KemSK := KemSK)) := by
  cases query with
  | inl message =>
      simp only [RegistrationNativeCommonCompiler.service, StateT.run_lift, bind_pure_comp]
      exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  | inr query => cases query with
    | inl publication =>
        simp only [RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
          RegistrationNativeCommonCompiler.publication, StateT.run]
        apply mapped
        apply simulation _ EffectAllowed (LocalAllowed (KemSK := KemSK)) _ _
          (RegistrationNativeHiddenAllocationService.publication source writer sign publication before.receipts)
        intro effect allowed
        exact (allQueriesSatisfy_query_iff _ _).mpr allowed
    | inr effect =>
        simp only [RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
          StateT.run_lift, bind_pure_comp]
        exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr allowed)

/-- The actual full public-reference build, including hidden/known installation, has no Beacon-allocation callback. -/
theorem build_safe (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerMaterialFrontend.State)
    (env : RegistrationServerReferenceCompiler.Environment) :
    AllQueriesSatisfy (((RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK)
      source wire checks sign handle application).run before).run env) (LocalAllowed (KemSK := KemSK)) := by
  change AllQueriesSatisfy ((simulateQ (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
    RegistrationServerOpenReferenceCompiler.demand source wire.frameWrite sign)
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before)).run env) _
  generalize actual : (RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before = work
  have safe : AllQueriesSatisfy work PublicAllowed := actual ▸ material_build wire checks.reservePeer handle application before
  clear actual
  induction work using OracleComp.inductionOn generalizing env with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (service_safe source wire.frameWrite sign query env first)
        (fun result => ih result.1 result.2 (later result.1))

/-- The complete current-environment SDK build preserves the allocation-free public frontend footprint. -/
theorem build_frontend_safe {mlSource : RegistrationNativeMldsa.Source}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationNativePublicFrontend.State mlSource) :
    AllQueriesSatisfy ((RegistrationNativePublicFrontend.serverOpen false
      (RegistrationServerOpenReferenceCompiler.build (n := n) (KemSK := KemSK)
        source wire checks sign handle application)).run before) RegistrationNativeHiddenAllocationCore.Allowed :=
  RegistrationNativeHiddenServerAllocationCaps.server_safe false _ before
    (build_safe source wire checks sign handle application before.server before.environment)

end BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.build_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.build_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.service_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.service_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.build_frontend_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenServerAllocationCapsBuild.build_frontend_safe
