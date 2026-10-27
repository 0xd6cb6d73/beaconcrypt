import BeaconcryptCore.Computational.RawCtxSelectedFamilyAudit

/-!
The audited selected-material family is interpreted by the literal native private-table backend. Complete native role and primitive state are retained; only private labels and audit observations are projected away. These source equations do not supply installation provenance or a nonce probability bound.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open RawCtxSelectedFamilyAudit
variable {A M P I D K Result : Type} {S B : Nat}

abbrev Roles (M P I D K : Type) (S B : Nat) :=
  RawCtxGenericRoleFamily.Roles
    (RawCtxOwnerLabels.Labelled RawCtxSelectedMessageReveals.Kernel S B) M P I D K S B

def native (key : RootOutput) (roles : Roles M P I D K S B) :
    RawCtxProtocolReveals.Roles M P I D K S B :=
  RawCtxGenericRoleFamily.nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key)
    (RawCtxGenericRoleFamily.mapRoles Prod.snd roles)

/-- The actual native role operation and all backend effects are recovered from the same audited frontend with the exact private table and public services. -/
theorem native_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (roles : Roles M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer
        (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
      ((RawCtxProtocolRoles.protocolImpl S B sender route decode query).run (native key roles)) =
      Prod.map id (native key) <$>
        simulateQ (sourceServices source writer prior parent key target nonce next)
          (simulateQ RawCtxSelectedDriverAudit.erase
            ((frontend parent target nonce next sender route decode query).run roles)) := by
  rw [native, RawCtxSelectedMessageFamily.frontend_source, ← service_frontend, step_erased,
    simulateQ_map, Functor.map_map]
  rfl

/-- Every adaptive original native record/public schedule retains its exact optional replies, complete roles and shared primitive effects under private audit erasure. -/
theorem native_schedule (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result) (roles : Roles M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer
        (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
      ((simulateQ (RawCtxProtocolRoles.protocolImpl S B sender route decode) client).run (native key roles)) =
      Prod.map id (native key) <$>
        simulateQ (sourceServices source writer prior parent key target nonce next)
          (simulateQ RawCtxSelectedDriverAudit.erase
            ((simulateQ (frontend parent target nonce next sender route decode) client).run roles)) := by
  induction client using OracleComp.inductionOn generalizing roles with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [native_step, bind_map_left, map_bind]
    exact bind_congr fun result => ih result.1 result.2

noncomputable def lifted (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl Services (OptionT (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :=
  fun query => monadLift (sourceServices (A := A) source writer prior parent key target nonce next query)

/-- The actual source service has no outer compiler stop; every optional native result stays inside its original reply. -/
theorem lifted_program {Value : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (work : OracleComp Services Value) :
    (simulateQ (lifted (A := A) source writer prior parent key target nonce next) work).run =
      some <$> simulateQ (sourceServices source writer prior parent key target nonce next) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, lifted, OptionT.run_bind,
      OptionT.run_monadLift, Option.elimM, bind_map_left, monadLift_self, Option.elim_some, ih, map_bind]

noncomputable def observed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result) (roles : Roles M P I D K S B)
    (history : List (RawCtxSelectedDriverAudit.Event (RawCtxProtocolReveals.Owner S B)))
    (state : RawCtxSharedPrimitive.SharedState A) :=
  ((simulateQ (RawCtxSelectedDriverAudit.observed (lifted source writer prior parent key target nonce next))
    ((simulateQ (frontend parent target nonce next sender route decode) client).run roles)).run).run (history, state)

/-- The complete native record/public execution is exactly the source audit execution after erasing only private annotations and retained events; all native optional outputs and private primitive state survive. -/
theorem observed_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result) (roles : Roles M P I D K S B)
    (history : List (RawCtxSelectedDriverAudit.Event (RawCtxProtocolReveals.Owner S B)))
    (state : RawCtxSharedPrimitive.SharedState A) :
    (fun result => (Option.map (Prod.map id (native key)) result.1, result.2.2)) <$>
      observed source writer prior parent key target nonce next sender route decode client roles history state =
      (fun result => (some result.1, result.2)) <$>
        ((simulateQ (RawCtxFunctionalFamily.backend source writer
          (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
          ((simulateQ (RawCtxProtocolRoles.protocolImpl S B sender route decode) client).run (native key roles))).run state) := by
  have erased := RawCtxSelectedDriverAudit.observed_program
    (lifted (A := A) source writer prior parent key target nonce next)
    ((simulateQ (frontend parent target nonce next sender route decode) client).run roles) history state
  rw [lifted_program, StateT.run_map] at erased
  rw [native_schedule, StateT.run_map]
  have projected := congrArg (fun work => Prod.map (Option.map (Prod.map id (native key))) id <$> work) erased
  simpa only [Functor.map_map, Prod.map_def, id_eq, Option.map_some, observed] using projected

/-- Retaining the complete native audit has exactly the original uniform-query allowance; no source callback or rejected path is treated as free. -/
theorem observed_uniform (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolRoles.SourceSpec S B) Result) (roles : Roles M P I D K S B)
    (history : List (RawCtxSelectedDriverAudit.Event (RawCtxProtocolReveals.Owner S B)))
    (state : RawCtxSharedPrimitive.SharedState A) (budget : Nat) :
    (observed source writer prior parent key target nonce next sender route decode client roles history state).IsTotalQueryBound budget ↔
      ((simulateQ (RawCtxFunctionalFamily.backend source writer
        (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
        ((simulateQ (RawCtxProtocolRoles.protocolImpl S B sender route decode) client).run (native key roles))).run state).IsTotalQueryBound budget := by
  have cost := congrArg (fun work => work.IsTotalQueryBound budget)
    (observed_native source writer prior parent key target nonce next sender route decode client roles history state)
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using Iff.of_eq cost

end BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.native_step
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.native_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.native_schedule
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.lifted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.lifted_program
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.observed_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.observed_native
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.observed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit.observed_uniform
