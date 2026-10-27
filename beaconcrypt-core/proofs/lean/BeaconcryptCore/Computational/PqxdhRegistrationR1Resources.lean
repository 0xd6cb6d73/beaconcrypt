-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationR1Authentication
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleResources

/-! The actual singleton source ledger is separate from the cryptographic reduction bills: it includes both initialization calls, the complete constructor and bundle, and every adaptive suffix attempt. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationR1Resources
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthSourceCosts
open PqxdhRegistrationR1Surface PqxdhRegistrationSchedule
variable {ι KemSK Reader Response Result A : Type} {baseSpec : OracleSpec ι}

/-- The seven original API capabilities retain their coordinates in the nine-capability raw surface. Creation and bundle occur only in the explicit prefix. -/
def suffixKind : ServerAuthSpec.Domain → Fin 9
  | .inl _ => 0
  | .inr (.accept _) => 3
  | .inr (.build _ _) => 4
  | .inr (.finish _) => 5
  | .inr (.hmac _ _) => 6
  | .inr (.hash _) => 7
  | .inr (.reveal _) => 8

/-- Routing issues one request of the same class per original API request and adds no callback. -/
theorem route_bound (work : OracleComp ServerAuthSpec Result) (kind : Fin 9) (q : Nat)
    (bounded : work.IsQueryBoundP (fun query => suffixKind query = kind) q) :
    (simulateQ surfaceRoute work).IsQueryBoundP (fun query => surfaceKind query = kind) q := by
  apply bounded.simulateQ_of_step (impl := surfaceRoute)
  · intro query _
    rcases query with coin | (_ | _ | _ | _ | _ | _)
    all_goals simp [surfaceRoute, isQueryBoundP_query_iff]
  · intro query excluded
    rcases query with coin | (_ | _ | _ | _ | _ | _)
    all_goals simp only [surfaceRoute]
    all_goals rw [isQueryBoundP_query_iff]
    all_goals simpa only [surfaceKind, sourceKind, suffixKind, Nat.lt_irrefl, imp_false] using excluded

/-- Add the one actual raw create and one actual bundle attempt to the original suffix caps. -/
def programBudget (budget : Fin 9 → Nat) (kind : Fin 9) : Nat :=
  (if kind = 1 then 1 else 0) + ((if kind = 2 then 1 else 0) + budget kind)

/-- The full raw singleton client pays exactly its two prefix requests in addition to each original selective suffix cap. Every possible optional reply is quantified. -/
theorem program_bills (identity : PublicIdentity) (sender : Std.U64)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (budget : Fin 9 → Nat)
    (bounded : ∀ input kind, (work input).IsQueryBoundP (fun query => suffixKind query = kind) (budget kind)) :
    UniformBounded (PqxdhRegistrationR1Surface.program identity sender work) (programBudget budget) := by
  intro kind
  unfold PqxdhRegistrationR1Surface.program programBudget
  apply isQueryBoundP_bind
  case h =>
    rw [isQueryBoundP_query_iff]
    simp +contextual [surfaceKind, eq_comm]
  case h' =>
    intro created _
    apply isQueryBoundP_bind
    case h =>
      rw [isQueryBoundP_query_iff]
      simp +contextual [surfaceKind, sourceKind, eq_comm]
    case h' =>
      intro published _
      exact route_bound _ kind (budget kind) (bounded _ kind)

/-- The complete source experiment charges the Server constructor, both initialization calls and all interpreted primitive/base work. This is separate from the reduction bills, which use the gate-free ordered experiment. -/
theorem source_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (supplied : Option Pqxdh.Bytes) (work : AuthInput → OracleComp ServerAuthSpec Result)
    (budget : Fin 9 → Nat)
    (certified : ∀ input kind, (work input).IsQueryBoundP (fun query => suffixKind query = kind) (budget kind))
    (runtime : A) :
    (surfaceExperiment setup codec checks ensureInit supplied
      (fun identity sender => PqxdhRegistrationR1Surface.program identity sender work) runtime).IsTotalQueryBound
        (qInit + (if supplied.isNone then 32 else 0) +
          ∑ kind, uniformCost caps qInit kind * programBudget budget kind) :=
  surfaceExperiment_uniform setup codec checks caps bounded ensureInit qInit initBound supplied
    _ (programBudget budget) (fun identity sender => program_bills identity sender work budget certified) runtime

/-- With zero creation and bundle caps in the seven-capability suffix, the generated source bill contains both initialization calls, four 32-byte source draws and the entire declared KEM keygen bill. -/
theorem generated_uniform_bill (caps : KemCaps) (qInit : Nat) (budget : Fin 9 → Nat)
    (noCreate : budget 1 = 0) (noBundle : budget 2 = 0) :
    (qInit + 32 + ∑ kind, uniformCost caps qInit kind * programBudget budget kind) =
      2 * qInit + 128 + caps.keygenCost + budget 0 +
        (96 + caps.encapsCost) * budget 3 + 64 * budget 4 +
        (69 * max 64 caps.decapsCost) * budget 5 + 64 * budget 6 + 64 * budget 7 := by
  rw [uniform_bill]
  simp [programBudget, noCreate, noBundle]
  omega

/-- The actual source acceptance classifier is exactly coordinate three, including refused constructor requests. -/
theorem accept_class (checks : Checks) (query : SurfaceSpec.Domain) :
    SurfaceClass checks IsAccept query ↔ surfaceKind query = 3 := by
  rcases query with coin | (⟨bytes, keyId⟩ | ⟨request, allowed⟩)
  · simp [SurfaceClass, surfaceLabel, IsAccept, serverLabel, surfaceKind]
  · cases parsed : parsePin checks bytes <;>
      simp [SurfaceClass, surfaceLabel, IsAccept, serverLabel, surfaceKind, *]
  · cases request <;> simp [SurfaceClass, surfaceLabel, IsAccept, serverLabel,
      surfaceKind, sourceKind, IsAcceptQuery]

/-- The actual source build classifier is exactly coordinate four, including refused constructor requests. -/
theorem build_class (checks : Checks) (query : SurfaceSpec.Domain) :
    SurfaceClass checks IsBuild query ↔ surfaceKind query = 4 := by
  rcases query with coin | (⟨bytes, keyId⟩ | ⟨request, allowed⟩)
  · simp [SurfaceClass, surfaceLabel, IsBuild, serverLabel, surfaceKind]
  · cases parsed : parsePin checks bytes <;>
      simp [SurfaceClass, surfaceLabel, IsBuild, serverLabel, surfaceKind, *]
  · cases request <;> simp [SurfaceClass, surfaceLabel, IsBuild, serverLabel,
      surfaceKind, sourceKind, PqxdhRegistrationResponse.IsBuild]

/-- The same actual singleton source preserves consumed-set uniqueness and pays for all accept/build attempts in its session and counter ledger. No successful-call-only bound or target-origin premise is used. -/
theorem source_ledger (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (budget : Fin 9 → Nat)
    (certified : ∀ input kind, (work input).IsQueryBoundP (fun query => suffixKind query = kind) (budget kind))
    (runtime afterRuntime : A) (created : PqxdhLiveServerConstruction.Created Unit)
    (result : Result × State KemSK)
    (supported : (some (created, result), afterRuntime) ∈ support
      (surfaceExperiment setup codec checks ensureInit supplied
        (fun identity sender => PqxdhRegistrationR1Surface.program identity sender work) runtime)) :
    result.2.shared.2.server.consumed.Nodup ∧
      result.2.shared.2.server.consumed.length ≤ budget 3 ∧
      result.2.shared.2.sessions ≤ budget 3 ∧
      setup.serverKeyId.val ≤ result.2.shared.2.server.control.last_key_id.val ∧
      result.2.shared.2.server.control.last_key_id.val ≤ setup.serverKeyId.val + budget 4 := by
  apply surfaceExperiment_ledger setup codec checks ensureInit supplied
    (fun identity sender => PqxdhRegistrationR1Surface.program identity sender work) (budget 3) (budget 4)
    ?_ ?_ runtime afterRuntime created result supported
  · intro identity sender
    apply (isQueryBoundP_congr_pred (fun query => accept_class checks query)).mpr
    simpa [programBudget] using program_bills identity sender work budget certified 3
  · intro identity sender
    apply (isQueryBoundP_congr_pred (fun query => build_class checks query)).mpr
    simpa [programBudget] using program_bills identity sender work budget certified 4

end BeaconcryptCore.Computational.PqxdhRegistrationR1Resources

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.route_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.program_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.program_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.source_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.generated_uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.generated_uniform_bill
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.accept_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.accept_class
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.build_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.build_class
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.source_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationR1Resources.source_ledger
