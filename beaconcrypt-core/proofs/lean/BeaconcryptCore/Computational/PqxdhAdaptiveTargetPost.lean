import BeaconcryptCore.Computational.PqxdhAuthenticatedEvolvingResources

/-!
The adversary chooses a target only after the original adaptive post schedule. Filtering that returned choice changes only the final Boolean; every original request, optional response and state update is retained. The existing fixed-target source theorem therefore receives a concrete post program with exactly the original query certificate.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhPhase2GeneratedDriver PqxdhAuthenticatedRootExperiment
open PqxdhKemIndCca PqxdhStatefulPhase1EufCma
variable {ι Choice Selection M P I D K X Response Shared Origin Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev Decision (Choice : Type) := Option Choice × Bool
abbrev Post (Choice Selection : Type) (baseSpec : OracleSpec ι) (S B : Nat) :=
  Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) (Decision Choice)

def choose [DecidableEq Choice] (target : Choice) (result : Decision Choice) : Bool :=
  decide (result.1 = some target) && result.2

def mapPost (post : Post Choice Selection baseSpec S B) (observe : Decision Choice → Bool) :
    PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) Selection S B :=
  fun selected reply => observe <$> post selected reply

/-- The final adaptive target test preserves every selective source-query budget, including failed and repeated calls. -/
theorem map_query_bound (post : Post Choice Selection baseSpec S B) (observe : Decision Choice → Bool)
    (selected : Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (predicate : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (mapPost post observe selected reply).IsQueryBoundP predicate budget ↔
      (post selected reply).IsQueryBoundP predicate budget :=
  isQueryBoundP_map_iff _ _ _

variable {A KemSK : Type} {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context S (B + 1))
    (post : Post Choice program.Selection baseSpec S (B + 1))

/-- The concrete target-filtered post inherits the same original caller and primitive callback certificate; no complete-observer bound is assumed. -/
def certificate (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (mapPost post Prod.snd))
    (observe : Decision Choice → Bool) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (mapPost post observe) :=
  { c with
    postBound := by
      intro selected reply kind
      exact (map_query_bound post observe selected reply _ _).mpr
        ((map_query_bound post Prod.snd selected reply _ _).mp (c.postBound selected reply kind)) }

end BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost.map_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost.map_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAdaptiveTargetPost.certificate
