import BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma

/-!
# Query accounting for the retained Phase-1 prefix

The complete retained tail makes at most three logical signing calls, and only its adaptive selector can make logical decapsulation calls. Local KEM interpretation, prekey generation, and KEM key generation preserve the signing cap because their ambient interface does not expose signing. The standard weak-EUF-CMA reduction only maps the final retained result to the selected forgery and therefore has the same signing cap.

These are structural interface bounds, not bounds on ambient base or uniform work performed inside the supplied KEM algorithms. The selector's logical decapsulation cap is stated before local interpretation; its decrypted workload is retained by the source-shaped reduction. No primitive security assumption is added, and this module proves neither cryptographic internals nor a secrecy or authentication bound. Exact three-entry logs for successful results are supplied by the separate retained writer theorem.
-/

open OracleSpec OracleComp ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma

open PqxdhEd25519EufCma PqxdhKemIndCca

variable {iota : Type} {baseSpec : OracleSpec iota} {KemSK : Type}

/-- The explicit CCA embedding agrees with the concrete nested-sum lift. -/
theorem phase1CcaLift_eq_liftComp {alpha : Type}
    (computation : OracleComp ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) alpha) :
    phase1CcaLift computation = OracleComp.liftComp computation
      (((unifSpec + baseSpec) +
        (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) + Phase1SigningSpec) := by
  unfold phase1CcaLift OracleComp.liftComp
  congr 1
  funext query
  cases query <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem phase1CcaLift_noSigningQuery {alpha : Type}
    (computation : OracleComp ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) alpha) :
    (phase1CcaLift computation).IsQueryBoundP IsPhase1SigningQuery 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [phase1CcaLift]
  | query_bind query continuation ih =>
    simp [phase1CcaLift, phase1CcaLiftImpl] at *
    simp [IsPhase1SigningQuery, ih]

/-- Logical decapsulation queries on the CCA-plus-signing interface. -/
def IsPhase1LogicalDecapsulationQuery :
    (((ℕ ⊕ iota) ⊕ MlKem768Ciphertext) ⊕ Pqxdh.Bytes) → Prop
  | .inl query => IsMlKemLogicalDecapsulationQuery query
  | .inr _ => False

noncomputable instance instDecidablePredIsPhase1LogicalDecapsulationQuery :
    DecidablePred (@IsPhase1LogicalDecapsulationQuery iota) :=
  Classical.decPred _

set_option backward.isDefEq.respectTransparency false in
theorem phase1CcaLift_decapQueryBound {alpha : Type}
    (computation : OracleComp ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) alpha) {q : ℕ}
    (bound : computation.IsQueryBoundP IsMlKemLogicalDecapsulationQuery q) :
    (phase1CcaLift computation).IsQueryBoundP IsPhase1LogicalDecapsulationQuery q := by
  induction computation using OracleComp.inductionOn generalizing q with
  | pure value => simp [phase1CcaLift]
  | query_bind query continuation ih =>
    simp [phase1CcaLift, phase1CcaLiftImpl] at *
    exact ⟨bound.1, fun u => ih u (bound.2 u)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The complete retained tail makes at most three logical signing-interface calls. -/
theorem statefulPhase1Tail_signingQueryBound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) :
    (statefulPhase1Tail kem setup selector identity before target).IsQueryBoundP
      IsPhase1SigningQuery 3 := by
  unfold statefulPhase1Tail
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 3)
    (phase1CcaLift_noSigningQuery _) ?_
  intro after _
  simp [phase1SigningQuery, IsPhase1SigningQuery, phase1CcaLift_noSigningQuery]

set_option backward.isDefEq.respectTransparency false in
/-- Setup's ambient calls cannot invoke the logical decapsulation interface. -/
theorem liftPhase1Ambient_noDecapsulationQuery {alpha : Type}
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (OracleComp.liftComp computation ((unifSpec + baseSpec) +
      (MlKem768Ciphertext →ₒ Option MlKemSharedSecret))).IsQueryBoundP
        IsMlKemLogicalDecapsulationQuery 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
    have query_route : OracleComp.liftComp
        (liftM ((unifSpec + baseSpec).query query) :
          OracleComp (unifSpec + baseSpec) ((unifSpec + baseSpec).Range query))
        ((unifSpec + baseSpec) + (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)) =
        liftM ((((unifSpec + baseSpec) +
          (MlKem768Ciphertext →ₒ Option MlKemSharedSecret)).query (.inl query))) := by
      cases query <;> rfl
    simp only [OracleComp.liftComp_bind, query_route, OracleComp.isQueryBoundP_query_bind_iff]
    simp [IsMlKemLogicalDecapsulationQuery, ih]

set_option backward.isDefEq.respectTransparency false in
/-- Every logical decapsulation call in the retained tail comes from the adaptive selector. -/
theorem statefulPhase1Tail_decapsulationQueryBound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context) {qD : ℕ}
    (selectorBound : ∀ transcript,
      (selector.mainConcrete kem transcript).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qD)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) :
    (statefulPhase1Tail kem setup selector identity before target).IsQueryBoundP
      IsPhase1LogicalDecapsulationQuery qD := by
  unfold statefulPhase1Tail
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qD)
    (phase1CcaLift_decapQueryBound _ (liftPhase1Ambient_noDecapsulationQuery _))
    ?_).mono (Nat.le_of_eq (Nat.zero_add qD))
  intro after _
  simp [phase1SigningQuery, IsPhase1LogicalDecapsulationQuery,
    phase1CcaLift_decapQueryBound, selectorBound]

set_option backward.isDefEq.respectTransparency false in
theorem phase1BaseLift_noSigningQuery {alpha : Type}
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (liftM computation : OracleComp ((unifSpec + baseSpec) + Phase1SigningSpec) alpha).IsQueryBoundP
      IsPhase1SigningQuery 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query continuation ih =>
    simp only [liftM_bind, phase1Base_query_lift, OracleComp.isQueryBoundP_query_bind_iff]
    simp [IsPhase1SigningQuery, ih]
set_option backward.isDefEq.respectTransparency false in
/-- Local KEM interpretation retains the three-call signing cap, with arbitrary ambient KEM work. -/
theorem localStatefulPhase1Tail_signingQueryBound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) (before : PrivatePrekey setup.PrivatePre)
    (target : TargetKemPublicKey) (sk : KemSK) :
    (localStatefulPhase1Tail kem setup selector identity before target sk).IsQueryBoundP
      IsPhase1SigningQuery 3 := by
  unfold localStatefulPhase1Tail
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 3)
    (phase1BaseLift_noSigningQuery _) ?_
  intro after _
  simp [phase1ForwardSigningQuery, IsPhase1SigningQuery, phase1BaseLift_noSigningQuery]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit ambient lift used for prekey and KEM key generation cannot sign. -/
theorem phase1BaseLiftComp_noSigningQuery {alpha : Type}
    (computation : OracleComp (unifSpec + baseSpec) alpha) :
    (OracleComp.liftComp computation ((unifSpec + baseSpec) + Phase1SigningSpec)).IsQueryBoundP
      IsPhase1SigningQuery 0 := by
  induction computation using OracleComp.inductionOn
  all_goals simp_all only [OracleComp.liftComp_pure, OracleComp.liftComp_bind,
    phase1Base_query_liftComp, OracleComp.isQueryBoundP_pure,
    OracleComp.isQueryBoundP_query_bind_iff, IsPhase1SigningQuery,
    not_false_eq_true, true_or, ite_false, true_and]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Prekey generation and locally owned KEM work add no calls to the signing interface. -/
theorem statefulPhase1Client_signingQueryBound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) :
    (statefulPhase1Client kem setup selector identity).IsQueryBoundP IsPhase1SigningQuery 3 := by
  unfold statefulPhase1Client
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 3)
    (phase1BaseLiftComp_noSigningQuery _) fun before _ => ?_
  refine OracleComp.isQueryBoundP_bind (n := 0) (m := 3)
    (phase1BaseLiftComp_noSigningQuery _) fun ⟨target, sk⟩ _ => ?_
  simpa only [simulateQ_statefulPhase1Tail_localKem] using
    localStatefulPhase1Tail_signingQueryBound kem setup selector identity before target sk

set_option backward.isDefEq.respectTransparency false in
/-- Selecting the forgery from the complete retained result adds no oracle calls. -/
theorem statefulPhase1ToEUFCMA_signingQueryBound {SecretKey : Type}
    (sigAlg : Ed25519Scheme (unifSpec + baseSpec) SecretKey)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (selector : StatefulPhase1Selector kem setup.Context)
    (identity : Ed25519PublicKey) :
    ((statefulPhase1ToEUFCMA sigAlg kem setup selector).main identity).IsQueryBoundP
      IsPhase1SigningQuery 3 := by
  simpa only [statefulPhase1ToEUFCMA, OracleComp.isQueryBoundP_map_iff] using
    statefulPhase1Client_signingQueryBound kem setup selector identity

/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1Tail_signingQueryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1Tail_signingQueryBound
/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1Tail_decapsulationQueryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1Tail_decapsulationQueryBound
/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.localStatefulPhase1Tail_signingQueryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms localStatefulPhase1Tail_signingQueryBound
/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1Client_signingQueryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1Client_signingQueryBound
/--
info: 'BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma.statefulPhase1ToEUFCMA_signingQueryBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms statefulPhase1ToEUFCMA_signingQueryBound

end BeaconcryptCore.Computational.PqxdhStatefulPhase1EufCma
