import BeaconcryptCore.Computational.PqxdhJointKdfGame
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.ProgrammingOracle
import VCVio.OracleComp.QueryTracking.SubSpec
import VCVio.ProgramLogic.Relational.ProgrammingOracle

/-!
# One-hidden-coordinate PQXDH root games

This module isolates the computational step after the final PQXDH coordinate has already been
replaced by an independent uniform 32-byte value.  It retains the four known 32-byte DH
coordinates and the exact source encoding
`FF^32 || DH1 || DH2 || DH3 || DH4 || hidden32`; no other transcript field is serialized into
the HKDF address.

The only primitive-security endpoint is the fixed BeaconCrypt HKDF-SHA-512/no-salt joint-stream
advantage from `PqxdhJointKdfGame`.  Nothing here proves HKDF, HMAC, SHA-512, or ML-KEM security.
-/

open OracleComp OracleSpec ENNReal

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhHiddenRoot

open PqxdhJointKdf PqxdhJointKdfGame

/-- The one independent, uniform final coordinate in the Stage-3 PQXDH game. -/
abbrev HiddenRootCoordinate := List.Vector UInt8 32

/-- The four fixed, known 32-byte coordinates preceding the hidden coordinate. -/
structure KnownPqxdhRootCoordinates where
  dh1 : HiddenRootCoordinate
  dh2 : HiddenRootCoordinate
  dh3 : HiddenRootCoordinate
  dh4 : HiddenRootCoordinate

/-- The fixed 160-byte part of the exact source PQXDH input. -/
def knownRootPrefix (known : KnownPqxdhRootCoordinates) : Pqxdh.Bytes :=
  Pqxdh.padFF32 ++ known.dh1.toList ++ known.dh2.toList ++
    known.dh3.toList ++ known.dh4.toList

/-- The exact 192-byte source input with one hidden final coordinate. -/
def hiddenRootIKM (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) : Pqxdh.Bytes :=
  Pqxdh.pqxdhIKM known.dh1.toList known.dh2.toList known.dh3.toList
    known.dh4.toList hidden.toList

/-- The exact root-domain joint-stream address for the one-hidden-coordinate input. -/
def hiddenRootAddress (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) : JointKdfAddress :=
  FixedHkdfDomain.pqxdh.address (hiddenRootIKM known hidden)

@[simp] theorem knownRootPrefix_length (known : KnownPqxdhRootCoordinates) :
    (knownRootPrefix known).length = 160 := by
  simp [knownRootPrefix, Pqxdh.padFF32]

theorem hiddenRootIKM_eq_prefix_append
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    hiddenRootIKM known hidden = knownRootPrefix known ++ hidden.toList := by
  rfl

/-- The source-faithful input has exactly the production 192-byte width. -/
@[simp] theorem hiddenRootIKM_length (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) :
    (hiddenRootIKM known hidden).length = 192 := by
  exact Pqxdh.pqxdhIKM_length known.dh1.toList_length known.dh2.toList_length
    known.dh3.toList_length known.dh4.toList_length hidden.toList_length

/-- Fixing the first four coordinates makes the exact encoding injective in `hidden32`. -/
theorem hiddenRootIKM_injective (known : KnownPqxdhRootCoordinates) :
    Function.Injective (hiddenRootIKM known) := by
  intro left right equality
  apply List.Vector.toList_injective
  have dropped := congrArg (List.drop 160) equality
  simpa [hiddenRootIKM_eq_prefix_append, knownRootPrefix_length] using dropped

/-- The canonical root address remains injective in the hidden coordinate. -/
theorem hiddenRootAddress_injective (known : KnownPqxdhRootCoordinates) :
    Function.Injective (hiddenRootAddress known) := by
  intro left right equality
  apply hiddenRootIKM_injective known
  exact rootAddress_injective equality

/-- Every hidden-root address is in the exact `INFO_PQ` domain. -/
@[simp] theorem hiddenRootAddress_eq_rootAddress
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    hiddenRootAddress known hidden = rootAddress (hiddenRootIKM known hidden) := by
  rfl

/-- A hidden-root address cannot alias any symmetric-ratchet address. -/
theorem hiddenRootAddress_ne_ratchetAddress
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (ratchetInput : Pqxdh.Bytes) :
    hiddenRootAddress known hidden ≠ ratchetAddress ratchetInput := by
  exact rootAddress_ne_ratchetAddress _ _

/-- Parse the unique final coordinate only when the input has the exact fixed-width root layout. -/
def parseHiddenRootCoordinate? (known : KnownPqxdhRootCoordinates)
    (input : Pqxdh.Bytes) : Option HiddenRootCoordinate :=
  if h : input.length = 192 ∧ input.take 160 = knownRootPrefix known then
    some ⟨input.drop 160, by simp [h.1]⟩
  else
    none

/-- The parser accepts exactly the source encoding with the specified known coordinates. -/
theorem parseHiddenRootCoordinate?_eq_some_iff
    (known : KnownPqxdhRootCoordinates) (input : Pqxdh.Bytes)
    (hidden : HiddenRootCoordinate) :
    parseHiddenRootCoordinate? known input = some hidden ↔
      input = hiddenRootIKM known hidden := by
  unfold parseHiddenRootCoordinate?
  split
  · rename_i layout
    constructor
    · intro parsed
      have vectorEquality :
          (⟨input.drop 160, by simp [layout.1]⟩ : HiddenRootCoordinate) = hidden :=
        Option.some.inj parsed
      have dropped : input.drop 160 = hidden.toList :=
        congrArg List.Vector.toList vectorEquality
      calc
        input = input.take 160 ++ input.drop 160 :=
          (List.take_append_drop 160 input).symm
        _ = knownRootPrefix known ++ hidden.toList :=
          congrArg₂ (fun left right => left ++ right) layout.2 dropped
        _ = hiddenRootIKM known hidden :=
          (hiddenRootIKM_eq_prefix_append known hidden).symm
    · intro encoded
      subst input
      congr 1
      apply List.Vector.toList_injective
      simp [hiddenRootIKM_eq_prefix_append, knownRootPrefix_length]
  · rename_i notLayout
    constructor
    · simp
    · intro encoded
      subst input
      exfalso
      apply notLayout
      constructor
      · exact hiddenRootIKM_length known hidden
      · simp [hiddenRootIKM_eq_prefix_append, knownRootPrefix_length]

/-- Extract one candidate from every logical root-domain projection request. -/
def rootQueryCandidate? (known : KnownPqxdhRootCoordinates)
    (query : JointKdfViewQuery) : Option HiddenRootCoordinate :=
  match query.domain with
  | .pqxdh => parseHiddenRootCoordinate? known query.input
  | .ratchet => none

/-- Candidate extraction recognizes every projection at exactly the hidden root address. -/
theorem rootQueryCandidate?_eq_some_iff
    (known : KnownPqxdhRootCoordinates) (query : JointKdfViewQuery)
    (hidden : HiddenRootCoordinate) :
    rootQueryCandidate? known query = some hidden ↔
      query.address = hiddenRootAddress known hidden := by
  rcases query with ⟨input, domain, projection⟩
  cases domain with
  | pqxdh =>
      constructor
      · intro candidate
        change rootAddress input = rootAddress (hiddenRootIKM known hidden)
        apply congrArg rootAddress
        exact (parseHiddenRootCoordinate?_eq_some_iff known input hidden).mp candidate
      · intro addressEquality
        apply (parseHiddenRootCoordinate?_eq_some_iff known input hidden).mpr
        exact rootAddress_injective addressEquality
  | ratchet =>
      constructor
      · simp [rootQueryCandidate?]
      · intro addressEquality
        exact (rootAddress_ne_ratchetAddress
          (hiddenRootIKM known hidden) input addressEquality.symm).elim

/-! ## Exact source query classes and budgets -/

/-- Logical adversary projection requests under the PQXDH root domain. -/
def IsHiddenRootDomainQuery : JointKdfViewAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr query => query.domain = .pqxdh

instance : DecidablePred IsHiddenRootDomainQuery
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (query.domain = .pqxdh))

/-- Logical adversary projection requests under the symmetric-ratchet domain. -/
def IsHiddenRootSymmetricQuery : JointKdfViewAdversarySpec.Domain → Prop
  | .inl _ => False
  | .inr query => query.domain = .ratchet

instance : DecidablePred IsHiddenRootSymmetricQuery
  | .inl _ => isFalse id
  | .inr query => inferInstanceAs (Decidable (query.domain = .ratchet))

/-- Every public projection request lies in exactly one of the two source domains. -/
theorem isProjectionQuery_iff_root_or_symmetric
    (query : JointKdfViewAdversarySpec.Domain) :
    IsJointKdfViewProjectionQuery query ↔
      IsHiddenRootDomainQuery query ∨ IsHiddenRootSymmetricQuery query := by
  rcases query with randomQuery | viewQuery
  · simp [IsJointKdfViewProjectionQuery, IsHiddenRootDomainQuery,
      IsHiddenRootSymmetricQuery]
  · rcases viewQuery with ⟨input, domain, projection⟩
    cases domain <;>
      simp [IsJointKdfViewProjectionQuery, IsHiddenRootDomainQuery,
        IsHiddenRootSymmetricQuery]

/-- A Boolean source adversary with separate logical randomness, root, and symmetric budgets.

`publicContext` is an opaque fixed parameter.  With no byte serialization operation in this
interface, it is passed unchanged and cannot be added to the HKDF address by the game.
-/
structure HiddenRootSourceAdversary (PublicContext : Type)
    (qU qRoot qSym : ℕ) where
  main : KnownPqxdhRootCoordinates → PublicContext → HiddenRootCoordinate →
    OracleComp JointKdfViewAdversarySpec Bool
  uniformQueryBound : ∀ known publicContext root,
    (main known publicContext root).IsQueryBoundP IsJointKdfViewUniformQuery qU
  rootQueryBound : ∀ known publicContext root,
    (main known publicContext root).IsQueryBoundP IsHiddenRootDomainQuery qRoot
  symmetricQueryBound : ∀ known publicContext root,
    (main known publicContext root).IsQueryBoundP IsHiddenRootSymmetricQuery qSym

/-- Separate domain budgets imply the exact `qRoot + qSym` projection-query budget. -/
theorem isProjectionQueryBound_of_root_and_symmetric_bounds {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qRoot qSym : ℕ}
    (hroot : computation.IsQueryBoundP IsHiddenRootDomainQuery qRoot)
    (hsym : computation.IsQueryBoundP IsHiddenRootSymmetricQuery qSym) :
    computation.IsQueryBoundP IsJointKdfViewProjectionQuery (qRoot + qSym) := by
  induction computation using OracleComp.inductionOn generalizing qRoot qSym with
  | pure output => trivial
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hroot hsym ⊢
      rcases query with randomQuery | viewQuery
      · simp [IsHiddenRootDomainQuery, IsHiddenRootSymmetricQuery,
          IsJointKdfViewProjectionQuery] at hroot hsym ⊢
        intro response
        exact ih response (hroot response) (hsym response)
      · rcases viewQuery with ⟨input, domain, projection⟩
        cases domain
        · simp [IsHiddenRootDomainQuery, IsHiddenRootSymmetricQuery,
            IsJointKdfViewProjectionQuery] at hroot hsym ⊢
          refine ⟨Or.inl hroot.1, fun response => ?_⟩
          exact (ih response (hroot.2 response) (hsym response)).mono (by omega)
        · simp [IsHiddenRootDomainQuery, IsHiddenRootSymmetricQuery,
            IsJointKdfViewProjectionQuery] at hroot hsym ⊢
          refine ⟨Or.inr hsym.1, fun response => ?_⟩
          exact (ih response (hroot response) (hsym.2 response)).mono (by omega)

/-- Primitive complete-stream requests in the exact PQXDH root domain. -/
def IsFixedHkdfRootStreamQuery :
    FixedHkdfSha512JointStreamSpec.Domain → Prop
  | .inl _ => False
  | .inr address => address.info = Pqxdh.INFO_PQ

instance : DecidablePred IsFixedHkdfRootStreamQuery
  | .inl _ => isFalse id
  | .inr address => inferInstanceAs (Decidable (address.info = Pqxdh.INFO_PQ))

/-- Primitive complete-stream requests in the exact symmetric-ratchet domain. -/
def IsFixedHkdfSymmetricStreamQuery :
    FixedHkdfSha512JointStreamSpec.Domain → Prop
  | .inl _ => False
  | .inr address => address.info = Pqxdh.INFO_R

instance : DecidablePred IsFixedHkdfSymmetricStreamQuery
  | .inl _ => isFalse id
  | .inr address => inferInstanceAs (Decidable (address.info = Pqxdh.INFO_R))

/-- Forwarding preserves the root-domain indicator one-for-one. -/
theorem jointKdfViewForwardImpl_root_query_bound_step
    (query : JointKdfViewAdversarySpec.Domain) :
    (jointKdfViewForwardImpl query).IsQueryBoundP
      IsFixedHkdfRootStreamQuery
      (if IsHiddenRootDomainQuery query then 1 else 0) := by
  rcases query with randomQuery | viewQuery
  · simp only [jointKdfViewForwardImpl_uniform, IsHiddenRootDomainQuery, if_false]
    change (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
      IsFixedHkdfRootStreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfRootStreamQuery]
  · by_cases hroot : viewQuery.domain = .pqxdh
    · simp only [jointKdfViewForwardImpl_projection, IsHiddenRootDomainQuery,
        hroot, if_true, bind_pure_comp]
      change (viewQuery.project <$> (liftM
        (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr viewQuery.address)))).IsQueryBoundP
        IsFixedHkdfRootStreamQuery 1
      rw [OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff
        (p := IsFixedHkdfRootStreamQuery) (.inr viewQuery.address) 1).2
          (by simp [IsFixedHkdfRootStreamQuery, JointKdfViewQuery.address,
            hroot, FixedHkdfDomain.address])
    · simp only [jointKdfViewForwardImpl_projection, IsHiddenRootDomainQuery,
        hroot, if_false, bind_pure_comp]
      change (viewQuery.project <$> (liftM
        (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr viewQuery.address)))).IsQueryBoundP
        IsFixedHkdfRootStreamQuery 0
      rw [OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff
        (p := IsFixedHkdfRootStreamQuery) (.inr viewQuery.address) 0).2
          (by intro hinfo
              exfalso
              apply hroot
              apply FixedHkdfDomain.info_injective
              simpa [IsFixedHkdfRootStreamQuery, JointKdfViewQuery.address,
                FixedHkdfDomain.address] using hinfo)

/-- Forwarding preserves the symmetric-domain indicator one-for-one. -/
theorem jointKdfViewForwardImpl_symmetric_query_bound_step
    (query : JointKdfViewAdversarySpec.Domain) :
    (jointKdfViewForwardImpl query).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery
      (if IsHiddenRootSymmetricQuery query then 1 else 0) := by
  rcases query with randomQuery | viewQuery
  · simp only [jointKdfViewForwardImpl_uniform, IsHiddenRootSymmetricQuery, if_false]
    change (liftM
      (FixedHkdfSha512JointStreamSpec.query (.inl randomQuery)) :
        OracleComp FixedHkdfSha512JointStreamSpec
          (FixedHkdfSha512JointStreamSpec.Range (.inl randomQuery))).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery 0
    rw [OracleComp.isQueryBoundP_query_iff]
    simp [IsFixedHkdfSymmetricStreamQuery]
  · by_cases hsym : viewQuery.domain = .ratchet
    · simp only [jointKdfViewForwardImpl_projection, IsHiddenRootSymmetricQuery,
        hsym, if_true, bind_pure_comp]
      change (viewQuery.project <$> (liftM
        (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr viewQuery.address)))).IsQueryBoundP
        IsFixedHkdfSymmetricStreamQuery 1
      rw [OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff
        (p := IsFixedHkdfSymmetricStreamQuery) (.inr viewQuery.address) 1).2
          (by simp [IsFixedHkdfSymmetricStreamQuery, JointKdfViewQuery.address,
            hsym, FixedHkdfDomain.address])
    · simp only [jointKdfViewForwardImpl_projection, IsHiddenRootSymmetricQuery,
        hsym, if_false, bind_pure_comp]
      change (viewQuery.project <$> (liftM
        (FixedHkdfSha512JointStreamSpec.query (.inr viewQuery.address)) :
          OracleComp FixedHkdfSha512JointStreamSpec
            (FixedHkdfSha512JointStreamSpec.Range
              (.inr viewQuery.address)))).IsQueryBoundP
        IsFixedHkdfSymmetricStreamQuery 0
      rw [OracleComp.isQueryBoundP_map_iff]
      exact (OracleComp.isQueryBoundP_query_iff
        (p := IsFixedHkdfSymmetricStreamQuery) (.inr viewQuery.address) 0).2
          (by intro hinfo
              exfalso
              apply hsym
              apply FixedHkdfDomain.info_injective
              simpa [IsFixedHkdfSymmetricStreamQuery, JointKdfViewQuery.address,
                FixedHkdfDomain.address] using hinfo)

/-- Forwarding preserves the logical root-domain budget without loss. -/
theorem jointKdfViewForwardImpl_root_query_bound {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qRoot : ℕ}
    (hbound : computation.IsQueryBoundP IsHiddenRootDomainQuery qRoot) :
    (simulateQ jointKdfViewForwardImpl computation).IsQueryBoundP
      IsFixedHkdfRootStreamQuery qRoot := by
  refine hbound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using jointKdfViewForwardImpl_root_query_bound_step query
  · intro query hquery
    simpa [hquery] using jointKdfViewForwardImpl_root_query_bound_step query

/-- Forwarding preserves the logical symmetric-domain budget without loss. -/
theorem jointKdfViewForwardImpl_symmetric_query_bound {alpha : Type}
    {computation : OracleComp JointKdfViewAdversarySpec alpha} {qSym : ℕ}
    (hbound : computation.IsQueryBoundP IsHiddenRootSymmetricQuery qSym) :
    (simulateQ jointKdfViewForwardImpl computation).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery qSym := by
  refine hbound.simulateQ_of_step ?_ ?_
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_symmetric_query_bound_step query
  · intro query hquery
    simpa [hquery] using
      jointKdfViewForwardImpl_symmetric_query_bound_step query

/-- Forget the domain split while retaining its exact summed public-view budget. -/
def HiddenRootSourceAdversary.toJointKdfViewAdversary
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (root : HiddenRootCoordinate) : JointKdfViewAdversary qU (qRoot + qSym) where
  main := adversary.main known publicContext root
  uniformQueryBound := adversary.uniformQueryBound known publicContext root
  projectionQueryBound := isProjectionQueryBound_of_root_and_symmetric_bounds
    (adversary.rootQueryBound known publicContext root)
    (adversary.symmetricQueryBound known publicContext root)

/-! ## Reduction into the fixed HKDF-SHA-512 joint-stream challenge -/

/-- The one honest complete-stream lookup owned by the reduction. -/
def queryHiddenRootStream (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) :
    OracleComp FixedHkdfSha512JointStreamSpec JointKdfStream :=
  liftM (FixedHkdfSha512JointStreamSpec.query
    (.inr (hiddenRootAddress known hidden)))

/-- Sample the one hidden coordinate, derive the honest root, then forward the source view. -/
noncomputable def hiddenRootReductionMain
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    OracleComp FixedHkdfSha512JointStreamSpec Bool := do
  let hidden ← OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
    FixedHkdfSha512JointStreamSpec
  let stream ← queryHiddenRootStream known hidden
  simulateQ jointKdfViewForwardImpl
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))

/-- Lifting the hidden-coordinate sampler costs exactly its 32 source uniform queries. -/
theorem liftHiddenRootCoordinate_uniform_query_bound :
    (OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UniformQuery 32 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec)
    (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => True) (q := IsFixedHkdfSha512UniformQuery)
    (hpq := by
      intro query
      simp [IsFixedHkdfSha512UniformQuery, SubSpec.onQuery])
    (uniformFixedBytes_isTotalQueryBound 32).isQueryBoundP

/-- Lifting the hidden-coordinate sampler makes no primitive root-stream query. -/
theorem liftHiddenRootCoordinate_no_root_query :
    (OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfRootStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec)
    (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfRootStreamQuery)
    (hpq := by
      intro query
      simp [IsFixedHkdfRootStreamQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false ($ᵗ HiddenRootCoordinate) 0)

/-- Lifting the hidden-coordinate sampler makes no primitive symmetric-stream query. -/
theorem liftHiddenRootCoordinate_no_symmetric_query :
    (OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSymmetricStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec)
    (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSymmetricStreamQuery)
    (hpq := by
      intro query
      simp [IsFixedHkdfSymmetricStreamQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false ($ᵗ HiddenRootCoordinate) 0)

/-- Lifting the hidden-coordinate sampler makes no complete-stream query. -/
theorem liftHiddenRootCoordinate_no_stream_query :
    (OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512StreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec)
    (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSha512StreamQuery)
    (hpq := by
      intro query
      simp [IsFixedHkdfSha512StreamQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false ($ᵗ HiddenRootCoordinate) 0)

/-- Lifting the hidden-coordinate sampler emits no raw stream address. -/
theorem liftHiddenRootCoordinate_no_untyped_stream_query :
    (OracleComp.liftComp ($ᵗ HiddenRootCoordinate)
      FixedHkdfSha512JointStreamSpec).IsQueryBoundP
        IsFixedHkdfSha512UntypedStreamQuery 0 := by
  exact OracleComp.IsQueryBoundP.liftComp_subSpec
    (spec := unifSpec)
    (superSpec := FixedHkdfSha512JointStreamSpec)
    (p := fun _ => False) (q := IsFixedHkdfSha512UntypedStreamQuery)
    (hpq := by
      intro query
      simp [IsFixedHkdfSha512UntypedStreamQuery, SubSpec.onQuery])
    (OracleComp.isQueryBoundP_false ($ᵗ HiddenRootCoordinate) 0)

/-- The honest root lookup consumes no adversary-uniform query. -/
theorem queryHiddenRootStream_no_uniform_query
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    (queryHiddenRootStream known hidden).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery 0 := by
  unfold queryHiddenRootStream
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsFixedHkdfSha512UniformQuery)
    (.inr (hiddenRootAddress known hidden)) 0).2
      (by simp [IsFixedHkdfSha512UniformQuery])

/-- The honest root lookup contributes exactly one root-domain stream request. -/
theorem queryHiddenRootStream_root_query_bound
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    (queryHiddenRootStream known hidden).IsQueryBoundP
      IsFixedHkdfRootStreamQuery 1 := by
  unfold queryHiddenRootStream
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsFixedHkdfRootStreamQuery)
    (.inr (hiddenRootAddress known hidden)) 1).2
      (by simp [IsFixedHkdfRootStreamQuery, hiddenRootAddress,
        FixedHkdfDomain.address])

/-- The honest root lookup contributes no symmetric-domain request. -/
theorem queryHiddenRootStream_no_symmetric_query
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    (queryHiddenRootStream known hidden).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery 0 := by
  unfold queryHiddenRootStream
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsFixedHkdfSymmetricStreamQuery)
    (.inr (hiddenRootAddress known hidden)) 0).2
      (by simp [IsFixedHkdfSymmetricStreamQuery, hiddenRootAddress,
        FixedHkdfDomain.address, Pqxdh.INFO_PQ_ne_INFO_R])

/-- The honest root lookup contributes exactly one complete-stream request. -/
theorem queryHiddenRootStream_stream_query_bound
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    (queryHiddenRootStream known hidden).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery 1 := by
  unfold queryHiddenRootStream
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsFixedHkdfSha512StreamQuery)
    (.inr (hiddenRootAddress known hidden)) 1).2
      (by simp [IsFixedHkdfSha512StreamQuery])

/-- The reduction-owned honest lookup is in the exact `INFO_PQ` address image. -/
theorem queryHiddenRootStream_no_untyped_stream_query
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    (queryHiddenRootStream known hidden).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  unfold queryHiddenRootStream
  exact (OracleComp.isQueryBoundP_query_iff
    (p := IsFixedHkdfSha512UntypedStreamQuery)
    (.inr (hiddenRootAddress known hidden)) 0).2
      (by simp [IsFixedHkdfSha512UntypedStreamQuery, hiddenRootAddress,
        FixedHkdfDomain.address])

/-- The reduction uses the source adversary's randomness plus 32 owned hidden-coordinate bytes. -/
theorem hiddenRootReductionMain_uniform_query_bound
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReductionMain adversary known publicContext).IsQueryBoundP
      IsFixedHkdfSha512UniformQuery (qU + 32) := by
  unfold hiddenRootReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 32) (m := qU)
    liftHiddenRootCoordinate_uniform_query_bound ?_).mono (by omega)
  intro hidden hiddenSupport
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qU)
    (queryHiddenRootStream_no_uniform_query known hidden) ?_).mono (by omega)
  intro stream streamSupport
  exact jointKdfViewForwardImpl_uniform_query_bound
    (adversary.uniformQueryBound known publicContext
      (JointKdfProjection.first32.project stream))

/-- The honest derivation adds exactly one primitive root request to the adversary's `qRoot`. -/
theorem hiddenRootReductionMain_root_query_bound
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReductionMain adversary known publicContext).IsQueryBoundP
      IsFixedHkdfRootStreamQuery (qRoot + 1) := by
  unfold hiddenRootReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qRoot + 1)
    liftHiddenRootCoordinate_no_root_query ?_).mono (by omega)
  intro hidden hiddenSupport
  refine (OracleComp.isQueryBoundP_bind (n := 1) (m := qRoot)
    (queryHiddenRootStream_root_query_bound known hidden) ?_).mono (by omega)
  intro stream streamSupport
  exact jointKdfViewForwardImpl_root_query_bound
    (adversary.rootQueryBound known publicContext
      (JointKdfProjection.first32.project stream))

/-- The reduction preserves the adversary's symmetric-domain budget exactly. -/
theorem hiddenRootReductionMain_symmetric_query_bound
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReductionMain adversary known publicContext).IsQueryBoundP
      IsFixedHkdfSymmetricStreamQuery qSym := by
  unfold hiddenRootReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qSym)
    liftHiddenRootCoordinate_no_symmetric_query ?_).mono (by omega)
  intro hidden hiddenSupport
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qSym)
    (queryHiddenRootStream_no_symmetric_query known hidden) ?_).mono (by omega)
  intro stream streamSupport
  exact jointKdfViewForwardImpl_symmetric_query_bound
    (adversary.symmetricQueryBound known publicContext
      (JointKdfProjection.first32.project stream))

/-- Total complete-stream accounting is `qRoot + qSym + 1`, with factor-one forwarding. -/
theorem hiddenRootReductionMain_stream_query_bound
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReductionMain adversary known publicContext).IsQueryBoundP
      IsFixedHkdfSha512StreamQuery (qRoot + qSym + 1) := by
  unfold hiddenRootReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := qRoot + qSym + 1)
    liftHiddenRootCoordinate_no_stream_query ?_).mono (by omega)
  intro hidden hiddenSupport
  refine (OracleComp.isQueryBoundP_bind (n := 1) (m := qRoot + qSym)
    (queryHiddenRootStream_stream_query_bound known hidden) ?_).mono (by omega)
  intro stream streamSupport
  exact jointKdfViewForwardImpl_stream_query_bound
    (isProjectionQueryBound_of_root_and_symmetric_bounds
      (adversary.rootQueryBound known publicContext
        (JointKdfProjection.first32.project stream))
      (adversary.symmetricQueryBound known publicContext
        (JointKdfProjection.first32.project stream)))

/-- The complete hidden-root reduction emits only the source `INFO_PQ` and `INFO_R` images. -/
theorem hiddenRootReductionMain_no_untyped_stream_queries
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReductionMain adversary known publicContext).IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  unfold hiddenRootReductionMain
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    liftHiddenRootCoordinate_no_untyped_stream_query ?_).mono (by omega)
  intro hidden _hiddenSupport
  refine (OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (queryHiddenRootStream_no_untyped_stream_query known hidden) ?_).mono (by omega)
  intro stream _streamSupport
  exact jointKdfViewForwardImpl_no_untyped_queries
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))

/-- Bounded primitive distinguisher used by the fixed-HKDF-SHA-512 endpoint. -/
noncomputable def hiddenRootReduction
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    FixedHkdfSha512JointStreamAdversary (qU + 32) (qRoot + qSym + 1) where
  main := hiddenRootReductionMain adversary known publicContext
  uniformQueryBound := hiddenRootReductionMain_uniform_query_bound
    adversary known publicContext
  streamQueryBound := hiddenRootReductionMain_stream_query_bound
    adversary known publicContext

/-- The packaged primitive distinguisher preserves the complete typed-address invariant. -/
theorem hiddenRootReduction_no_untyped_stream_queries
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootReduction adversary known publicContext).main.IsQueryBoundP
      IsFixedHkdfSha512UntypedStreamQuery 0 := by
  exact hiddenRootReductionMain_no_untyped_stream_queries
    adversary known publicContext

/-- Production's 32-byte root wrapper, retained explicitly in the source-shaped real game. -/
def productionHiddenRoot (source : FixedHkdfSha512NoSaltSource)
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    HiddenRootCoordinate :=
  ⟨Pqxdh.rootSecret source.crypto (hiddenRootIKM known hidden),
    Pqxdh.rootSecret_length source.crypto _⟩

/-- The production root wrapper equals the first projection of its one complete real stream. -/
theorem productionHiddenRoot_eq_first32_realStream
    (source : FixedHkdfSha512NoSaltSource)
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate) :
    productionHiddenRoot source known hidden =
      JointKdfProjection.first32.project
        (productionStream source.crypto (hiddenRootAddress known hidden)) := by
  apply List.Vector.toList_injective
  exact source.rootSecret_eq_realStream (hiddenRootIKM known hidden)

/-- Source-faithful fixed-HKDF root view after the final coordinate is uniform. -/
noncomputable def hiddenRootRealGame
    (source : FixedHkdfSha512NoSaltSource)
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool := do
  let hidden ← $ᵗ HiddenRootCoordinate
  simulateQ (jointKdfViewRealImpl source)
    (adversary.main known publicContext
      (productionHiddenRoot source known hidden))

/-- Shared lazy-stream root view: the honest lookup and all adversary projections share one cache. -/
noncomputable def hiddenRootSharedRandomGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool :=
  (simulateQ fixedHkdfSha512JointStreamRandomImpl
    (hiddenRootReductionMain adversary known publicContext)).run' ∅

/-- Independent-root view: the root is uniform and the adversary's lazy stream cache starts empty. -/
noncomputable def hiddenRootIndependentGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool := do
  let _hidden ← $ᵗ HiddenRootCoordinate
  let root ← $ᵗ HiddenRootCoordinate
  (simulateQ jointKdfViewRandomImpl
    (adversary.main known publicContext root)).run' ∅

/-- Distinguishing advantage between the production root view and an independent uniform root. -/
noncomputable def hiddenRootAdvantage
    (source : FixedHkdfSha512NoSaltSource)
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) : ℝ :=
  (hiddenRootRealGame source adversary known publicContext).boolDistAdvantage
    (hiddenRootIndependentGame adversary known publicContext)

/-- The reduction's fixed-HKDF real experiment is exactly the source-shaped production game. -/
theorem hiddenRootRealGame_eq_fixedHkdfSha512JointStreamRealExp
    (source : FixedHkdfSha512NoSaltSource)
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    hiddenRootRealGame source adversary known publicContext =
      fixedHkdfSha512JointStreamRealExp source
        (hiddenRootReduction adversary known publicContext) := by
  simp [hiddenRootRealGame, fixedHkdfSha512JointStreamRealExp,
    hiddenRootReduction, hiddenRootReductionMain, queryHiddenRootStream,
    fixedHkdfSha512JointStreamRealImpl, jointKdfViewRealImpl,
    productionHiddenRoot_eq_first32_realStream,
    QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]

/-- The reduction's random experiment is definitionally the shared lazy-stream root game. -/
theorem hiddenRootSharedRandomGame_eq_fixedHkdfSha512JointStreamRandomExp
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    hiddenRootSharedRandomGame adversary known publicContext =
      fixedHkdfSha512JointStreamRandomExp
        (hiddenRootReduction adversary known publicContext) := by
  rfl

/-! ## Uniform first-projection lemma -/

/-- Split one 76-byte stream bijectively into its first 32 bytes and remaining 44 bytes. -/
def jointKdfStreamSplitEquiv :
    JointKdfStream ≃ (HiddenRootCoordinate × List.Vector UInt8 44) where
  toFun stream := (List.Vector.take 32 stream, List.Vector.drop 32 stream)
  invFun parts := parts.1 ++ parts.2
  left_inv stream := by
    apply List.Vector.toList_injective
    change List.take 32 stream.toList ++ List.drop 32 stream.toList = stream.toList
    exact List.take_append_drop 32 stream.toList
  right_inv parts := by
    apply Prod.ext
    · apply List.Vector.toList_injective
      change List.take 32 (parts.1.toList ++ parts.2.toList) = parts.1.toList
      simpa using (List.take_left
        (l₁ := parts.1.toList) (l₂ := parts.2.toList))
    · apply List.Vector.toList_injective
      change List.drop 32 (parts.1.toList ++ parts.2.toList) = parts.2.toList
      simpa using (List.drop_left
        (l₁ := parts.1.toList) (l₂ := parts.2.toList))

/-- The split equivalence's first component is exactly the public first-32 projection. -/
theorem jointKdfStreamSplitEquiv_fst (stream : JointKdfStream) :
    (jointKdfStreamSplitEquiv stream).1 =
      JointKdfProjection.first32.project stream := by
  rfl

/-- The first 32 bytes of a uniform 76-byte stream are exactly uniform 32 bytes. -/
theorem evalDist_first32_uniformJointKdfStream :
    𝒟[JointKdfProjection.first32.project <$> ($ᵗ JointKdfStream)] =
      𝒟[$ᵗ HiddenRootCoordinate] := by
  calc
    𝒟[JointKdfProjection.first32.project <$> ($ᵗ JointKdfStream)] =
        𝒟[Prod.fst <$> (jointKdfStreamSplitEquiv <$> ($ᵗ JointKdfStream))] := by
      simp only [Functor.map_map, Function.comp_def,
        jointKdfStreamSplitEquiv_fst]
      rfl
    _ = 𝒟[Prod.fst <$>
        ($ᵗ (HiddenRootCoordinate × List.Vector UInt8 44))] := by
      rw [evalDist_map, evalDist_ext fun pair =>
        probOutput_map_bijective_uniform_cross
          (α := JointKdfStream)
          (β := HiddenRootCoordinate × List.Vector UInt8 44)
          jointKdfStreamSplitEquiv
          jointKdfStreamSplitEquiv.bijective pair, ← evalDist_map]
    _ = 𝒟[$ᵗ HiddenRootCoordinate] :=
      evalDist_map_fst_uniformSample_prod

/-! ## Full-stream programming at the hidden address -/

/-- Program the complete 76-byte stream at exactly one canonical address. -/
def jointKdfSingletonProgrammingPolicy (target : JointKdfAddress)
    (stream : JointKdfStream) : JointKdfRO.ProgrammingPolicy :=
  fun address =>
    if address = target then some stream else none

/-- Hidden-root specialization of complete-stream singleton programming. -/
def hiddenRootProgrammingPolicy (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream) :
    JointKdfRO.ProgrammingPolicy :=
  jointKdfSingletonProgrammingPolicy (hiddenRootAddress known hidden) stream

@[simp] theorem hiddenRootProgrammingPolicy_target
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) :
    hiddenRootProgrammingPolicy known hidden stream
        (hiddenRootAddress known hidden) = some stream := by
  unfold hiddenRootProgrammingPolicy jointKdfSingletonProgrammingPolicy
  rw [if_pos rfl]

theorem hiddenRootProgrammingPolicy_other
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) (address : JointKdfAddress)
    (hne : address ≠ hiddenRootAddress known hidden) :
    hiddenRootProgrammingPolicy known hidden stream address = none := by
  unfold hiddenRootProgrammingPolicy jointKdfSingletonProgrammingPolicy
  rw [if_neg hne]

/-- Primitive handler transparent on adversary randomness and programmed at one complete stream. -/
noncomputable def jointKdfSingletonProgrammedStreamImpl
    (target : JointKdfAddress) (stream : JointKdfStream) :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) +
    QueryImpl.withProgramming uniformSampleImpl
      (jointKdfSingletonProgrammingPolicy target stream)

/-- Hidden-root specialization of the singleton-programmed primitive handler. -/
noncomputable def hiddenRootProgrammedStreamImpl
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  jointKdfSingletonProgrammedStreamImpl (hiddenRootAddress known hidden) stream

/-- Primitive lazy-stream handler that tracks whether the singleton policy address is queried. -/
noncomputable def jointKdfSingletonTrackingStreamImpl
    (target : JointKdfAddress) (stream : JointKdfStream) :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) +
    QueryImpl.withCachingTrackingPolicy uniformSampleImpl
      (jointKdfSingletonProgrammingPolicy target stream)

/-- Hidden-root specialization of the policy-tracking primitive handler. -/
noncomputable def hiddenRootTrackingStreamImpl
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) :
    QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  jointKdfSingletonTrackingStreamImpl (hiddenRootAddress known hidden) stream

/-- Source-view handler whose projections share the singleton-programmed complete stream. -/
noncomputable def hiddenRootProgrammedViewImpl
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) :
    QueryImpl JointKdfViewAdversarySpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  hiddenRootProgrammedStreamImpl known hidden stream ∘ₛ jointKdfViewForwardImpl

/-- Source-view handler backed by a lazy stream cache while tracking the same policy. -/
noncomputable def hiddenRootTrackingViewImpl
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (stream : JointKdfStream) :
    QueryImpl JointKdfViewAdversarySpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp) :=
  hiddenRootTrackingStreamImpl known hidden stream ∘ₛ jointKdfViewForwardImpl

/-- Project a programmed cache into the corresponding cache prefilled at the target address. -/
def hiddenRootPrefillProjection (target : JointKdfAddress) (stream : JointKdfStream)
    (state : JointKdfRO.QueryCache × Bool) : JointKdfRO.QueryCache :=
  state.1.cacheQuery target stream

/-- A programmed cache never associates the target with a stream other than the challenge. -/
def HiddenRootProgrammedCacheInvariant (target : JointKdfAddress)
    (stream : JointKdfStream) (state : JointKdfRO.QueryCache × Bool) : Prop :=
  ∀ cached, state.1 target = some cached → cached = stream

theorem jointKdfCache_cacheQuery_comm (cache : JointKdfRO.QueryCache)
    (left right : JointKdfAddress) (leftStream rightStream : JointKdfStream)
    (hne : left ≠ right) :
    (cache.cacheQuery left leftStream).cacheQuery right rightStream =
      (cache.cacheQuery right rightStream).cacheQuery left leftStream := by
  unfold QueryCache.cacheQuery
  exact Function.update_comm hne _ _ _

theorem jointKdfCache_cacheQuery_idem (cache : JointKdfRO.QueryCache)
    (address : JointKdfAddress) (stream : JointKdfStream) :
    (cache.cacheQuery address stream).cacheQuery address stream =
      cache.cacheQuery address stream := by
  unfold QueryCache.cacheQuery
  exact Function.update_idem _ _ _

theorem jointKdfSingletonProgrammedStream_project_step
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (state : JointKdfRO.QueryCache × Bool)
    (hinvariant : HiddenRootProgrammedCacheInvariant target stream state) :
    Prod.map id (hiddenRootPrefillProjection target stream) <$>
      (jointKdfSingletonProgrammedStreamImpl target stream query).run state =
    (fixedHkdfSha512JointStreamRandomImpl query).run
      (hiddenRootPrefillProjection target stream state) := by
  rcases state with ⟨cache, bad⟩
  rcases query with randomQuery | address
  · simp [jointKdfSingletonProgrammedStreamImpl,
      fixedHkdfSha512JointStreamRandomImpl, hiddenRootPrefillProjection,
      QueryImpl.liftTarget_apply, OracleComp.liftM_run_StateT]
  · by_cases htarget : address = target
    · subst address
      cases hcache : cache target with
      | none =>
          simp [jointKdfSingletonProgrammedStreamImpl,
            fixedHkdfSha512JointStreamRandomImpl, hiddenRootPrefillProjection,
            QueryImpl.withProgramming_apply, hcache,
            jointKdfSingletonProgrammingPolicy]
          rw [jointKdfLazyRandomStreamImpl_run_hit target
            (cache.cacheQuery target stream) stream
              (QueryCache.cacheQuery_self cache target stream)]
          simp [jointKdfCache_cacheQuery_idem]
      | some cached =>
          have hcached : cached = stream := hinvariant cached hcache
          subst cached
          simp [jointKdfSingletonProgrammedStreamImpl,
            fixedHkdfSha512JointStreamRandomImpl, hiddenRootPrefillProjection,
            QueryImpl.withProgramming_apply, hcache]
          rw [jointKdfLazyRandomStreamImpl_run_hit target
            (cache.cacheQuery target stream) stream
              (QueryCache.cacheQuery_self cache target stream)]
    · cases hcache : cache address with
      | none =>
          have hprefill :
              (cache.cacheQuery target stream) address = none := by
            simpa [QueryCache.cacheQuery_of_ne cache stream htarget] using hcache
          simp [jointKdfSingletonProgrammedStreamImpl,
            fixedHkdfSha512JointStreamRandomImpl, hiddenRootPrefillProjection,
            QueryImpl.withProgramming_apply, hcache, hprefill,
            jointKdfSingletonProgrammingPolicy, htarget,
            jointKdfCache_cacheQuery_comm cache address target]
          rw [jointKdfLazyRandomStreamImpl_run_miss address
            (cache.cacheQuery target stream) hprefill]
          rfl
      | some cached =>
          have hprefill :
              (cache.cacheQuery target stream) address = some cached := by
            simpa [QueryCache.cacheQuery_of_ne cache stream htarget] using hcache
          simp [jointKdfSingletonProgrammedStreamImpl,
            fixedHkdfSha512JointStreamRandomImpl, hiddenRootPrefillProjection,
            QueryImpl.withProgramming_apply, hcache, hprefill,
            jointKdfSingletonProgrammingPolicy, htarget]
          rw [jointKdfLazyRandomStreamImpl_run_hit address
            (cache.cacheQuery target stream) cached hprefill]

theorem hiddenRootProgrammedCacheInvariant_cache_target
    (cache : JointKdfRO.QueryCache) (bad : Bool)
    (target : JointKdfAddress) (stream : JointKdfStream) :
    HiddenRootProgrammedCacheInvariant target stream
      (cache.cacheQuery target stream, bad) := by
  intro cached hcached
  exact (Option.some.inj
    ((QueryCache.cacheQuery_self cache target stream).symm.trans hcached)).symm

theorem hiddenRootProgrammedCacheInvariant_cache_other
    (cache : JointKdfRO.QueryCache) (bad : Bool)
    (target address : JointKdfAddress) (stream answer : JointKdfStream)
    (hinvariant : HiddenRootProgrammedCacheInvariant target stream (cache, bad))
    (hne : address ≠ target) :
    HiddenRootProgrammedCacheInvariant target stream
      (cache.cacheQuery address answer, bad) := by
  intro cached hcached
  change (cache.cacheQuery address answer) target = some cached at hcached
  rw [QueryCache.cacheQuery_of_ne cache answer hne.symm] at hcached
  exact hinvariant cached hcached

theorem jointKdfSingletonProgrammedStream_preserves_invariant
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (state : JointKdfRO.QueryCache × Bool)
    (hinvariant : HiddenRootProgrammedCacheInvariant target stream state) :
    ∀ result ∈ support
        ((jointKdfSingletonProgrammedStreamImpl target stream query).run state),
      HiddenRootProgrammedCacheInvariant target stream result.2 := by
  rcases state with ⟨cache, bad⟩
  rcases query with randomQuery | address
  · intro result hresult
    simp [jointKdfSingletonProgrammedStreamImpl,
      QueryImpl.liftTarget_apply, OracleComp.liftM_run_StateT,
      mem_support_bind_iff] at hresult
    obtain ⟨sample, _, rfl⟩ := hresult
    exact hinvariant
  · by_cases htarget : address = target
    · subst address
      cases hcache : cache target with
      | none =>
          intro result hresult
          simp [jointKdfSingletonProgrammedStreamImpl,
            QueryImpl.withProgramming_apply, hcache,
            jointKdfSingletonProgrammingPolicy] at hresult
          subst result
          exact hiddenRootProgrammedCacheInvariant_cache_target
            cache true target stream
      | some cached =>
          intro result hresult
          simp [jointKdfSingletonProgrammedStreamImpl,
            QueryImpl.withProgramming_apply, hcache] at hresult
          subst result
          exact hinvariant
    · cases hcache : cache address with
      | none =>
          intro result hresult
          simp [jointKdfSingletonProgrammedStreamImpl,
            QueryImpl.withProgramming_apply, hcache,
            jointKdfSingletonProgrammingPolicy, htarget,
            support_map] at hresult
          obtain ⟨sample, _, rfl⟩ := hresult
          exact hiddenRootProgrammedCacheInvariant_cache_other
            cache bad target address stream sample hinvariant htarget
      | some cached =>
          intro result hresult
          simp [jointKdfSingletonProgrammedStreamImpl,
            QueryImpl.withProgramming_apply, hcache] at hresult
          subst result
          exact hinvariant

/-- The singleton-programmed cache is a state ornament of the lazy cache prefilled at its target. -/
noncomputable def jointKdfSingletonProgrammedStreamOrnament
    (target : JointKdfAddress) (stream : JointKdfStream) :
    QueryImpl.StateOrnament
      (jointKdfSingletonProgrammedStreamImpl target stream)
      fixedHkdfSha512JointStreamRandomImpl where
  inv := HiddenRootProgrammedCacheInvariant target stream
  proj := hiddenRootPrefillProjection target stream
  preserves_inv := jointKdfSingletonProgrammedStream_preserves_invariant target stream
  project_step := jointKdfSingletonProgrammedStream_project_step target stream

/-- Empty singleton programming has exactly the output distribution of a lazy cache prefilled
with the same complete 76-byte stream. -/
theorem jointKdfSingletonProgrammedStream_run'_eq_prefilled
    {alpha : Type} (target : JointKdfAddress) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha) :
    (simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
      computation).run' (∅, false) =
    (simulateQ fixedHkdfSha512JointStreamRandomImpl computation).run'
      ((∅ : JointKdfRO.QueryCache).cacheQuery target stream) := by
  have hempty : HiddenRootProgrammedCacheInvariant target stream
      ((∅ : JointKdfRO.QueryCache), false) := by
    intro cached hcached
    change (none : Option JointKdfStream) = some cached at hcached
    contradiction
  simpa [jointKdfSingletonProgrammedStreamOrnament,
    hiddenRootPrefillProjection, HiddenRootProgrammedCacheInvariant] using
    (jointKdfSingletonProgrammedStreamOrnament target stream).run'_eq
      computation (∅, false) hempty

/-- On the public projection surface, singleton programming is exactly lazy reuse of a prefilled
complete-stream cache. -/
theorem hiddenRootProgrammedView_run'_eq_prefilled
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream)
    (computation : OracleComp JointKdfViewAdversarySpec alpha) :
    (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
      computation).run' (∅, false) =
    (simulateQ jointKdfViewRandomImpl computation).run'
      ((∅ : JointKdfRO.QueryCache).cacheQuery
        (hiddenRootAddress known hidden) stream) := by
  simpa [hiddenRootProgrammedViewImpl, hiddenRootProgrammedStreamImpl,
    jointKdfViewRandomImpl, QueryImpl.simulateQ_compose] using
    jointKdfSingletonProgrammedStream_run'_eq_prefilled
      (hiddenRootAddress known hidden) stream
      (simulateQ jointKdfViewForwardImpl computation)

/-- Shared-ROM experiment represented by a sampled complete stream and singleton programming. -/
noncomputable def hiddenRootProgrammedGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool := do
  let hidden ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))).run' (∅, false)

/-- The Stage-2 shared random-stream game is exactly the singleton-programmed source game. -/
theorem hiddenRootSharedRandomGame_eq_programmedGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    hiddenRootSharedRandomGame adversary known publicContext =
      hiddenRootProgrammedGame adversary known publicContext := by
  simp [hiddenRootSharedRandomGame, hiddenRootProgrammedGame,
    hiddenRootReductionMain, queryHiddenRootStream,
    fixedHkdfSha512JointStreamRandomImpl,
    QueryImpl.simulateQ_add_liftM_left,
    jointKdfLazyRandomStreamImpl_run_miss,
    hiddenRootProgrammedView_run'_eq_prefilled]
  apply bind_congr
  intro hidden
  apply bind_congr
  intro stream
  change Prod.fst <$>
      (simulateQ fixedHkdfSha512JointStreamRandomImpl
        (simulateQ jointKdfViewForwardImpl
          (adversary.main known publicContext
            (JointKdfProjection.first32.project stream)))).run
        ((∅ : JointKdfRO.QueryCache).cacheQuery
          (hiddenRootAddress known hidden) stream) =
    Prod.fst <$>
      (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
        (adversary.main known publicContext
          (JointKdfProjection.first32.project stream))).run (∅, false)
  rw [← QueryImpl.simulateQ_compose]
  change
    (simulateQ jointKdfViewRandomImpl
      (adversary.main known publicContext
        (JointKdfProjection.first32.project stream))).run'
          ((∅ : JointKdfRO.QueryCache).cacheQuery
            (hiddenRootAddress known hidden) stream) =
      (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
        (adversary.main known publicContext
          (JointKdfProjection.first32.project stream))).run' (∅, false)
  exact (hiddenRootProgrammedView_run'_eq_prefilled known hidden stream
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))).symm

/-! ## Identical-until-bad coupling to an unprogrammed lazy stream -/

/-- Programming and policy tracking have identical non-bad one-step transitions. -/
theorem jointKdfSingletonProgrammed_tracking_agree_good
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (cache : JointKdfRO.QueryCache)
    (response : FixedHkdfSha512JointStreamSpec.Range query)
    (nextCache : JointKdfRO.QueryCache) :
    Pr[= (response, (nextCache, false)) |
      (jointKdfSingletonProgrammedStreamImpl target stream query).run
        (cache, false)] =
    Pr[= (response, (nextCache, false)) |
      (jointKdfSingletonTrackingStreamImpl target stream query).run
        (cache, false)] := by
  rcases query with randomQuery | address
  · simp [jointKdfSingletonProgrammedStreamImpl,
      jointKdfSingletonTrackingStreamImpl, QueryImpl.liftTarget_apply]
  · cases hcache : cache address with
    | some cached =>
        simp [jointKdfSingletonProgrammedStreamImpl,
          jointKdfSingletonTrackingStreamImpl,
          QueryImpl.withProgramming_apply,
          QueryImpl.withCachingTrackingPolicy_apply, hcache]
    | none =>
        cases hpolicy : jointKdfSingletonProgrammingPolicy target stream address with
        | none =>
            simp [jointKdfSingletonProgrammedStreamImpl,
              jointKdfSingletonTrackingStreamImpl,
              QueryImpl.withProgramming_apply,
              QueryImpl.withCachingTrackingPolicy_apply, hcache, hpolicy]
        | some programmed =>
            simp [jointKdfSingletonProgrammedStreamImpl,
              jointKdfSingletonTrackingStreamImpl,
              QueryImpl.withProgramming_apply,
              QueryImpl.withCachingTrackingPolicy_apply, hcache, hpolicy]
            have hleft : (response, nextCache, false) ∉
                support (pure
                  (programmed, cache.cacheQuery address programmed, true) :
                    ProbComp (JointKdfStream × JointKdfRO.QueryCache × Bool)) := by
              simp
            have hright : (response, nextCache, false) ∉ support
                ((fun sample : JointKdfStream =>
                  (sample, cache.cacheQuery address sample, true)) <$>
                    uniformSampleImpl (spec := JointKdfRO) address) := by
              intro hright
              rw [support_map] at hright
              obtain ⟨sample, _, hresult⟩ := hright
              have hflag := congrArg (fun result => result.2.2) hresult
              simp at hflag
            exact (probOutput_eq_zero_of_not_mem_support hleft).trans
              (probOutput_eq_zero_of_not_mem_support hright).symm

/-- Once set, the singleton-programming bad flag remains set. -/
theorem jointKdfSingletonProgrammedStream_bad_monotone
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (state : JointKdfRO.QueryCache × Bool) (hbad : state.2 = true)
    (result : FixedHkdfSha512JointStreamSpec.Range query ×
      (JointKdfRO.QueryCache × Bool))
    (hresult : result ∈ support
      ((jointKdfSingletonProgrammedStreamImpl target stream query).run state)) :
    result.2.2 = true := by
  rcases state with ⟨cache, bad⟩
  change bad = true at hbad
  subst bad
  rcases query with randomQuery | address
  · simp [jointKdfSingletonProgrammedStreamImpl,
      QueryImpl.liftTarget_apply, support_map] at hresult
    obtain ⟨sample, _, rfl⟩ := hresult
    rfl
  · exact QueryImpl.withProgramming_bad_monotone
      uniformSampleImpl (jointKdfSingletonProgrammingPolicy target stream)
      address cache result hresult

/-- Once set, the policy-tracking bad flag remains set. -/
theorem jointKdfSingletonTrackingStream_bad_monotone
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (state : JointKdfRO.QueryCache × Bool) (hbad : state.2 = true)
    (result : FixedHkdfSha512JointStreamSpec.Range query ×
      (JointKdfRO.QueryCache × Bool))
    (hresult : result ∈ support
      ((jointKdfSingletonTrackingStreamImpl target stream query).run state)) :
    result.2.2 = true := by
  rcases state with ⟨cache, bad⟩
  change bad = true at hbad
  subst bad
  rcases query with randomQuery | address
  · simp [jointKdfSingletonTrackingStreamImpl,
      QueryImpl.liftTarget_apply, support_map] at hresult
    obtain ⟨sample, _, rfl⟩ := hresult
    rfl
  · exact QueryImpl.withCachingTrackingPolicy_bad_monotone
      uniformSampleImpl (jointKdfSingletonProgrammingPolicy target stream)
      address cache result hresult

/-- For a fixed target and challenge stream, programming and tracking differ by at most the one
sticky policy-hit event. -/
theorem jointKdfSingletonProgrammed_tracking_tvDist_le_bad
    {alpha : Type} (target : JointKdfAddress) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha) :
    tvDist
      ((simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
        computation).run' (∅, false))
      ((simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
        computation).run' (∅, false)) ≤
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
        computation).run (∅, false)].toReal := by
  refine (tvDist_map_le Prod.fst
    ((simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
      computation).run (∅, false))
    ((simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
      computation).run (∅, false))).trans ?_
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (jointKdfSingletonProgrammedStreamImpl target stream)
    (jointKdfSingletonTrackingStreamImpl target stream)
    computation ∅
    (jointKdfSingletonProgrammed_tracking_agree_good target stream)
    (jointKdfSingletonProgrammedStream_bad_monotone target stream)
    (jointKdfSingletonTrackingStream_bad_monotone target stream)

/-- Public projection version of the fixed-target identical-until-bad bound. -/
theorem hiddenRootProgrammed_tracking_tvDist_le_bad
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream)
    (computation : OracleComp JointKdfViewAdversarySpec alpha) :
    tvDist
      ((simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
        computation).run' (∅, false))
      ((simulateQ (hiddenRootTrackingViewImpl known hidden stream)
        computation).run' (∅, false)) ≤
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
        computation).run (∅, false)].toReal := by
  simpa [hiddenRootProgrammedViewImpl, hiddenRootTrackingViewImpl,
    hiddenRootProgrammedStreamImpl, hiddenRootTrackingStreamImpl,
    QueryImpl.simulateQ_compose] using
    jointKdfSingletonProgrammed_tracking_tvDist_le_bad
      (hiddenRootAddress known hidden) stream
      (simulateQ jointKdfViewForwardImpl computation)

/-- Forgetting the sticky policy flag turns the primitive tracking handler back into the
ordinary lazy joint-stream handler. -/
theorem jointKdfSingletonTrackingStream_project_step
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (state : JointKdfRO.QueryCache × Bool) :
    Prod.map id Prod.fst <$>
      (jointKdfSingletonTrackingStreamImpl target stream query).run state =
    (fixedHkdfSha512JointStreamRandomImpl query).run state.1 := by
  rcases state with ⟨cache, bad⟩
  rcases query with randomQuery | address
  · simp [jointKdfSingletonTrackingStreamImpl,
      fixedHkdfSha512JointStreamRandomImpl, QueryImpl.liftTarget_apply,
      OracleComp.liftM_run_StateT]
  · cases hcache : cache address with
    | none =>
        simp [jointKdfSingletonTrackingStreamImpl,
          fixedHkdfSha512JointStreamRandomImpl,
          jointKdfLazyRandomStreamImpl, OracleSpec.randomOracle,
          QueryImpl.withCachingTrackingPolicy_apply,
          QueryImpl.withCaching_apply, hcache]
    | some cached =>
        simp [jointKdfSingletonTrackingStreamImpl,
          fixedHkdfSha512JointStreamRandomImpl,
          jointKdfLazyRandomStreamImpl, OracleSpec.randomOracle,
          QueryImpl.withCachingTrackingPolicy_apply,
          QueryImpl.withCaching_apply, hcache]

/-- The policy flag is a pure state ornament of the primitive lazy-stream cache. -/
noncomputable def jointKdfSingletonTrackingStreamOrnament
    (target : JointKdfAddress) (stream : JointKdfStream) :
    QueryImpl.StateOrnament
      (jointKdfSingletonTrackingStreamImpl target stream)
      fixedHkdfSha512JointStreamRandomImpl where
  inv := fun _ => True
  proj := Prod.fst
  preserves_inv := by simp
  project_step := fun query state _ =>
    jointKdfSingletonTrackingStream_project_step target stream query state

/-- Output projection of policy tracking is exactly the ordinary lazy complete-stream game. -/
theorem jointKdfSingletonTrackingStream_run'_eq_random
    {alpha : Type} (target : JointKdfAddress) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha)
    (cache : JointKdfRO.QueryCache) (bad : Bool) :
    (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
      computation).run' (cache, bad) =
    (simulateQ fixedHkdfSha512JointStreamRandomImpl computation).run' cache := by
  exact (jointKdfSingletonTrackingStreamOrnament target stream).run'_eq
    computation (cache, bad) trivial

/-- Output projection of policy tracking on the public component surface is exactly the
ordinary lazy projection handler. -/
theorem hiddenRootTrackingView_run'_eq_random
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream)
    (computation : OracleComp JointKdfViewAdversarySpec alpha)
    (cache : JointKdfRO.QueryCache) (bad : Bool) :
    (simulateQ (hiddenRootTrackingViewImpl known hidden stream)
      computation).run' (cache, bad) =
    (simulateQ jointKdfViewRandomImpl computation).run' cache := by
  simpa [hiddenRootTrackingViewImpl, hiddenRootTrackingStreamImpl,
    jointKdfViewRandomImpl, QueryImpl.simulateQ_compose] using
    jointKdfSingletonTrackingStream_run'_eq_random
      (hiddenRootAddress known hidden) stream
      (simulateQ jointKdfViewForwardImpl computation) cache bad

/-- Starting from a clear flag, one primitive tracking step can set it only on the exact
singleton target request. -/
theorem jointKdfSingletonTrackingStream_new_bad_implies_target
    (target : JointKdfAddress) (stream : JointKdfStream)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (cache : JointKdfRO.QueryCache)
    (result : FixedHkdfSha512JointStreamSpec.Range query ×
      (JointKdfRO.QueryCache × Bool))
    (hresult : result ∈ support
      ((jointKdfSingletonTrackingStreamImpl target stream query).run
        (cache, false)))
    (hbad : result.2.2 = true) :
    query = .inr target := by
  rcases query with randomQuery | address
  · simp [jointKdfSingletonTrackingStreamImpl,
      QueryImpl.liftTarget_apply, support_map] at hresult
    obtain ⟨sample, _, rfl⟩ := hresult
    contradiction
  · cases hcache : cache address with
    | some cached =>
        simp [jointKdfSingletonTrackingStreamImpl,
          QueryImpl.withCachingTrackingPolicy_apply, hcache] at hresult
        subst result
        contradiction
    | none =>
        by_cases htarget : address = target
        · exact congrArg Sum.inr htarget
        · simp [jointKdfSingletonTrackingStreamImpl,
            QueryImpl.withCachingTrackingPolicy_apply, hcache,
            jointKdfSingletonProgrammingPolicy, htarget,
            support_map] at hresult
          obtain ⟨sample, _, rfl⟩ := hresult
          contradiction

/-! ## Root-only logical query trace -/

/-- Parse one hidden-coordinate candidate from an exact primitive root-domain request.  Uniform
and symmetric-domain requests contribute no candidate. -/
def hiddenRootStreamQueryCandidate? (known : KnownPqxdhRootCoordinates) :
    FixedHkdfSha512JointStreamSpec.Domain → Option HiddenRootCoordinate
  | .inl _ => none
  | .inr address =>
      if address.info = Pqxdh.INFO_PQ then
        parseHiddenRootCoordinate? known address.input
      else
        none

/-- Primitive candidate parsing succeeds exactly on the canonical hidden-root address. -/
theorem hiddenRootStreamQueryCandidate?_eq_some_iff
    (known : KnownPqxdhRootCoordinates)
    (query : FixedHkdfSha512JointStreamSpec.Domain)
    (hidden : HiddenRootCoordinate) :
    hiddenRootStreamQueryCandidate? known query = some hidden ↔
      query = .inr (hiddenRootAddress known hidden) := by
  rcases query with randomQuery | address
  · simp [hiddenRootStreamQueryCandidate?]
  · rcases address with ⟨info, input⟩
    by_cases hroot : info = Pqxdh.INFO_PQ
    · subst info
      simp [hiddenRootStreamQueryCandidate?, hiddenRootAddress,
        FixedHkdfDomain.address,
        parseHiddenRootCoordinate?_eq_some_iff]
    · simp [hiddenRootStreamQueryCandidate?, hroot, hiddenRootAddress,
        FixedHkdfDomain.address]

/-- Candidate slots extracted only from root-domain primitive requests in a logical query log. -/
def hiddenRootStreamCandidates (known : KnownPqxdhRootCoordinates) :
    QueryLog FixedHkdfSha512JointStreamSpec →
      List (Option HiddenRootCoordinate)
  | [] => []
  | ⟨query, _response⟩ :: tail =>
      if IsFixedHkdfRootStreamQuery query then
        hiddenRootStreamQueryCandidate? known query ::
          hiddenRootStreamCandidates known tail
      else
        hiddenRootStreamCandidates known tail

@[simp] theorem hiddenRootStreamCandidates_length
    (known : KnownPqxdhRootCoordinates)
    (log : QueryLog FixedHkdfSha512JointStreamSpec) :
    (hiddenRootStreamCandidates known log).length =
      (log.getQ IsFixedHkdfRootStreamQuery).length := by
  induction log with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨query, response⟩
      by_cases hroot : IsFixedHkdfRootStreamQuery query <;>
        simp [hiddenRootStreamCandidates, QueryLog.getQ_cons, hroot, ih]

/-- A predicate query bound controls the matching portion of every logical query trace. -/
theorem getQ_length_le_of_mem_support_withQueryLog
    {index : Type} {spec : OracleSpec index} [spec.DecidableEq]
    [IsUniformSpec spec] {alpha : Type}
    (predicate : spec.Domain → Prop) [DecidablePred predicate]
    {computation : OracleComp spec alpha} {bound : ℕ}
    (hbound : computation.IsQueryBoundP predicate bound)
    {result : alpha × QueryLog spec}
    (hresult : result ∈ support computation.withQueryLog) :
    (result.2.getQ predicate).length ≤ bound := by
  induction computation using OracleComp.inductionOn generalizing bound result with
  | pure output =>
      simp only [OracleComp.withQueryLog_pure, mem_support_pure_iff] at hresult
      subst result
      simp
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [show (liftM (spec.query query) >>= rest).withQueryLog =
          (simulateQ spec.loggingOracle
            (liftM (spec.query query) >>= rest)).run from rfl,
        OracleComp.run_simulateQ_loggingOracle_query_bind,
        support_bind] at hresult
      simp only [Set.mem_iUnion, support_map] at hresult
      obtain ⟨response, _, tail, htail, rfl⟩ := hresult
      by_cases hquery : predicate query
      · have htailLength := ih response (hbound.2 response) htail
        simp only [hquery, if_true] at htailLength
        simp only [QueryLog.getQ_cons, hquery, if_true, List.length_cons]
        have hpositive : 0 < bound := by
          rcases hbound.1 with hnot | hpos
          · exact (hnot hquery).elim
          · exact hpos
        omega
      · have htailLength := ih response (hbound.2 response) htail
        simpa [QueryLog.getQ_cons, hquery] using htailLength

/-- The extracted candidate trace has at most one slot per adversary root-domain request. -/
theorem hiddenRootStreamCandidates_length_le
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    {computation : OracleComp FixedHkdfSha512JointStreamSpec alpha}
    {qRoot : ℕ}
    (hbound : computation.IsQueryBoundP IsFixedHkdfRootStreamQuery qRoot)
    {result : alpha × QueryLog FixedHkdfSha512JointStreamSpec}
    (hresult : result ∈ support computation.withQueryLog) :
    (hiddenRootStreamCandidates known result.2).length ≤ qRoot := by
  rw [hiddenRootStreamCandidates_length]
  exact getQ_length_le_of_mem_support_withQueryLog
    IsFixedHkdfRootStreamQuery hbound hresult

/-- The same exact logical-query bound holds after interpreting the logged computation through
an arbitrary stateful handler; it counts computation requests, not handler cache misses. -/
theorem hiddenRootStreamCandidates_length_le_simulate
    {alpha state : Type} (known : KnownPqxdhRootCoordinates)
    (impl : QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT state ProbComp))
    {computation : OracleComp FixedHkdfSha512JointStreamSpec alpha}
    {qRoot : ℕ}
    (hbound : computation.IsQueryBoundP IsFixedHkdfRootStreamQuery qRoot)
    (initialState : state)
    {result : (alpha × QueryLog FixedHkdfSha512JointStreamSpec) × state}
    (hresult : result ∈ support
      ((simulateQ impl computation.withQueryLog).run initialState)) :
    (hiddenRootStreamCandidates known result.1.2).length ≤ qRoot := by
  induction computation using OracleComp.inductionOn generalizing qRoot initialState result with
  | pure output =>
      simp only [OracleComp.withQueryLog_pure, simulateQ_pure,
        StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      simp [hiddenRootStreamCandidates]
  | query_bind query rest ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [show (liftM (FixedHkdfSha512JointStreamSpec.query query) >>= rest).withQueryLog =
          (simulateQ FixedHkdfSha512JointStreamSpec.loggingOracle
            (liftM (FixedHkdfSha512JointStreamSpec.query query) >>= rest)).run from rfl,
        OracleComp.run_simulateQ_loggingOracle_query_bind,
        simulateQ_bind, StateT.run_bind, support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨head, _hhead, htail⟩ := hresult
      rcases head with ⟨response, nextState⟩
      simp only [simulateQ_map, StateT.run_map, support_map,
        Set.mem_image] at htail
      obtain ⟨tailResult, htail, rfl⟩ := htail
      have htailLength := ih response (hbound.2 response) nextState htail
      by_cases hquery : IsFixedHkdfRootStreamQuery query
      · simp only [hquery, if_true] at htailLength
        simp only [hiddenRootStreamCandidates, hquery, if_true, List.length_cons]
        have hpositive : 0 < qRoot := by
          rcases hbound.1 with hnot | hpos
          · exact (hnot hquery).elim
          · exact hpos
        omega
      · simpa [hiddenRootStreamCandidates, hquery] using htailLength

/-- In the unprogrammed tracking run, a newly raised flag witnesses an exact target request in
the response-dependent logical query trace. -/
theorem jointKdfSingletonTracking_bad_implies_target_in_log
    {alpha : Type} (target : JointKdfAddress) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha)
    (cache : JointKdfRO.QueryCache) (initialBad : Bool)
    (result : (alpha × QueryLog FixedHkdfSha512JointStreamSpec) ×
      (JointKdfRO.QueryCache × Bool))
    (hresult : result ∈ support
      ((simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
        computation.withQueryLog).run (cache, initialBad)))
    (hbad : result.2.2 = true) :
    initialBad = true ∨
      (.inr target : FixedHkdfSha512JointStreamSpec.Domain) ∈
        result.1.2.map (fun entry => entry.1) := by
  induction computation using OracleComp.inductionOn generalizing cache initialBad result with
  | pure output =>
      simp only [OracleComp.withQueryLog_pure, simulateQ_pure,
        StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      exact Or.inl hbad
  | query_bind query rest ih =>
      rw [show (liftM (FixedHkdfSha512JointStreamSpec.query query) >>= rest).withQueryLog =
          (simulateQ FixedHkdfSha512JointStreamSpec.loggingOracle
            (liftM (FixedHkdfSha512JointStreamSpec.query query) >>= rest)).run from rfl,
        OracleComp.run_simulateQ_loggingOracle_query_bind,
        simulateQ_bind, StateT.run_bind, support_bind] at hresult
      simp only [Set.mem_iUnion] at hresult
      obtain ⟨head, hhead, htail⟩ := hresult
      rcases head with ⟨response, nextCache, nextBad⟩
      simp only [simulateQ_map, StateT.run_map, support_map,
        Set.mem_image] at htail
      obtain ⟨tailResult, htail, rfl⟩ := htail
      have htail' := ih response nextCache nextBad tailResult htail hbad
      rcases htail' with hwasBad | htargetTail
      · by_cases hwasInitiallyBad : initialBad = true
        · exact Or.inl hwasInitiallyBad
        · have hinitialFalse : initialBad = false := by
            cases initialBad <;> simp_all
          subst initialBad
          have hhead' : (response, (nextCache, nextBad)) ∈ support
              ((jointKdfSingletonTrackingStreamImpl target stream query).run
                (cache, false)) := by
            simpa using hhead
          have hqueryTarget :=
            jointKdfSingletonTrackingStream_new_bad_implies_target
              target stream query cache
                (response, (nextCache, nextBad)) hhead' hwasBad
          right
          subst query
          simp
      · right
        simp only [List.map_cons, List.mem_cons]
        exact Or.inr htargetTail

/-- The exact target appears in a primitive logical trace iff its extracted root-candidate list
contains the corresponding hidden coordinate. -/
theorem hiddenRootTarget_in_log_iff_candidate_mem
    (known : KnownPqxdhRootCoordinates) (hidden : HiddenRootCoordinate)
    (log : QueryLog FixedHkdfSha512JointStreamSpec) :
    (.inr (hiddenRootAddress known hidden) :
        FixedHkdfSha512JointStreamSpec.Domain) ∈
        log.map (fun entry => entry.1) ↔
      some hidden ∈ hiddenRootStreamCandidates known log := by
  induction log with
  | nil => simp [hiddenRootStreamCandidates]
  | cons entry tail ih =>
      rcases entry with ⟨query, response⟩
      by_cases hroot : IsFixedHkdfRootStreamQuery query
      · simp only [List.map_cons, List.mem_cons,
          hiddenRootStreamCandidates, hroot, if_true]
        constructor
        · intro hmem
          rcases hmem with hhead | htail
          · left
            exact ((hiddenRootStreamQueryCandidate?_eq_some_iff
              known query hidden).mpr hhead.symm).symm
          · exact Or.inr (ih.mp htail)
        · intro hmem
          rcases hmem with hhead | htail
          · left
            exact ((hiddenRootStreamQueryCandidate?_eq_some_iff
              known query hidden).mp hhead.symm).symm
          · exact Or.inr (ih.mpr htail)
      · have hne : query ≠
            (.inr (hiddenRootAddress known hidden) :
              FixedHkdfSha512JointStreamSpec.Domain) := by
          intro heq
          subst query
          apply hroot
          simp [IsFixedHkdfRootStreamQuery, hiddenRootAddress,
            FixedHkdfDomain.address]
        simp only [List.map_cons, List.mem_cons,
          hiddenRootStreamCandidates, hroot, if_false]
        rw [or_iff_right hne.symm]
        exact ih

/-- Adding a logical query log and then forgetting it preserves an arbitrary stateful primitive
simulation exactly. -/
theorem jointKdfSimulate_withQueryLog_run_project
    {alpha state : Type}
    (impl : QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT state ProbComp))
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha)
    (initialState : state) :
    Prod.map Prod.fst id <$>
        (simulateQ impl computation.withQueryLog).run initialState =
      (simulateQ impl computation).run initialState := by
  have hhandler :
      impl.writerTMapBase FixedHkdfSha512JointStreamSpec.loggingOracle =
        impl.withLogging := by
    funext query
    apply WriterT.ext
    simp [QueryImpl.writerTMapBase, OracleSpec.loggingOracle]
  have hbase := QueryImpl.simulateQ_writerTMapBase_run
    impl FixedHkdfSha512JointStreamSpec.loggingOracle computation
  rw [hhandler] at hbase
  have hproject := QueryImpl.fst_map_run_withLogging impl computation
  have hrun := congrArg (fun stateful => stateful.run initialState) hproject
  rw [← hrun]
  have houter := congrArg (fun stateful =>
    Prod.map Prod.fst id <$> stateful.run initialState) hbase
  change Prod.map Prod.fst id <$>
      (simulateQ impl
        (simulateQ FixedHkdfSha512JointStreamSpec.loggingOracle
          computation).run).run initialState =
    Prod.map Prod.fst id <$>
      (simulateQ impl.withLogging computation).run.run initialState
  exact houter

/-- The primitive computation obtained by one-for-one forwarding of the adversary's public
projection requests. -/
def hiddenRootForwardedAdversary
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (root : HiddenRootCoordinate) :
    OracleComp FixedHkdfSha512JointStreamSpec Bool :=
  simulateQ jointKdfViewForwardImpl
    (adversary.main known publicContext root)

/-- The forwarded logical trace has the adversary's exact root-domain budget. -/
theorem hiddenRootForwardedAdversary_root_query_bound
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (root : HiddenRootCoordinate) :
    (hiddenRootForwardedAdversary adversary known publicContext root).IsQueryBoundP
      IsFixedHkdfRootStreamQuery qRoot := by
  exact jointKdfViewForwardImpl_root_query_bound
    (adversary.rootQueryBound known publicContext root)

/-- Logging every logical request leaves the final sticky-bad probability unchanged. -/
theorem jointKdfSimulate_withQueryLog_probEvent_bad_eq
    {alpha : Type}
    (impl : QueryImpl FixedHkdfSha512JointStreamSpec
      (StateT (JointKdfRO.QueryCache × Bool) ProbComp))
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha)
    (cache : JointKdfRO.QueryCache) (initialBad : Bool) :
    Pr[fun result : (alpha ×
          QueryLog FixedHkdfSha512JointStreamSpec) ×
          (JointKdfRO.QueryCache × Bool) => result.2.2 = true |
        (simulateQ impl computation.withQueryLog).run (cache, initialBad)] =
      Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
          result.2.2 = true |
        (simulateQ impl computation).run (cache, initialBad)] := by
  rw [← jointKdfSimulate_withQueryLog_run_project
    impl computation (cache, initialBad), probEvent_map]
  rfl

/-- Unprogrammed lazy execution with a response-dependent trace of every forwarded logical
request. -/
noncomputable def hiddenRootLoggedRandomRun
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (root : HiddenRootCoordinate) :
    ProbComp ((Bool × QueryLog FixedHkdfSha512JointStreamSpec) ×
      JointKdfRO.QueryCache) :=
  (simulateQ fixedHkdfSha512JointStreamRandomImpl
    (hiddenRootForwardedAdversary adversary known publicContext root).withQueryLog).run ∅

/-- Programming and unprogrammed tracking raise the same sticky bad event probability. -/
theorem jointKdfSingletonProgrammed_tracking_probEvent_bad_eq
    {alpha : Type} (target : JointKdfAddress) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha) :
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
        computation).run (∅, false)] =
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
        computation).run (∅, false)] := by
  exact OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (jointKdfSingletonProgrammedStreamImpl target stream)
    (jointKdfSingletonTrackingStreamImpl target stream)
    (jointKdfSingletonProgrammed_tracking_agree_good target stream)
    (jointKdfSingletonProgrammedStream_bad_monotone target stream)
    (jointKdfSingletonTrackingStream_bad_monotone target stream)
    computation ∅

/-- Once the trace is retained, forgetting the tracking flag gives the ordinary lazy random
joint-stream run without changing candidate events. -/
theorem jointKdfSingletonTracking_candidate_probEvent_eq_random
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    (target : JointKdfAddress) (stream : JointKdfStream)
    (hidden : HiddenRootCoordinate)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha) :
    Pr[fun result : (alpha × QueryLog FixedHkdfSha512JointStreamSpec) ×
          (JointKdfRO.QueryCache × Bool) =>
        some hidden ∈ hiddenRootStreamCandidates known result.1.2 |
      (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
        computation.withQueryLog).run (∅, false)] =
    Pr[fun result : (alpha × QueryLog FixedHkdfSha512JointStreamSpec) ×
          JointKdfRO.QueryCache =>
        some hidden ∈ hiddenRootStreamCandidates known result.1.2 |
      (simulateQ fixedHkdfSha512JointStreamRandomImpl
        computation.withQueryLog).run ∅] := by
  have hproject : Prod.map id Prod.fst <$>
        (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
          computation.withQueryLog).run (∅, false) =
      (simulateQ fixedHkdfSha512JointStreamRandomImpl
        computation.withQueryLog).run ∅ := by
    simpa [jointKdfSingletonTrackingStreamOrnament] using
      (jointKdfSingletonTrackingStreamOrnament target stream).run_eq
        computation.withQueryLog (∅, false) trivial
  rw [← hproject, probEvent_map]
  rfl

/-- For fixed independent `hidden32` and stream samples, the programming bad event is bounded by
the candidate-hit event in a run whose observable trace no longer depends on `hidden32`. -/
theorem jointKdfSingletonProgrammed_bad_le_random_candidate
    {alpha : Type} (known : KnownPqxdhRootCoordinates)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream)
    (computation : OracleComp FixedHkdfSha512JointStreamSpec alpha) :
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (jointKdfSingletonProgrammedStreamImpl
        (hiddenRootAddress known hidden) stream) computation).run (∅, false)] ≤
    Pr[fun result : (alpha × QueryLog FixedHkdfSha512JointStreamSpec) ×
          JointKdfRO.QueryCache =>
        some hidden ∈ hiddenRootStreamCandidates known result.1.2 |
      (simulateQ fixedHkdfSha512JointStreamRandomImpl
        computation.withQueryLog).run ∅] := by
  let target := hiddenRootAddress known hidden
  calc
    Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (jointKdfSingletonProgrammedStreamImpl target stream)
        computation).run (∅, false)] =
        Pr[fun result : alpha × JointKdfRO.QueryCache × Bool =>
          result.2.2 = true |
        (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
          computation).run (∅, false)] :=
      jointKdfSingletonProgrammed_tracking_probEvent_bad_eq
        target stream computation
    _ = Pr[fun result : (alpha ×
          QueryLog FixedHkdfSha512JointStreamSpec) ×
          (JointKdfRO.QueryCache × Bool) => result.2.2 = true |
        (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
          computation.withQueryLog).run (∅, false)] :=
      (jointKdfSimulate_withQueryLog_probEvent_bad_eq
        (jointKdfSingletonTrackingStreamImpl target stream)
        computation ∅ false).symm
    _ ≤ Pr[fun result : (alpha ×
          QueryLog FixedHkdfSha512JointStreamSpec) ×
          (JointKdfRO.QueryCache × Bool) =>
          some hidden ∈ hiddenRootStreamCandidates known result.1.2 |
        (simulateQ (jointKdfSingletonTrackingStreamImpl target stream)
          computation.withQueryLog).run (∅, false)] := by
      apply probEvent_mono
      intro result hresult hbad
      have htarget := jointKdfSingletonTracking_bad_implies_target_in_log
        target stream computation ∅ false result hresult hbad
      simp only [Bool.false_eq_true, false_or] at htarget
      exact (hiddenRootTarget_in_log_iff_candidate_mem known hidden result.1.2).mp
        htarget
    _ = Pr[fun result : (alpha ×
          QueryLog FixedHkdfSha512JointStreamSpec) × JointKdfRO.QueryCache =>
          some hidden ∈ hiddenRootStreamCandidates known result.1.2 |
        (simulateQ fixedHkdfSha512JointStreamRandomImpl
          computation.withQueryLog).run ∅] :=
      jointKdfSingletonTracking_candidate_probEvent_eq_random
        known target stream hidden computation

/-! ## Fixed candidate vectors and the 256-bit union bound -/

/-- One optional hidden-coordinate candidate slot per allowed root-domain logical query. -/
abbrev HiddenRootCandidateProbes (qRoot : ℕ) :=
  List.Vector (Option HiddenRootCoordinate) qRoot

/-- Some root-query candidate slot equals the hidden coordinate. -/
def HiddenRootCandidateHit {qRoot : ℕ} (hidden : HiddenRootCoordinate)
    (probes : HiddenRootCandidateProbes qRoot) : Prop :=
  ∃ index : Fin qRoot, probes.get index = some hidden

/-- Pad a bounded candidate trace with `none` to a fixed `qRoot`-slot vector. -/
def hiddenRootCandidateVector (qRoot : ℕ)
    (candidates : List (Option HiddenRootCoordinate)) :
    HiddenRootCandidateProbes qRoot :=
  List.Vector.ofFn fun index => (candidates[index.val]?).join

theorem hiddenRootCandidateVector_hit_of_mem {qRoot : ℕ}
    (candidates : List (Option HiddenRootCoordinate))
    (hidden : HiddenRootCoordinate) (hlen : candidates.length ≤ qRoot)
    (hmem : some hidden ∈ candidates) :
    HiddenRootCandidateHit hidden
      (hiddenRootCandidateVector qRoot candidates) := by
  obtain ⟨index, hindex, hcandidate⟩ := List.mem_iff_getElem.mp hmem
  let boundedIndex : Fin qRoot := ⟨index, lt_of_lt_of_le hindex hlen⟩
  refine ⟨boundedIndex, ?_⟩
  simp [hiddenRootCandidateVector, boundedIndex,
    List.getElem?_eq_getElem hindex, hcandidate]

theorem hiddenRootCandidateVector_mem_of_hit {qRoot : ℕ}
    (candidates : List (Option HiddenRootCoordinate))
    (hidden : HiddenRootCoordinate)
    (hhit : HiddenRootCandidateHit hidden
      (hiddenRootCandidateVector qRoot candidates)) :
    some hidden ∈ candidates := by
  obtain ⟨index, hcandidate⟩ := hhit
  simp only [hiddenRootCandidateVector, List.Vector.get_ofFn] at hcandidate
  cases hget : candidates[index.val]? with
  | none => simp [hget] at hcandidate
  | some candidate =>
      have hcandidate' : candidate = some hidden := by
        simpa [hget] using hcandidate
      rw [hcandidate'] at hget
      exact List.mem_iff_getElem?.mpr ⟨index.val, hget⟩

theorem hiddenRootCandidateVector_hit_iff_of_length_le {qRoot : ℕ}
    (candidates : List (Option HiddenRootCoordinate))
    (hidden : HiddenRootCoordinate) (hlen : candidates.length ≤ qRoot) :
    HiddenRootCandidateHit hidden
        (hiddenRootCandidateVector qRoot candidates) ↔
      some hidden ∈ candidates := by
  exact ⟨hiddenRootCandidateVector_mem_of_hit candidates hidden,
    hiddenRootCandidateVector_hit_of_mem candidates hidden hlen⟩

/-- The hidden final-coordinate space has exactly 256 bits. -/
theorem hiddenRootCoordinate_card :
    Fintype.card HiddenRootCoordinate = 2 ^ 256 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- A fixed `qRoot`-slot vector hits an independent uniform coordinate with probability at most
`qRoot / 2^256`. -/
theorem probEvent_uniformHiddenRoot_candidateHit_le {qRoot : ℕ}
    (probes : HiddenRootCandidateProbes qRoot) :
    Pr[fun hidden => HiddenRootCandidateHit hidden probes |
        $ᵗ HiddenRootCoordinate] ≤
      (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ := by
  classical
  calc
    Pr[fun hidden => HiddenRootCandidateHit hidden probes |
        $ᵗ HiddenRootCoordinate] ≤
        ∑ index : Fin qRoot,
          Pr[fun hidden => probes.get index = some hidden |
            $ᵗ HiddenRootCoordinate] := by
      simpa [HiddenRootCandidateHit] using
        (probEvent_exists_finset_le_sum
          (Finset.univ : Finset (Fin qRoot)) ($ᵗ HiddenRootCoordinate)
          (fun index hidden => probes.get index = some hidden))
    _ ≤ ∑ _index : Fin qRoot,
          (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_le_sum fun index _ => ?_
      cases hprobe : probes.get index with
      | none => simp
      | some candidate => simp
    _ = (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-! ## Independent trace guessing bound -/

/-- Generate the lazy-random logical trace before drawing the independent hidden coordinate.
This ordering makes the absence of hidden-coordinate dependence explicit. -/
noncomputable def hiddenRootIndependentCandidateExperiment
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp (HiddenRootCoordinate ×
      ((Bool × QueryLog FixedHkdfSha512JointStreamSpec) ×
        JointKdfRO.QueryCache)) := do
  let stream ← $ᵗ JointKdfStream
  let traced ← hiddenRootLoggedRandomRun adversary known publicContext
    (JointKdfProjection.first32.project stream)
  let hidden ← $ᵗ HiddenRootCoordinate
  pure (hidden, traced)

/-- An independent hidden coordinate hits the bounded logical root-query trace with probability
at most `qRoot / 2^256`. -/
theorem probEvent_hiddenRootIndependentCandidateExperiment_le
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    Pr[fun result =>
        some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
      hiddenRootIndependentCandidateExperiment adversary known publicContext] ≤
      (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ := by
  unfold hiddenRootIndependentCandidateExperiment
  refine probEvent_bind_le_of_forall_le fun stream _hstream => ?_
  refine probEvent_bind_le_of_forall_le fun traced htraced => ?_
  rw [show (fun hidden : HiddenRootCoordinate => pure (hidden, traced)) =
      pure ∘ (fun hidden => (hidden, traced)) from rfl,
    probEvent_bind_pure_comp]
  have htraceLength :
      (hiddenRootStreamCandidates known traced.1.2).length ≤ qRoot := by
    apply hiddenRootStreamCandidates_length_le_simulate known
      fixedHkdfSha512JointStreamRandomImpl
      (hiddenRootForwardedAdversary_root_query_bound
        adversary known publicContext
          (JointKdfProjection.first32.project stream)) ∅
    exact htraced
  let probes : HiddenRootCandidateProbes qRoot :=
    hiddenRootCandidateVector qRoot
      (hiddenRootStreamCandidates known traced.1.2)
  calc
    Pr[fun hidden : HiddenRootCoordinate =>
        some hidden ∈ hiddenRootStreamCandidates known traced.1.2 |
      $ᵗ HiddenRootCoordinate] =
        Pr[fun hidden : HiddenRootCoordinate => HiddenRootCandidateHit hidden probes |
          $ᵗ HiddenRootCoordinate] := by
      congr 1
      funext hidden
      apply propext
      exact (hiddenRootCandidateVector_hit_iff_of_length_le
        (hiddenRootStreamCandidates known traced.1.2) hidden htraceLength).symm
    _ ≤ (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ :=
      probEvent_uniformHiddenRoot_candidateHit_le probes

/-! ## Averaged programming bound and final reduction -/

/-- Tracking the singleton-programming bad flag while retaining only the adversary output. -/
noncomputable def hiddenRootTrackingGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool := do
  let hidden ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  (simulateQ (hiddenRootTrackingViewImpl known hidden stream)
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))).run' (∅, false)

/-- The tracking flag is an ornament: after it is forgotten, the stream and root samples remain
shared but the adversary starts with an ordinary empty lazy-stream cache. -/
noncomputable def hiddenRootProjectedStreamGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp Bool := do
  let _hidden ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  (simulateQ jointKdfViewRandomImpl
    (adversary.main known publicContext
      (jointKdfStreamSplitEquiv stream).1)).run' ∅

/-- Forgetting the tracking flag gives exactly the projected-stream game. -/
theorem hiddenRootTrackingGame_eq_projectedStreamGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    hiddenRootTrackingGame adversary known publicContext =
      hiddenRootProjectedStreamGame adversary known publicContext := by
  unfold hiddenRootTrackingGame hiddenRootProjectedStreamGame
  apply bind_congr
  intro hidden
  apply bind_congr
  intro stream
  rw [jointKdfStreamSplitEquiv_fst]
  exact hiddenRootTrackingView_run'_eq_random known hidden stream
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream)) ∅ false

/-- Sampling the first projection of a uniform complete stream gives exactly the independent
uniform root supplied to the source adversary. -/
theorem evalDist_hiddenRootProjectedStreamGame_eq_independentGame
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    𝒟[hiddenRootProjectedStreamGame adversary known publicContext] =
      𝒟[hiddenRootIndependentGame adversary known publicContext] := by
  unfold hiddenRootProjectedStreamGame hiddenRootIndependentGame
  refine evalDist_bind_congr' ($ᵗ HiddenRootCoordinate) fun _hidden => ?_
  let continuation : HiddenRootCoordinate → ProbComp Bool := fun root =>
    (simulateQ jointKdfViewRandomImpl
      (adversary.main known publicContext root)).run' ∅
  change
    𝒟[($ᵗ JointKdfStream) >>= fun stream =>
      continuation (jointKdfStreamSplitEquiv stream).1] =
    𝒟[($ᵗ HiddenRootCoordinate) >>= continuation]
  rw [show (($ᵗ JointKdfStream) >>= fun stream =>
      continuation (jointKdfStreamSplitEquiv stream).1) =
        (Prod.fst <$> (jointKdfStreamSplitEquiv <$> ($ᵗ JointKdfStream))) >>=
          continuation by rw [bind_map_left, bind_map_left]]
  have hprefix :
      𝒟[Prod.fst <$> (jointKdfStreamSplitEquiv <$> ($ᵗ JointKdfStream))] =
        𝒟[$ᵗ HiddenRootCoordinate] := by
    calc
      𝒟[Prod.fst <$> (jointKdfStreamSplitEquiv <$> ($ᵗ JointKdfStream))] =
          𝒟[Prod.fst <$> ($ᵗ
            (HiddenRootCoordinate × List.Vector UInt8 44))] := by
        rw [evalDist_map, evalDist_ext fun pair =>
          probOutput_map_bijective_uniform_cross
            (α := JointKdfStream)
            (β := HiddenRootCoordinate × List.Vector UInt8 44)
            jointKdfStreamSplitEquiv
            jointKdfStreamSplitEquiv.bijective pair, ← evalDist_map]
      _ = 𝒟[$ᵗ HiddenRootCoordinate] :=
        evalDist_map_fst_uniformSample_prod
  rw [evalDist_bind, evalDist_bind, hprefix]

/-- Stateful programmed execution used only to measure the one sticky target-address event. -/
noncomputable def hiddenRootProgrammedBadRun
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream) :
    ProbComp (Bool × JointKdfRO.QueryCache × Bool) :=
  (simulateQ (jointKdfSingletonProgrammedStreamImpl
      (hiddenRootAddress known hidden) stream)
    (hiddenRootForwardedAdversary adversary known publicContext
      (JointKdfProjection.first32.project stream))).run (∅, false)

/-- Sample both independent coordinates before measuring the programmed sticky-bad event. -/
noncomputable def hiddenRootProgrammedBadExperiment
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp (Bool × JointKdfRO.QueryCache × Bool) := do
  let hidden ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  hiddenRootProgrammedBadRun adversary known publicContext hidden stream

/-- Public-view composition and primitive forwarding measure the identical sticky-bad event. -/
theorem hiddenRootProgrammedView_probEvent_bad_eq
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext)
    (hidden : HiddenRootCoordinate) (stream : JointKdfStream) :
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      (simulateQ (hiddenRootProgrammedViewImpl known hidden stream)
        (adversary.main known publicContext
          (JointKdfProjection.first32.project stream))).run (∅, false)] =
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      hiddenRootProgrammedBadRun adversary known publicContext hidden stream] := by
  simp [hiddenRootProgrammedBadRun, hiddenRootProgrammedViewImpl,
    hiddenRootProgrammedStreamImpl, hiddenRootForwardedAdversary,
    QueryImpl.simulateQ_compose]

/-- Candidate-hit experiment in the same hidden-then-stream sampling order as programming. -/
noncomputable def hiddenRootHiddenFirstCandidateExperiment
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    ProbComp (HiddenRootCoordinate ×
      ((Bool × QueryLog FixedHkdfSha512JointStreamSpec) ×
        JointKdfRO.QueryCache)) := do
  let hidden ← $ᵗ HiddenRootCoordinate
  let stream ← $ᵗ JointKdfStream
  let traced ← hiddenRootLoggedRandomRun adversary known publicContext
    (JointKdfProjection.first32.project stream)
  pure (hidden, traced)

/-- Moving independent draws does not change the candidate-hit probability. -/
theorem hiddenRootHiddenFirstCandidate_probEvent_eq_independent
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    Pr[fun result =>
        some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
      hiddenRootHiddenFirstCandidateExperiment adversary known publicContext] =
    Pr[fun result =>
        some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
      hiddenRootIndependentCandidateExperiment adversary known publicContext] := by
  unfold hiddenRootHiddenFirstCandidateExperiment
    hiddenRootIndependentCandidateExperiment
  rw [probEvent_bind_bind_swap]
  refine probEvent_bind_congr' ($ᵗ JointKdfStream) _ fun stream => ?_
  rw [probEvent_bind_bind_swap]

/-- The one programmed sticky-bad event is contained in the hidden-coordinate candidate event. -/
theorem probEvent_hiddenRootProgrammedBadExperiment_le_hiddenFirstCandidate
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      hiddenRootProgrammedBadExperiment adversary known publicContext] ≤
    Pr[fun result =>
        some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
      hiddenRootHiddenFirstCandidateExperiment adversary known publicContext] := by
  calc
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      hiddenRootProgrammedBadExperiment adversary known publicContext] =
        ∑' hidden : HiddenRootCoordinate,
          Pr[= hidden | $ᵗ HiddenRootCoordinate] *
            ∑' stream : JointKdfStream,
              Pr[= stream | $ᵗ JointKdfStream] *
                Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
                    result.2.2 = true |
                  hiddenRootProgrammedBadRun adversary known publicContext
                    hidden stream] := by
      unfold hiddenRootProgrammedBadExperiment
      rw [probEvent_bind_eq_tsum]
      refine tsum_congr fun hidden => ?_
      rw [probEvent_bind_eq_tsum]
    _ ≤ ∑' hidden : HiddenRootCoordinate,
          Pr[= hidden | $ᵗ HiddenRootCoordinate] *
            ∑' stream : JointKdfStream,
              Pr[= stream | $ᵗ JointKdfStream] *
                Pr[fun traced =>
                    some hidden ∈ hiddenRootStreamCandidates known traced.1.2 |
                  hiddenRootLoggedRandomRun adversary known publicContext
                    (JointKdfProjection.first32.project stream)] := by
      refine ENNReal.tsum_le_tsum fun hidden => ?_
      apply mul_le_mul_left'
      refine ENNReal.tsum_le_tsum fun stream => ?_
      apply mul_le_mul_left'
      simpa [hiddenRootProgrammedBadRun, hiddenRootLoggedRandomRun] using
        (jointKdfSingletonProgrammed_bad_le_random_candidate
          known hidden stream
          (hiddenRootForwardedAdversary adversary known publicContext
            (JointKdfProjection.first32.project stream)))
    _ = Pr[fun result =>
        some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
      hiddenRootHiddenFirstCandidateExperiment adversary known publicContext] := by
      unfold hiddenRootHiddenFirstCandidateExperiment
      rw [probEvent_bind_eq_tsum]
      refine tsum_congr fun hidden => ?_
      rw [probEvent_bind_eq_tsum]
      refine congrArg (fun probability =>
        Pr[= hidden | $ᵗ HiddenRootCoordinate] * probability) ?_
      refine tsum_congr fun stream => ?_
      refine congrArg (fun probability =>
        Pr[= stream | $ᵗ JointKdfStream] * probability) ?_
      rw [show (fun traced => pure (hidden, traced)) =
          pure ∘ (fun traced => (hidden, traced)) from rfl,
        probEvent_bind_pure_comp]
      rfl

/-- Average pointwise TV bounds expressed as probabilities over the same shared draw. -/
theorem tvDist_bind_left_le_probEvent_bind
    {alpha beta gamma : Type} (sample : ProbComp alpha)
    (left right : alpha → ProbComp beta)
    (badRun : alpha → ProbComp gamma) (bad : gamma → Prop)
    (hpoint : ∀ value,
      tvDist (left value) (right value) ≤ Pr[bad | badRun value].toReal) :
    tvDist (sample >>= left) (sample >>= right) ≤
      Pr[bad | sample >>= badRun].toReal := by
  rw [probEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun value =>
    ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top)]
  simp_rw [ENNReal.toReal_mul]
  refine (tvDist_bind_left_le sample left right).trans ?_
  refine Summable.tsum_le_tsum (fun value => ?_) ?_ ?_
  · exact mul_le_mul_of_nonneg_left (hpoint value) ENNReal.toReal_nonneg
  · refine Summable.of_nonneg_of_le
      (fun value => mul_nonneg ENNReal.toReal_nonneg
        (tvDist_nonneg (left value) (right value)))
      (fun value => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (tvDist_le_one (left value) (right value))) ?_
    exact ENNReal.summable_toReal tsum_probOutput_ne_top
  · refine Summable.of_nonneg_of_le
      (fun value => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun value => mul_le_of_le_one_right ENNReal.toReal_nonneg ?_) ?_
    · exact ENNReal.toReal_mono one_ne_top probEvent_le_one
    · exact ENNReal.summable_toReal tsum_probOutput_ne_top

/-- Averaging over the hidden coordinate and complete stream charges singleton programming's
sticky target-address event exactly once. -/
theorem hiddenRootProgrammed_tracking_tvDist_le_programmedBad
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    tvDist (hiddenRootProgrammedGame adversary known publicContext)
        (hiddenRootTrackingGame adversary known publicContext) ≤
      Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
          result.2.2 = true |
        hiddenRootProgrammedBadExperiment adversary known publicContext].toReal := by
  unfold hiddenRootProgrammedGame hiddenRootTrackingGame
    hiddenRootProgrammedBadExperiment
  refine tvDist_bind_left_le_probEvent_bind
    ($ᵗ HiddenRootCoordinate) _ _ _ _ fun hidden => ?_
  refine tvDist_bind_left_le_probEvent_bind
    ($ᵗ JointKdfStream) _ _ _ _ fun stream => ?_
  rw [← hiddenRootProgrammedView_probEvent_bad_eq
    adversary known publicContext hidden stream]
  exact hiddenRootProgrammed_tracking_tvDist_le_bad known hidden stream
    (adversary.main known publicContext
      (JointKdfProjection.first32.project stream))

/-- The averaged sticky-bad probability is at most one 256-bit guess per logical root-domain
projection query. -/
theorem probEvent_hiddenRootProgrammedBadExperiment_le
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      hiddenRootProgrammedBadExperiment adversary known publicContext] ≤
      (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ := by
  calc
    Pr[fun result : Bool × JointKdfRO.QueryCache × Bool =>
        result.2.2 = true |
      hiddenRootProgrammedBadExperiment adversary known publicContext] ≤
        Pr[fun result =>
            some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
          hiddenRootHiddenFirstCandidateExperiment adversary known publicContext] :=
      probEvent_hiddenRootProgrammedBadExperiment_le_hiddenFirstCandidate
        adversary known publicContext
    _ = Pr[fun result =>
            some result.1 ∈ hiddenRootStreamCandidates known result.2.1.2 |
          hiddenRootIndependentCandidateExperiment adversary known publicContext] :=
      hiddenRootHiddenFirstCandidate_probEvent_eq_independent
        adversary known publicContext
    _ ≤ (qRoot : ℝ≥0∞) *
        (Fintype.card HiddenRootCoordinate : ℝ≥0∞)⁻¹ :=
      probEvent_hiddenRootIndependentCandidateExperiment_le
        adversary known publicContext

/-- Replacing the shared programmed root stream by an independent root costs at most
`qRoot / 2^256`; symmetric-domain queries never enter the event. -/
theorem tvDist_hiddenRootSharedRandomGame_independentGame_le
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    tvDist (hiddenRootSharedRandomGame adversary known publicContext)
        (hiddenRootIndependentGame adversary known publicContext) ≤
      ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  have htracking :
      𝒟[hiddenRootTrackingGame adversary known publicContext] =
        𝒟[hiddenRootIndependentGame adversary known publicContext] := by
    rw [hiddenRootTrackingGame_eq_projectedStreamGame]
    exact evalDist_hiddenRootProjectedStreamGame_eq_independentGame
      adversary known publicContext
  have htvdist :
      tvDist (hiddenRootProgrammedGame adversary known publicContext)
          (hiddenRootIndependentGame adversary known publicContext) =
        tvDist (hiddenRootProgrammedGame adversary known publicContext)
          (hiddenRootTrackingGame adversary known publicContext) := by
    unfold tvDist
    rw [htracking]
  have hbad := probEvent_hiddenRootProgrammedBadExperiment_le
    adversary known publicContext
  have hcard :
      (Fintype.card HiddenRootCoordinate : ℝ≥0∞) =
        (2 ^ 256 : ℝ≥0∞) := by
    have hcast := congrArg (fun cardinality : ℕ =>
      (cardinality : ℝ≥0∞)) hiddenRootCoordinate_card
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcast
  rw [hcard] at hbad
  have hfinite :
      (qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) ≠ ∞ := by
    finiteness
  rw [hiddenRootSharedRandomGame_eq_programmedGame, htvdist]
  exact (hiddenRootProgrammed_tracking_tvDist_le_programmedBad
    adversary known publicContext).trans (ENNReal.toReal_mono hfinite (by
      simpa only [div_eq_mul_inv] using hbad))

/-- The production-to-shared-root hop is exactly the named fixed-HKDF-SHA-512 joint-stream
primitive advantage of the bounded forwarding reduction. -/
theorem hiddenRootReal_shared_advantage_eq_fixedHkdfSha512JointStreamAdvantage
    (source : FixedHkdfSha512NoSaltSource)
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    (hiddenRootRealGame source adversary known publicContext).boolDistAdvantage
        (hiddenRootSharedRandomGame adversary known publicContext) =
      fixedHkdfSha512JointStreamAdvantage source
        (hiddenRootReduction adversary known publicContext) := by
  unfold fixedHkdfSha512JointStreamAdvantage
  rw [← hiddenRootRealGame_eq_fixedHkdfSha512JointStreamRealExp,
    ← hiddenRootSharedRandomGame_eq_fixedHkdfSha512JointStreamRandomExp]

/-- One-hidden-coordinate PQXDH root reduction.

The reduction makes at most `qU + 32` uniform-byte queries, at most `qRoot + 1` root-domain
stream queries (including its one honest lookup), at most `qSym` symmetric-domain queries, and
at most `qRoot + qSym + 1` stream queries in total.  Its terminal primitive assumption is the
fixed BeaconCrypt HKDF-SHA-512/no-salt joint-stream advantage; the only information-theoretic
loss is one 256-bit hidden-coordinate guess per adversarial root-domain logical query.
-/
theorem hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add
    (source : FixedHkdfSha512NoSaltSource)
    {PublicContext : Type} {qU qRoot qSym : ℕ}
    (adversary : HiddenRootSourceAdversary PublicContext qU qRoot qSym)
    (known : KnownPqxdhRootCoordinates) (publicContext : PublicContext) :
    hiddenRootAdvantage source adversary known publicContext ≤
      fixedHkdfSha512JointStreamAdvantage source
          (hiddenRootReduction adversary known publicContext) +
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
  have hindependent :
      (hiddenRootSharedRandomGame adversary known publicContext).boolDistAdvantage
          (hiddenRootIndependentGame adversary known publicContext) ≤
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
    have houtput := abs_probOutput_toReal_sub_le_tvDist
      (hiddenRootSharedRandomGame adversary known publicContext)
      (hiddenRootIndependentGame adversary known publicContext)
    have hadvantage :
        (hiddenRootSharedRandomGame adversary known publicContext).boolDistAdvantage
            (hiddenRootIndependentGame adversary known publicContext) ≤
          tvDist (hiddenRootSharedRandomGame adversary known publicContext)
            (hiddenRootIndependentGame adversary known publicContext) := by
      simpa [ProbComp.boolDistAdvantage] using houtput
    exact hadvantage.trans
      (tvDist_hiddenRootSharedRandomGame_independentGame_le
        adversary known publicContext)
  have hprimitive :=
    hiddenRootReal_shared_advantage_eq_fixedHkdfSha512JointStreamAdvantage
      source adversary known publicContext
  unfold hiddenRootAdvantage
  calc
    (hiddenRootRealGame source adversary known publicContext).boolDistAdvantage
        (hiddenRootIndependentGame adversary known publicContext) ≤
      (hiddenRootRealGame source adversary known publicContext).boolDistAdvantage
          (hiddenRootSharedRandomGame adversary known publicContext) +
        (hiddenRootSharedRandomGame adversary known publicContext).boolDistAdvantage
          (hiddenRootIndependentGame adversary known publicContext) :=
      ProbComp.boolDistAdvantage_triangle _ _ _
    _ ≤ fixedHkdfSha512JointStreamAdvantage source
          (hiddenRootReduction adversary known publicContext) +
        ((qRoot : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal := by
      exact add_le_add (le_of_eq hprimitive) hindependent

/--
info: 'BeaconcryptCore.Computational.PqxdhHiddenRoot.hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms hiddenRootAdvantage_le_fixedHkdfSha512JointStreamAdvantage_add

end BeaconcryptCore.Computational.PqxdhHiddenRoot
