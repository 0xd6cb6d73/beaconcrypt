import BeaconcryptCore.Computational.PqxdhServerAuthControlWitness

open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf

abbrev Bits := Fin 256 → Bool

/-- A finite representation of the toy's exact 32-byte words; this is a consistency witness, not a primitive implementation. -/
theorem word_card : Fintype.card RootOutput = Fintype.card Bits := by
  rw [CtxNonceAeadIndDollar.ctxKey_card]
  simp [Bits]

/-- A zero-preserving finite encoding, chosen only for the mathematical consistency witness. -/
noncomputable def wordEncoding : RootOutput ≃ Bits :=
  let raw : RootOutput ≃ Bits := Fintype.equivOfCardEq word_card
  raw.trans (Equiv.swap (raw zeroDh) (fun _ => false))

/-- The all-zero wire word is represented by the all-false bit function. -/
theorem encoding_zero : wordEncoding zeroDh = fun _ => false := by
  simp [wordEncoding]

/-- The abstract toy accepts every byte string by normalizing to a fixed-width word; source-width scalar inputs are unchanged. -/
def normalize (bytes : Pqxdh.Bytes) : RootOutput :=
  if h : bytes.length = 32 then ⟨bytes, h⟩ else zeroDh

/-- Every actual 32-byte scalar and peer retains its complete value through normalization. -/
theorem normalize_word (value : RootOutput) : normalize value.toList = value := by
  simp [normalize]

/-- Symmetric toy agreement forces one output bit and retains all other XOR bits. At most one scalar bit is lost. -/
def marked (left right : Bits) : Bits := fun i => if i = 0 then true else left i ^^ right i

/-- The toy's complete agreement output is symmetric. -/
theorem marked_comm (left right : Bits) : marked left right = marked right left := by
  funext i
  simp [marked, Bool.xor_comm]

/-- The forced bit excludes the all-zero DH output for every normalized input. -/
theorem marked_nonzero (left right : Bits) : marked left right ≠ fun _ => false := by
  intro same
  have atZero := congrFun same 0
  simp [marked] at atZero

/-- Equality of two peers under one toy scalar preserves equality under every other scalar, including the bit alias. -/
theorem marked_class (a b left right : Bits) (same : marked a left = marked a right) :
    marked b left = marked b right := by
  funext i
  by_cases atZero : i = 0
  · simp [marked, atZero]
  · have equal := congrFun same i
    simp only [marked, atZero, ite_false, Bool.xor_right_inj] at equal
    simp only [marked, atZero, ite_false, equal]

/-- Supplying the one erased scalar bit reconstructs the complete toy scalar from a peer and output. -/
def recover (peer value : Bits) (first : Bool) : Bits := fun i => if i = 0 then first else value i ^^ peer i

/-- Only the scalar's first bit is lost by the symmetric marked output. -/
theorem marked_recover (a peer : Bits) : a = recover peer (marked a peer) (a 0) := by
  funext i
  by_cases atZero : i = 0
  · simp [recover, atZero]
  · simp [recover, marked, atZero]

/-- A fixed peer and output have at most the two preimages obtained by restoring the erased first bit. -/
theorem marked_fiber (a peer value : Bits) (same : marked a peer = value) :
    a = recover peer value false ∨ a = recover peer value true := by
  have restored := marked_recover a peer
  rw [same] at restored
  cases first : a 0
  · exact Or.inl (by simpa only [first] using restored)
  · exact Or.inr (by simpa only [first] using restored)

/-- The finite word-level toy agreement. No claim about computational security or X25519's implementation is made. -/
noncomputable def agreement (a peer : RootOutput) : RootOutput :=
  wordEncoding.symm (marked (wordEncoding a) (wordEncoding peer))

/-- The complete byte-word result preserves the symmetric agreement law. -/
theorem agreement_comm (a b : RootOutput) : agreement a b = agreement b a := by
  simp only [agreement, marked_comm]

/-- Every word-level toy agreement output is nonzero. -/
theorem agreement_nonzero (a peer : RootOutput) : agreement a peer ≠ zeroDh := by
  intro same
  have encoded := congrArg wordEncoding same
  simp only [agreement, Equiv.apply_symm_apply, encoding_zero] at encoded
  exact marked_nonzero (wordEncoding a) (wordEncoding peer) encoded

/-- A peer alias under one scalar remains an alias under every scalar. -/
theorem agreement_class (a b left right : RootOutput)
    (same : agreement a left = agreement a right) : agreement b left = agreement b right := by
  apply wordEncoding.injective
  simp only [agreement, Equiv.apply_symm_apply]
  apply marked_class (wordEncoding a)
  simpa only [agreement, Equiv.apply_symm_apply] using congrArg wordEncoding same

/-- A fixed complete word output has at most the two explicitly reconstructed scalars. -/
theorem agreement_fiber (a peer value : RootOutput) (same : agreement a peer = value) :
    a = wordEncoding.symm (recover (wordEncoding peer) (wordEncoding value) false) ∨
    a = wordEncoding.symm (recover (wordEncoding peer) (wordEncoding value) true) := by
  have encoded : marked (wordEncoding a) (wordEncoding peer) = wordEncoding value :=
    by simpa only [agreement, Equiv.apply_symm_apply] using congrArg wordEncoding same
  exact (marked_fiber (wordEncoding a) (wordEncoding peer) (wordEncoding value) encoded).imp
    (fun found => wordEncoding.injective (by simpa only [Equiv.apply_symm_apply] using found))
    (fun found => wordEncoding.injective (by simpa only [Equiv.apply_symm_apply] using found))

/-- The full finite scalar fiber fits in two explicit candidates, independently of the 256-bit space size. -/
theorem agreement_fiber_card (peer value : RootOutput) :
    (Finset.univ.filter fun a : RootOutput => agreement a peer = value).card ≤ 2 := by
  classical
  apply le_trans (Finset.card_le_card (t :=
    {wordEncoding.symm (recover (wordEncoding peer) (wordEncoding value) false),
      wordEncoding.symm (recover (wordEncoding peer) (wordEncoding value) true)}) ?_)
  · exact (Finset.card_insert_le _ _).trans (by simp)
  intro a selected
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    agreement_fiber a peer value (Finset.mem_filter.mp selected).2

/-- Raw toy public conversion, with a fixed-width source interface. -/
def publicKey (a : Pqxdh.Bytes) : Pqxdh.Bytes := (normalize a).toList

/-- Raw toy agreement, normalized at both inputs. -/
noncomputable def rawAgreement (a peer : Pqxdh.Bytes) : Pqxdh.Bytes :=
  (agreement (normalize a) (normalize peer)).toList

/-- The actual typed scalar distribution has at most two preimages under a fixed peer. -/
theorem raw_fiber_card (peer value : RootOutput) :
    (Finset.univ.filter fun a : RootOutput => rawAgreement a.toList peer.toList = value.toList).card ≤ 2 := by
  classical
  simpa only [rawAgreement, normalize_word, List.Vector.toList_injective.eq_iff] using agreement_fiber_card peer value

/-- Raw source-style agreement commutes for arbitrary normalized secret byte strings. -/
theorem raw_comm (a b : Pqxdh.Bytes) : rawAgreement a (publicKey b) = rawAgreement b (publicKey a) := by
  simp only [rawAgreement, publicKey, normalize_word, agreement_comm]

/-- The raw toy never returns the rejected zero output, including on non-source-width inputs. -/
theorem raw_nonzero (a peer : Pqxdh.Bytes) : rawAgreement a peer ≠ Pqxdh.zero32 := by
  exact fun same => agreement_nonzero (normalize a) (normalize peer) (Subtype.ext same)

/-- The raw toy satisfies the complete peer-alias class law, over every byte-string length. -/
theorem raw_class (a b left right : Pqxdh.Bytes) (same : rawAgreement a left = rawAgreement a right) :
    rawAgreement b left = rawAgreement b right := by
  exact congrArg List.Vector.toList (agreement_class (normalize a) (normalize b)
    (normalize left) (normalize right) (Subtype.ext same))

end BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.word_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.word_card
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.encoding_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.encoding_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.normalize_word' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.normalize_word
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_comm
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_nonzero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_nonzero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_recover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_recover
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_fiber' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.marked_fiber
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_comm
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_nonzero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_class
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_fiber' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_fiber
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_fiber_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.agreement_fiber_card
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_fiber_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_fiber_card
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_comm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_comm
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_nonzero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh.raw_class
