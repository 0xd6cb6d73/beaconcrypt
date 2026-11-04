-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniformObserver
import BeaconcryptCore.Refinement.AdapterPublicAgreementCommonModel
/-! Each reached source primitive contract is transported from the same original probabilistic primitive computation. The uniform interpreter observes effects without replacing private objects, decapsulation outcomes, or returned RNG state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformPublicAdapterUniformObserver
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]
variable {m : Type→Type} [Monad m] [LawfulMonad m]
variable {I KemSK : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable (uniform : QueryImpl unifSpec m)
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)

noncomputable def model (contract : AdapterPublicAgreementCommonModel.Model (m:=ProbComp) setup view) :
    letI : CryptoOperations (RustT m):=operations uniform original
    AdapterPublicAgreementCommonModel.Model (m:=m) setup view := by
  letI : CryptoOperations (RustT m):=operations uniform original
  refine {
    representation:=contract.representation
    scalar:={failure:=contract.scalar.failure,operation:=?_}
    getters:={secret:=?_,publicKey:=?_}
    identity:={operation:=?_}
    conversion:={
      parse:=contract.conversion.parse
      conversion:=contract.conversion.conversion
      parseNormal:=contract.conversion.parseNormal
      parseView:=contract.conversion.parseView
      parseRejected:=contract.conversion.parseRejected
      operation:=?_
      value:=contract.conversion.value}
    hkdf:={prk:=contract.hkdf.prk,extract:=?_,expand:=?_}
    decapsulate:=fun ciphertext secret=>simulateQ uniform (contract.decapsulate ciphertext secret)
    decapView:=contract.decapView
    cipherParsing:={parse:=contract.cipherParsing.parse,operation:=?_,exactBytes:=contract.cipherParsing.exactBytes}
    shared:={realize:=contract.shared.realize,exactBytes:=contract.shared.exactBytes,getter:=?_}
    decap:={failure:=contract.decap.failure,operation:=?_} }
  · intro secret publicKey
    change observe uniform (original.scalarMult secret.to_slice publicKey.to_slice)=_
    rw [contract.scalar.operation,pure_observe]
  · intro key
    change observe uniform (original.kxSecretBytes key)=_
    rw [contract.getters.secret,pure_observe]
  · intro key
    change observe uniform (original.kxPublicBytes key)=_
    rw [contract.getters.publicKey,pure_observe]
  · intro key
    change observe uniform (original.convertSecret key)=_
    rw [contract.identity.operation,pure_observe]
  · intro key
    change observe uniform (original.convertPublic key)=_
    rw [contract.conversion.operation,pure_observe]
  · intro input
    change observe uniform (original.extract .None (Array.to_slice input))=_
    rw [contract.hkdf.extract,pure_observe]
  · intro input info
    change observe uniform (original.expand 32#usize (.Some (Array.to_slice info)) (contract.hkdf.prk input))=_
    rw [contract.hkdf.expand,pure_observe]
  · intro input
    change observe uniform (original.kemCipherFromBytes input.to_slice)=_
    rw [contract.cipherParsing.operation,pure_observe]
  · intro shared
    change observe uniform (original.kemSharedBytes shared)=_
    rw [contract.shared.getter,pure_observe]
  · intro ciphertext secret
    change observe uniform (original.decapsulate ciphertext secret)=_
    rw [contract.decap.operation,lift_observe,simulateQ_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel.model' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel.model
