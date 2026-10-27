import BeaconcryptCore.Computational.RawCtxSelectedMessageFamily
import BeaconcryptCore.Computational.PqxdhInitialGenericBuilder

/-!
The actual first Server response uses the material-labelled private table and complete source send driver. Its executable generic builder carries an opaque selected material slot. The selected key occurs only in the mathematical native interpreter, never in the source builder's kernel representation. Every optional seal, serialization, publication, allocation and erasure branch is retained.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKey RawCtxSelectedMessageReveals RawCtxSelectedMessageDriver
open RawCtxSelectedMessageKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {M P A : Type}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The actual full native first-send callback is realized by the concrete opaque-material driver, with its shared cache and every private effect. -/
theorem send_source (kernel : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (((RawCtxFunctionalFamily.native (A := A) source writer
        (privateTable prior parent target (response key nonce next))) ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send (nativeKernel key kernel) context) =
      (fun result => (nativeKernel key result.1, result.2)) <$>
        (RawCtxSelectedMessageFamily.calls
          (receiveServices source writer prior parent key target nonce next)
          (sendServices source writer prior parent key target nonce next) parent target nonce next).send kernel context := by
  exact RawCtxSelectedMessageDriver.send_source source writer prior parent key target nonce next kernel context

/-- The complete production Ready builder retains consumed input, identity/allocation gates, first seal, erase, serialization and successful publication under the exact selected-message interpreter. -/
theorem ready_source
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    simulateQ (PqxdhInitialGenericPublication.nativeImpl
      (RawCtxFunctionalFamily.native source writer (privateTable prior parent target (response key nonce next))) aux)
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (PqxdhInitialBuilderCut.readyBuild source (nativeKernel key <$> initial) binding ready metadata
          (PqxdhInitialGenericPublication.native (nativeKernel key) state))) =
      Functor.map (Prod.map id (PqxdhInitialGenericPublication.native (nativeKernel key))) <$>
        PqxdhInitialGenericBuilder.readyBuild source
          (RawCtxSelectedMessageFamily.calls
            (receiveServices source writer prior parent key target nonce next)
            (sendServices source writer prior parent key target nonce next) parent target nonce next)
          aux initial binding ready metadata state :=
  PqxdhInitialGenericBuilder.ready_native source (nativeKernel key) _ _ aux
    (send_source source writer prior parent key target nonce next) initial binding ready metadata state

end BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder.send_source

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder.ready_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageBuilder.ready_source
