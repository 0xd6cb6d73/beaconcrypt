-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyCore
import BeaconcryptCore.Computational.RegistrationNativeEntropyEncode

/-! Exact ordinary-query simulation of the old record environment transport and the actual native full ledger. The projection reconstructs native ML creation pins from the complete transport transcript, while retaining all original private tests, fresh messages and optional callback poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyLayer
variable {Reader Response : Type}

/-- Restoring an encoded entry gives the actual native record operation, with original private secrets retained. -/
theorem restore_append (before : PqxdhDeploymentSecrecy.Ledger)
    (entry : RegistrationNativeInterface.Entry) :
    RegistrationNativeEntropyRestore.ledger { before with transcript :=
        before.transcript ++ RegistrationNativeEntropyEncode.entry entry } =
      RegistrationNativeLedger.record (RegistrationNativeEntropyRestore.ledger before) entry := by
  simp only [RegistrationNativeEntropyRestore.ledger, RegistrationNativeEntropyRestore.from_append,
    RegistrationNativeEntropyEncode.entry_decode, RegistrationNativeLedger.record, List.map_append,
    List.map_cons, List.map_nil]

/-- Creation restoration ignores the marker's arbitrary reply and retains the literal native ML pin. -/
theorem restore_create (before : PqxdhDeploymentSecrecy.Ledger) (edPin mlPin : Pqxdh.Bytes)
    (keyId : Std.U64) (markerReply : PqxdhSecretInputKdf.HmacBlock) (reply : Option Nat) :
    RegistrationNativeEntropyRestore.ledger
      ((before.record (.inl (.inr (.hmac PqxdhSecretInputKdf.zeroSalt
          (RegistrationNativeEntropyInterface.metadata mlPin)))) markerReply).record
        (.inl (.inr (.create edPin keyId))) reply) =
      RegistrationNativeLedger.record (RegistrationNativeEntropyRestore.ledger before)
        ⟨.inl (.inr (.create edPin mlPin keyId)), reply⟩ := by
  simp only [PqxdhDeploymentSecrecy.Ledger.record, List.append_assoc,
    RegistrationNativeEntropyRestore.ledger, RegistrationNativeEntropyRestore.from_append,
    RegistrationNativeEntropyRestore.decodeFrom, RegistrationNativeEntropyRestore.entry, RegistrationNativeEntropyInterface.decode_metadata,
    RegistrationNativeLedger.record, List.map_append,
    List.map_cons, List.map_nil, Option.toList, List.nil_append, List.cons_append]
  rfl

/-- Compiling a native ordinary query through the literal old full ledger restores the actual complete native ledger. -/
theorem ledger_core (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.Spec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger) :
    (fun result => (result.1, RegistrationNativeEntropyRestore.ledger result.2)) <$>
        (simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)
          (RegistrationNativeEntropyCompile.modeO (.inl query))).run before =
      simulateQ RegistrationNativeEntropyCore.compiler
        ((RegistrationNativeLedger.handler crypto codec serverKid bounds (.inl query)).run
          (RegistrationNativeEntropyRestore.ledger before)) := by
  rw [RegistrationNativeLedger.query_forward, simulateQ_map, simulateQ_spec_query]
  cases query with
  | inl coin =>
      simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
        PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
        RegistrationNativeEntropyCore.compiler]
      congr 1
      funext reply
      exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inl coin), reply⟩)
  | inr command =>
      cases command with
      | create edPin mlPin keyId =>
          change (fun result => (result.1, RegistrationNativeEntropyRestore.ledger result.2)) <$>
            ((PqxdhDeploymentInterface.Spec.query (.inr (.hmac PqxdhSecretInputKdf.zeroSalt
                (RegistrationNativeEntropyInterface.metadata mlPin))) : OracleComp PqxdhDeploymentInterface.Spec _) >>=
              fun markerReply => (fun reply => (reply,
                ((before.record (.inl (.inr (.hmac PqxdhSecretInputKdf.zeroSalt
                  (RegistrationNativeEntropyInterface.metadata mlPin))))) markerReply).record
                    (.inl (.inr (.create edPin keyId))) reply)) <$>
                  (PqxdhDeploymentInterface.Spec.query (.inr (.create edPin keyId)) :
                    OracleComp PqxdhDeploymentInterface.Spec _)) = _
          simp only [RegistrationNativeEntropyCore.compiler, map_bind]
          apply bind_congr
          intro markerReply
          simp only [Functor.map_map]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_create before edPin mlPin keyId markerReply reply)
      | bundle owner =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.bundle owner)), reply⟩)
      | accept raw =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.accept raw)), reply⟩)
      | build session payload =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.build session payload)), reply⟩)
      | finish owner raw =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.finish owner raw)), reply⟩)
      | hmac key message =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.hmac key message)), reply⟩)
      | hash bytes =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.hash bytes)), reply⟩)
      | serverSend keyId plaintext =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.serverSend keyId plaintext)), reply⟩)
      | serverRaw raw =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.serverRaw raw)), reply⟩)
      | beaconSend owner plaintext =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.beaconSend owner plaintext)), reply⟩)
      | beaconRaw owner raw =>
          simp only [RegistrationNativeEntropyCompile.modeO, simulateQ_spec_query,
            PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, Functor.map_map,
            RegistrationNativeEntropyCore.compiler]
          congr 1
          funext reply
          exact congrArg (Prod.mk reply) (restore_append before ⟨.inl (.inr (.beaconRaw owner raw)), reply⟩)

end BeaconcryptCore.Computational.RegistrationNativeEntropyLayer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.restore_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.restore_append
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.restore_create' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.restore_create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.ledger_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyLayer.ledger_core
