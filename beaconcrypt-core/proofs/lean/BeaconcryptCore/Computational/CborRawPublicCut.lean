-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPublicClient
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCut

/-! The public registration client delegates each CE query once and leaves raw accepts unchanged. Cutting before a selected accept therefore retains the exact reached public state and suspends the same accept; its continuation updates that state using the actual eventual answer. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawPublicCut

open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealCut (CutCE scanCE scanCE_pure scanCE_accept_zero scanCE_accept_succ scanCE_other)
open CborRawPublicClient (client request reply next)
open CborRawPublicState (Public)
variable {X : Type}

noncomputable def publicCut (cut : CutCE X × Public) : CutCE (X × Public) :=
  match cut.1 with
  | .complete value => .complete (value, cut.2)
  | .pending raw continuation => .pending raw fun answer =>
      client (continuation answer) (next cut.2 (.inr (.accept raw)) answer)

theorem client_query_bind (query : Spec.Domain) (continuation : Spec.Range query → OracleComp Spec X) (state : Public) :
    client ((Spec.query query : OracleComp Spec _) >>= continuation) state =
      ((Spec.query (request state query) : OracleComp Spec _) >>= fun answer =>
        client (continuation (reply state query answer)) (next state query answer)) := by
  simp only [client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  simp only [CborRawPublicClient.handler, StateT.run, bind_assoc, pure_bind]

theorem scan_client (work : OracleComp Spec X) (index : Nat) (state : Public) :
    scanCE (client work state) index = publicCut <$> client (scanCE work index) state := by
  induction work using OracleComp.inductionOn generalizing index state with
  | pure value => rfl
  | query_bind query continuation ih =>
      by_cases accept : PqxdhDeploymentCompileBudget.commandKind query = 3
      · rcases query with coin | command
        · exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
        · cases command with
          | accept raw =>
              cases index with
              | zero =>
                  rw [client_query_bind, scanCE_accept_zero]
                  rfl
              | succ index =>
                  rw [client_query_bind]
                  simp only [request, CborRawMiddleRegistration.request]
                  rw [scanCE_accept_succ, scanCE_accept_succ, client_query_bind]
                  simp only [map_bind, request, CborRawMiddleRegistration.request,
                    reply, CborRawMiddleRegistration.reply, id_eq]
                  apply bind_congr
                  intro answer
                  exact ih answer index (next state (.inr (.accept raw)) answer)
          | _ => exact absurd accept (by simp [PqxdhDeploymentCompileBudget.commandKind])
      · have transformed : PqxdhDeploymentCompileBudget.commandKind (request state query) ≠ 3 := by
          simpa only [request, CborRawMiddleRegistration.request_kind] using accept
        rw [client_query_bind, scanCE_other _ transformed, scanCE_other _ accept, client_query_bind]
        simp only [map_bind]
        apply bind_congr
        intro answer
        exact ih (reply state query answer) index (next state query answer)

end BeaconcryptCore.Computational.CborRawPublicCut

/-- info: 'BeaconcryptCore.Computational.CborRawPublicCut.client_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicCut.client_query_bind

/-- info: 'BeaconcryptCore.Computational.CborRawPublicCut.scan_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPublicCut.scan_client
