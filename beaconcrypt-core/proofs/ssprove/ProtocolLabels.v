(* SPDX-License-Identifier: 0BSD *)

(** Exact production domain labels and KDF-use bookkeeping shared by the finite SSProve games.

    Rocq strings are sequences of eight-bit [ascii] values, so the literals below model the production byte strings without a terminating NUL. The Boolean tag is only a finite encoding used by the existing random-oracle tables. Its injectivity theorem ties that encoding to the exact labels; it is not an additional production byte.

    Initial symmetric-ratchet expansion and every record step intentionally use the same label. Output length is therefore not a domain separator: a faithful HKDF model must expose one prefix-consistent stream for an equal label and input. *)

From Stdlib Require Import Strings.String Lia.

Open Scope string_scope.

Definition pqxdh_info : string :=
  "BeaconcryptPqxdh_CURVE25519_SHA-512_ML-KEM-768".

Definition symmetric_ratchet_info : string :=
  "SymRatchet_HKDF_SHA-512_CHACHA20_POLY1305".

Inductive kdf_domain : Type :=
| PqxdhRootDomain
| SymmetricRatchetDomain.

Definition kdf_domain_info (domain : kdf_domain) : string :=
  match domain with
  | PqxdhRootDomain => pqxdh_info
  | SymmetricRatchetDomain => symmetric_ratchet_info
  end.

(** Finite encoding used in the existing Boolean ROM query types. *)
Definition kdf_domain_tag (domain : kdf_domain) : bool :=
  match domain with
  | PqxdhRootDomain => false
  | SymmetricRatchetDomain => true
  end.

Inductive kdf_use : Type :=
| PqxdhRootDerivation
| InitialRatchetExpansion
| RatchetStepExpansion.

Definition kdf_use_domain (use : kdf_use) : kdf_domain :=
  match use with
  | PqxdhRootDerivation => PqxdhRootDomain
  | InitialRatchetExpansion | RatchetStepExpansion =>
      SymmetricRatchetDomain
  end.

Definition kdf_use_info (use : kdf_use) : string :=
  kdf_domain_info (kdf_use_domain use).

Definition kdf_output_size (use : kdf_use) : nat :=
  match use with
  | PqxdhRootDerivation => 32
  | InitialRatchetExpansion => 64
  | RatchetStepExpansion => 76
  end.

(** The final 87 bytes of production associated data, after the two tagged 33-byte identities. *)
Definition associated_data_label_suffix : string :=
  String.append pqxdh_info symmetric_ratchet_info.

Lemma pqxdh_info_has_production_length :
  String.length pqxdh_info = 46.
Proof. reflexivity. Qed.

Lemma symmetric_ratchet_info_has_production_length :
  String.length symmetric_ratchet_info = 41.
Proof. reflexivity. Qed.

Lemma production_kdf_labels_are_distinct :
  pqxdh_info <> symmetric_ratchet_info.
Proof. discriminate. Qed.

Theorem production_kdf_labels_are_exact :
  String.length pqxdh_info = 46 /\
  String.length symmetric_ratchet_info = 41 /\
  pqxdh_info <> symmetric_ratchet_info.
Proof.
  split; [exact pqxdh_info_has_production_length|].
  split; [exact symmetric_ratchet_info_has_production_length|].
  exact production_kdf_labels_are_distinct.
Qed.

Lemma kdf_domain_tag_is_injective :
  forall left right,
    kdf_domain_tag left = kdf_domain_tag right -> left = right.
Proof.
  intros [] [] tags_equal; simpl in tags_equal; try reflexivity;
    discriminate.
Qed.

Lemma kdf_domain_info_is_injective :
  forall left right,
    kdf_domain_info left = kdf_domain_info right -> left = right.
Proof.
  intros [] [] info_equal; simpl in info_equal; try reflexivity;
    discriminate.
Qed.

(** Equality of finite tags is exactly equality of the corresponding production label bytes. *)
Theorem kdf_domain_tag_models_exact_info :
  forall left right,
    kdf_domain_tag left = kdf_domain_tag right <->
    kdf_domain_info left = kdf_domain_info right.
Proof.
  intros [] []; simpl; split; intros equality; try reflexivity;
    discriminate.
Qed.

(** There is no initial-versus-step symmetric domain separator in production. *)
Theorem initial_and_step_share_symmetric_domain :
  kdf_use_domain InitialRatchetExpansion = SymmetricRatchetDomain /\
  kdf_use_domain RatchetStepExpansion = SymmetricRatchetDomain /\
  kdf_use_info InitialRatchetExpansion =
    kdf_use_info RatchetStepExpansion.
Proof. repeat split; reflexivity. Qed.

Theorem production_kdf_output_sizes :
  kdf_output_size PqxdhRootDerivation = 32 /\
  kdf_output_size InitialRatchetExpansion = 64 /\
  kdf_output_size RatchetStepExpansion = 76 /\
  kdf_output_size InitialRatchetExpansion <=
    kdf_output_size RatchetStepExpansion.
Proof. repeat split; simpl; lia. Qed.

Theorem associated_data_label_suffix_is_exact :
  String.length associated_data_label_suffix = 87 /\
  String.substring 0 46 associated_data_label_suffix = pqxdh_info /\
  String.substring 46 41 associated_data_label_suffix =
    symmetric_ratchet_info.
Proof. repeat split; reflexivity. Qed.

Print Assumptions kdf_domain_tag_models_exact_info.
Print Assumptions production_kdf_labels_are_exact.
Print Assumptions initial_and_step_share_symmetric_domain.
Print Assumptions production_kdf_output_sizes.
Print Assumptions associated_data_label_suffix_is_exact.
