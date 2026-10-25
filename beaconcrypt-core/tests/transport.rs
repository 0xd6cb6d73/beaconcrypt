// SPDX-License-Identifier: 0BSD

mod tests {
	use beaconcrypt_core::transport::*;

	#[test]
	fn canonical_argument_widths_cover_each_integer_boundary() {
		for (value, width) in [
			(0, 1),
			(23, 1),
			(24, 2),
			(255, 2),
			(256, 3),
			(65_535, 3),
			(65_536, 5),
			(u32::MAX as u64, 5),
			(u32::MAX as u64 + 1, 9),
			(u64::MAX, 9),
		] {
			assert_eq!(argument_len(value), width);
		}
	}

	#[test]
	fn exact_lengths_include_every_header_and_field() {
		assert_eq!(encoded_frame_len(0, 0, 0), Some(6));
		assert_eq!(encoded_frame_len(24, 256, 65_536), Some(65_549));
		assert_eq!(encoded_frame_len(u64::MAX, u64::MAX, 23), Some(45));
		assert_eq!(encoded_init_len([0; 6]), Some(9));
		assert_eq!(encoded_init_len([1, 24, 256, 65_536, 0, 0]), Some(65_833));
		assert_eq!(encoded_init_len([33, 98, 98, 1249, 1952, 3309]), Some(6757));
		assert_eq!(encoded_response_len([0; 5], 0), Some(9));
		assert_eq!(
			encoded_response_len([1, 24, 256, 65_536, 0], u64::MAX),
			Some(65_841)
		);
	}

	#[test]
	fn complete_message_limit_is_inclusive_for_every_layout_and_integer_width() {
		assert_eq!(MAX_MESSAGE_SIZE, 33_554_432);
		for (seq, key_id, overhead) in [(0, 0, 10), (24, 256, 13), (u64::MAX, u64::MAX, 26)] {
			assert_eq!(
				encoded_frame_len(seq, key_id, MAX_MESSAGE_SIZE - overhead),
				Some(MAX_MESSAGE_SIZE)
			);
			assert_eq!(
				encoded_frame_len(seq, key_id, MAX_MESSAGE_SIZE - overhead + 1),
				None
			);
		}
		for field in 0..6 {
			let mut lengths = [0; 6];
			lengths[field] = MAX_MESSAGE_SIZE - 13;
			assert_eq!(encoded_init_len(lengths), Some(MAX_MESSAGE_SIZE));
			lengths[field] += 1;
			assert_eq!(encoded_init_len(lengths), None);
		}
		for field in 0..5 {
			let mut lengths = [0; 5];
			for (key_id, overhead) in [(0, 13), (24, 14), (u64::MAX, 21)] {
				lengths[field] = MAX_MESSAGE_SIZE - overhead;
				assert_eq!(
					encoded_response_len(lengths, key_id),
					Some(MAX_MESSAGE_SIZE)
				);
				lengths[field] += 1;
				assert_eq!(encoded_response_len(lengths, key_id), None);
			}
		}
	}

	#[test]
	fn sizing_rejects_usize_overflow_and_oversized_combinations() {
		for impossible in [usize::MAX, usize::MAX - 8, MAX_MESSAGE_SIZE] {
			assert_eq!(encoded_frame_len(0, 0, impossible), None);
			for field in 0..6 {
				let mut lengths = [0; 6];
				lengths[field] = impossible;
				assert_eq!(encoded_init_len(lengths), None);
			}
			for field in 0..5 {
				let mut lengths = [0; 5];
				lengths[field] = impossible;
				assert_eq!(encoded_response_len(lengths, 0), None);
			}
		}
		assert_eq!(encoded_init_len([MAX_MESSAGE_SIZE / 6; 6]), None);
		assert_eq!(encoded_response_len([MAX_MESSAGE_SIZE / 5; 5], 0), None);
		assert_eq!(encoded_init_len([usize::MAX - 12, 12, 0, 0, 0, 0]), None);
	}

	#[test]
	fn protected_lengths_include_all_authentication_and_registration_fields() {
		for sender in [0, 23, 24, 255, 256, u32::MAX as u64, u64::MAX] {
			for sequence in [0, 23, 24, 256, u64::MAX] {
				for length in [0, 1, 23, 24, 255, 256, 65_535] {
					assert_eq!(
						protected_frame_len(length, sequence, sender),
						encoded_frame_len(sequence, sender, length + 80)
					);
				}
			}
			for length in [0, 1, 23, 255, 65_536] {
				assert_eq!(
					registration_response_len(length, sender),
					encoded_response_len([32, 32, 1088, length + 88, 3309], sender)
				);
			}
		}
		assert_eq!(registration_response_len(usize::MAX, 1), None);
		assert_eq!(protected_frame_len(usize::MAX, 1, 1), None);
		assert_eq!(
			registration_response_len(MAX_MESSAGE_SIZE - 4_568, 1),
			Some(MAX_MESSAGE_SIZE)
		);
		assert_eq!(
			registration_response_len(MAX_MESSAGE_SIZE - 4_568 + 1, 1),
			None
		);
		assert_eq!(
			registration_response_len(MAX_MESSAGE_SIZE - 4_576, u64::MAX),
			Some(MAX_MESSAGE_SIZE)
		);
		assert_eq!(
			registration_response_len(MAX_MESSAGE_SIZE - 4_576 + 1, u64::MAX),
			None
		);
	}

	#[test]
	fn frame_admission_binds_sender_and_preserves_every_other_field() {
		let ciphertext = [0xa5; 81];
		for sequence in [0, 1, u64::MAX] {
			for sender in [0, 1, u64::MAX] {
				let frame = admit_frame(sequence, sender, &ciphertext, sender).unwrap();
				assert_eq!(frame.sequence, sequence);
				assert_eq!(frame.sender, sender);
				assert!(core::ptr::eq(frame.ciphertext, ciphertext.as_slice()));
				assert!(
					admit_frame(sequence, sender, &ciphertext, sender.wrapping_add(1)).is_none()
				);
			}
		}
	}

	#[test]
	fn application_normalization_preserves_empty_and_borrowed_application() {
		let RegistrationApplication::Witness(witness) = normalize_registration_application(None)
		else {
			panic!("an omitted application must request the owned witness");
		};
		assert_eq!(witness, [0xff]);
		let empty = [];
		let RegistrationApplication::Provided(empty_view) =
			normalize_registration_application(Some(&empty))
		else {
			panic!("a provided empty application must remain provided");
		};
		assert!(empty_view.is_empty());
		let bytes = [0xff, 0x37, 0];
		let RegistrationApplication::Provided(view) =
			normalize_registration_application(Some(&bytes))
		else {
			panic!("a provided application must retain its borrowed view");
		};
		assert!(core::ptr::eq(view, bytes.as_slice()));
	}

	#[test]
	fn complete_message_gate_rejects_only_lengths_above_the_inclusive_limit() {
		for length in [0, 1, MAX_MESSAGE_SIZE - 1, MAX_MESSAGE_SIZE] {
			assert!(complete_message_size_admitted(length));
		}
		for length in [MAX_MESSAGE_SIZE + 1, usize::MAX] {
			assert!(!complete_message_size_admitted(length));
		}
	}
}
