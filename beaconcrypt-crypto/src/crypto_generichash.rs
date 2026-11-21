// SPDX-License-Identifier: 0BSD

use crate::{CryptoError, Result};
use alloc::vec::Vec;
use blake2::{
	Blake2bVarCore,
	digest::{
		Output,
		block_api::{Buffer, UpdateCore, VariableOutputCore},
	},
};

pub struct State {
	core: Blake2bVarCore,
	buffer: Buffer<Blake2bVarCore>,
	output_len: usize,
}

impl State {
	pub fn new(key: Option<&[u8]>, output_len: usize) -> Result<Self> {
		if !(16..=64).contains(&output_len)
			|| key.is_some_and(|key| !(16..=64).contains(&key.len()))
		{
			return Err(CryptoError);
		}
		let key = key.unwrap_or_default();
		let core = Blake2bVarCore::new_with_params(&[], &[], key.len(), output_len);
		let mut state = Self {
			core,
			buffer: Buffer::<Blake2bVarCore>::default(),
			output_len,
		};
		if !key.is_empty() {
			let mut block = zeroize::Zeroizing::new([0; 128]);
			block[..key.len()].copy_from_slice(key);
			state.update(&*block);
		}
		Ok(state)
	}

	pub fn update(&mut self, input: &[u8]) {
		let core = &mut self.core;
		self.buffer
			.digest_blocks(input, |blocks| core.update_blocks(blocks));
	}

	pub fn finalize(&mut self) -> Vec<u8> {
		let mut output = zeroize::Zeroizing::new(Output::<Blake2bVarCore>::default());
		self.core
			.finalize_variable_core(&mut self.buffer, &mut output);
		output[..self.output_len].to_vec()
	}
}

pub fn generichash(input: &[u8], key: Option<&[u8]>, output_len: usize) -> Result<Vec<u8>> {
	let mut state = State::new(key, output_len)?;
	state.update(input);
	Ok(state.finalize())
}
