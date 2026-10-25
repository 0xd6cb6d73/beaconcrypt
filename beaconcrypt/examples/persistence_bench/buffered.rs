// SPDX-License-Identifier: 0BSD

//! A callback-local optimistic read/write set shared by both benchmark SQL adapters.

use std::collections::BTreeMap;

use beaconcrypt::{RowError, RowTransaction};

use super::database::Counters;

pub type ReadSet = BTreeMap<Vec<u8>, Option<Vec<u8>>>;
pub type WriteSet = BTreeMap<Vec<u8>, Vec<u8>>;

pub struct Buffered<'a, F> {
	pub reads: ReadSet,
	pub writes: WriteSet,
	pub failure: Option<RowError>,
	pub fetch: F,
	pub counts: &'a Counters,
}

impl<'a, F> Buffered<'a, F>
where
	F: FnMut(&[u8]) -> Result<Option<Vec<u8>>, RowError>,
{
	pub fn new(fetch: F, counts: &'a Counters) -> Self {
		Self {
			reads: BTreeMap::new(),
			writes: BTreeMap::new(),
			failure: None,
			fetch,
			counts,
		}
	}

	fn ready(&self) -> Result<(), RowError> {
		match &self.failure {
			Some(error) => Err(error.clone()),
			None => Ok(()),
		}
	}

	fn conflict(&mut self) -> Result<(), RowError> {
		self.failure = Some(RowError::Conflict);
		Err(RowError::Conflict)
	}
}

impl<F> RowTransaction for Buffered<'_, F>
where
	F: FnMut(&[u8]) -> Result<Option<Vec<u8>>, RowError>,
{
	fn load(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>, RowError> {
		self.counts.loads.set(self.counts.loads.get() + 1);
		self.ready()?;
		if let Some(value) = self.writes.get(key) {
			return Ok(Some(value.clone()));
		}
		if let Some(value) = self.reads.get(key) {
			return Ok(value.clone());
		}
		let value = match (self.fetch)(key) {
			Ok(value) => value,
			Err(error) => {
				self.failure = Some(error.clone());
				return Err(error);
			}
		};
		self.reads.insert(key.to_vec(), value.clone());
		Ok(value)
	}

	fn expect(&mut self, key: &[u8], expected: Option<&[u8]>) -> Result<(), RowError> {
		self.counts.expects.set(self.counts.expects.get() + 1);
		self.counts
			.value_bytes_expected
			.set(self.counts.value_bytes_expected.get() + expected.map_or(0, |v| v.len() as u64));
		self.ready()?;
		if let Some(value) = self.writes.get(key) {
			return if Some(value.as_slice()) == expected {
				Ok(())
			} else {
				self.conflict()
			};
		}
		if let Some(value) = self.reads.get(key) {
			return if value.as_deref() == expected {
				Ok(())
			} else {
				self.conflict()
			};
		}
		self.reads
			.insert(key.to_vec(), expected.map(<[u8]>::to_vec));
		Ok(())
	}

	fn store(&mut self, key: &[u8], value: &[u8]) -> Result<(), RowError> {
		self.counts.stores.set(self.counts.stores.get() + 1);
		self.ready()?;
		self.writes.insert(key.to_vec(), value.to_vec());
		Ok(())
	}
}
