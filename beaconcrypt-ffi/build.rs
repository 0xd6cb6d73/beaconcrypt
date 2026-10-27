// SPDX-License-Identifier: 0BSD

#[cfg(not(feature = "cbinds"))]
fn main() {}

#[cfg(feature = "cbinds")]
fn main() {
	let crate_dir = std::path::PathBuf::from(
		std::env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is set by Cargo"),
	);

	let bindings = cbindgen::Builder::new()
		.with_crate(&crate_dir)
		.with_language(cbindgen::Language::C)
		.with_cpp_compat(true)
		.with_include_guard("_BEACON_CRYPT_H_")
		.with_documentation(true)
		.with_std_types(true)
		.with_include_version(true)
		.with_autogen_warning("// Do not modify manually.")
		.with_item_prefix("beaconcrypt_")
		.with_std_types(true)
		.generate()
		.expect("Unable to generate bindings");
	let header_path = crate_dir.join("../beaconcrypt/bindings.h");
	let mut rendered = Vec::new();
	bindings.write(&mut rendered);
	let header = if rendered.is_empty() {
		// cbindgen's recursive-invocation guard produces no output and preserves the existing file.
		std::fs::read_to_string(&header_path).expect("read generated bindings")
	} else {
		String::from_utf8(rendered).expect("read generated bindings")
	};
	let header = deduplicate_opaque_typedef(&header, "beaconcrypt_Beacon");
	let header = deduplicate_opaque_typedef(&header, "beaconcrypt_Server");
	let existing = match std::fs::read(&header_path) {
		Ok(bytes) => Some(bytes),
		Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
		Err(error) => panic!("read generated bindings: {error}"),
	};
	if existing.as_deref() != Some(header.as_bytes()) {
		std::fs::write(header_path, header).expect("write generated bindings");
	}
}

#[cfg(feature = "cbinds")]
fn deduplicate_opaque_typedef(header: &str, name: &str) -> String {
	let declaration = format!("typedef struct {name} {name};");
	let mut header = header.to_owned();
	while header.match_indices(&declaration).count() > 1 {
		let first = header.find(&declaration).expect("duplicate declaration");
		let mut end = first + declaration.len();
		while header[end..].starts_with('\n') {
			end += 1;
		}
		header.replace_range(first..end, "");
	}
	header
}
