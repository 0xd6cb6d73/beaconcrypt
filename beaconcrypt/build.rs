// SPDX-License-Identifier: 0BSD

fn main() {
	let crate_dir = std::path::PathBuf::from(
		std::env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR is set by Cargo"),
	);
	let schema_dir = crate_dir.join("src/schema");

	if cfg!(windows) {
		println!("cargo:rustc-link-lib=bcrypt");
	}

	capnpc::CompilerCommand::new()
		.src_prefix(&schema_dir)
		.import_path(&schema_dir)
		//.output_path("src/")
		.file(schema_dir.join("phase1.capnp"))
		.file(schema_dir.join("phase2.capnp"))
		.file(schema_dir.join("cryptoframe.capnp"))
		.run()
		.expect("schema compiler command");

	//let deps_to_parse = "libsodium_rs";
	//
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
		.exclude_item("memset_explicit")
		.exclude_item("SystemFunction036")
		.generate()
		.expect("Unable to generate bindings");
	let header_path = crate_dir.join("bindings.h");
	bindings.write_to_file(&header_path);
	let header = std::fs::read_to_string(&header_path).expect("read generated bindings");
	let header = deduplicate_opaque_typedef(&header, "beaconcrypt_Beacon");
	let header = deduplicate_opaque_typedef(&header, "beaconcrypt_Server");
	std::fs::write(header_path, header).expect("write generated bindings");
}

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
