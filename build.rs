// SPDX-License-Identifier: 0BSD

fn main() {
	if cfg!(windows) {
		println!("cargo:rustc-link-lib=bcrypt");
	}

	capnpc::CompilerCommand::new()
		.src_prefix("src/schema")
		.import_path("src/schema")
		//.output_path("src/")
		.file("src/schema/phase1.capnp")
		.file("src/schema/phase2.capnp")
		.file("src/schema/cryptoframe.capnp")
		.file("src/schema/protogram.capnp")
		.run()
		.expect("schema compiler command");

	let crate_dir = ".";
	//let deps_to_parse = "libsodium_rs";
	//
	cbindgen::Builder::new()
		.with_crate(crate_dir)
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
		.expect("Unable to generate bindings")
		.write_to_file("bindings.h");
}
