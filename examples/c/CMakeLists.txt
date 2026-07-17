cmake_minimum_required(VERSION 3.20)

project(beaconcrypt_c_example C)

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS OFF)

get_filename_component(BEACONCRYPT_REPO_ROOT "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)

find_program(CARGO_EXECUTABLE cargo REQUIRED)

option(BEACONCRYPT_CARGO_RELEASE "Build beaconcrypt with Cargo's release profile" OFF)

set(BEACONCRYPT_CARGO_PROFILE debug)
set(BEACONCRYPT_CARGO_ARGS build --features cbinds)
if(BEACONCRYPT_CARGO_RELEASE)
	set(BEACONCRYPT_CARGO_PROFILE release)
	list(APPEND BEACONCRYPT_CARGO_ARGS --release)
endif()

set(BEACONCRYPT_CARGO_TARGET_DIR "${BEACONCRYPT_REPO_ROOT}/target/${BEACONCRYPT_CARGO_PROFILE}")

if(WIN32)
	set(BEACONCRYPT_SHARED_LIBRARY "${BEACONCRYPT_CARGO_TARGET_DIR}/beaconcrypt.dll")
	if(MSVC)
		set(BEACONCRYPT_IMPORT_LIBRARY "${BEACONCRYPT_CARGO_TARGET_DIR}/beaconcrypt.dll.lib")
	else()
		set(BEACONCRYPT_IMPORT_LIBRARY "${BEACONCRYPT_CARGO_TARGET_DIR}/libbeaconcrypt.dll.a")
	endif()
elseif(APPLE)
	set(BEACONCRYPT_SHARED_LIBRARY "${BEACONCRYPT_CARGO_TARGET_DIR}/libbeaconcrypt.dylib")
	set(BEACONCRYPT_IMPORT_LIBRARY "${BEACONCRYPT_SHARED_LIBRARY}")
else()
	set(BEACONCRYPT_SHARED_LIBRARY "${BEACONCRYPT_CARGO_TARGET_DIR}/libbeaconcrypt.so")
	set(BEACONCRYPT_IMPORT_LIBRARY "${BEACONCRYPT_SHARED_LIBRARY}")
endif()

add_custom_target(beaconcrypt_rust
	COMMAND "${CARGO_EXECUTABLE}" ${BEACONCRYPT_CARGO_ARGS}
	WORKING_DIRECTORY "${BEACONCRYPT_REPO_ROOT}"
	BYPRODUCTS "${BEACONCRYPT_SHARED_LIBRARY}" "${BEACONCRYPT_IMPORT_LIBRARY}"
	VERBATIM
)

add_library(beaconcrypt_shared SHARED IMPORTED GLOBAL)
set_target_properties(beaconcrypt_shared PROPERTIES
	IMPORTED_LOCATION "${BEACONCRYPT_SHARED_LIBRARY}"
)
if(WIN32)
	set_target_properties(beaconcrypt_shared PROPERTIES
		IMPORTED_IMPLIB "${BEACONCRYPT_IMPORT_LIBRARY}"
	)
endif()

add_executable(beaconcrypt_c_example main.c)
add_dependencies(beaconcrypt_c_example beaconcrypt_rust)
target_include_directories(beaconcrypt_c_example PRIVATE "${BEACONCRYPT_REPO_ROOT}")
target_link_libraries(beaconcrypt_c_example PRIVATE beaconcrypt_shared)

if(WIN32)
	target_link_libraries(beaconcrypt_c_example PRIVATE bcrypt)
endif()

add_custom_command(TARGET beaconcrypt_c_example POST_BUILD
	COMMAND "${CMAKE_COMMAND}" -E copy_if_different
		"${BEACONCRYPT_SHARED_LIBRARY}"
		"$<TARGET_FILE_DIR:beaconcrypt_c_example>"
	VERBATIM
)
