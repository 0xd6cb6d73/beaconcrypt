-- SPDX-License-Identifier: 0BSD
-- Generated from exact original EverCDDL control fragments; production Rust is unchanged.
import BeaconcryptCore.Refinement.RegistrationCodecSourceControl
import BeaconcryptCore.Refinement.RegistrationCodecArraySingleton
import BeaconcryptCore.RegistrationSchemaExtraction.Types

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096

namespace BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates
open RegistrationCodecSourceControl RegistrationCodecControlNormalization
universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {Environment Result : Type}

def validateinitkexFragment0 : Control :=
  (.branch "is_done5"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                                    crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                                let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                    v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    }", source := "\n                                                let str: &[u8] =\n                                                    match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                                let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(\n                                                        1952u64,\n                                                        len\n                                                    )", source := "\n                                                let lo_ok: bool =\n                                                    crate::cbordetveraux::u64_lte_sizet(\n                                                        1952u64,\n                                                        len\n                                                    );" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        1952u64\n                                                    )", source := "\n                                                let hi_ok: bool =\n                                                    crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        1952u64\n                                                    );" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validateinitkexFragment0_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment0 environment) =
      evaluate (controlTree semantics validateinitkexFragment0 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment1 : Control :=
  (.branch "is_done4"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                                crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                            let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                                {\n                                                    crate::cbordetver::cbor_det_view::String\n                                                    { payload: a, .. }\n                                                    => a,\n                                                    _ => panic!(\"Incomplete pattern matching\")\n                                                }", source := "\n                                            let str: &[u8] =\n                                                match _letpattern0\n                                                {\n                                                    crate::cbordetver::cbor_det_view::String\n                                                    { payload: a, .. }\n                                                    => a,\n                                                    _ => panic!(\"Incomplete pattern matching\")\n                                                };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                            let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(1249u64, len)", source := "\n                                            let lo_ok: bool =\n                                                crate::cbordetveraux::u64_lte_sizet(1249u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 1249u64)", source := "\n                                            let hi_ok: bool =\n                                                crate::cbordetveraux::sizet_lte_u64(len, 1249u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validateinitkexFragment1_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment1 environment) =
      evaluate (controlTree semantics validateinitkexFragment1 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment2 : Control :=
  (.branch "is_done3"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            }", source := "\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                        let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(98u64, len)", source := "\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(98u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 98u64)", source := "\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 98u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validateinitkexFragment2_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment2 environment) =
      evaluate (controlTree semantics validateinitkexFragment2 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment3 : Control :=
  (.branch "is_done2"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        }", source := "\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                    let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(98u64, len)", source := "\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(98u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 98u64)", source := "\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 98u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validateinitkexFragment3_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment3 environment) =
      evaluate (controlTree semantics validateinitkexFragment3 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment4 : Control :=
  (.branch "is_done1"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    }", source := "\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(33u64, len)", source := "\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 33u64)", source := "\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validateinitkexFragment4_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment4 environment) =
      evaluate (controlTree semantics validateinitkexFragment4 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment5 : Control :=
  .expression "mt == crate::cbordetveraux::cbor_major_type_uint64"

theorem validateinitkexFragment5_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment5 environment) =
      evaluate (controlTree semantics validateinitkexFragment5 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment6 : Control :=
  (.branch "is_done0"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.statement { binding := "is_uint", rustType := "bool", expression := "mt == crate::cbordetveraux::cbor_major_type_uint64", source := "\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;" }
  ((.branch "is_uint"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "i2", rustType := "u64", expression := "match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                }", source := "\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };" }
  (.expression "i2 == 0u64")))))))
  (.done false))))))))))

theorem validateinitkexFragment6_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment6 environment) =
      evaluate (controlTree semantics validateinitkexFragment6 environment) >>= next :=
  fragment_preserved _ _ _ _

def validateinitkexFragment7 : Control :=
  (.branch "test1"
  ((.statement { binding := "i10", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =\n                    (&pi)[0];" }
  ((.statement { binding := "is_done0", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i10)", source := "\n                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);" }
  ((.statement { binding := "test11", rustType := "bool", expression := "if is_done0\n                    { false }\n                    else\n                    {\n                        let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;\n                        if is_uint\n                        {\n                            let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };\n                            i2 == 0u64\n                        }\n                        else\n                        { false }\n                    }", source := "\n                let test11: bool =\n                    if is_done0\n                    { false }\n                    else\n                    {\n                        let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;\n                        if is_uint\n                        {\n                            let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };\n                            i2 == 0u64\n                        }\n                        else\n                        { false }\n                    };" }
  ((.branch "test11"
  ((.statement { binding := "i11", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =\n                        (&pi)[0];" }
  ((.statement { binding := "is_done1", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i11)", source := "\n                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);" }
  ((.statement { binding := "test12", rustType := "bool", expression := "if is_done1\n                        { false }\n                        else\n                        {\n                            let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                            if mt == 2u8\n                            {\n                                let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };\n                                let len: usize = str.len();\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);\n                                lo_ok && hi_ok\n                            }\n                            else\n                            { false }\n                        }", source := "\n                    let test12: bool =\n                        if is_done1\n                        { false }\n                        else\n                        {\n                            let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                            if mt == 2u8\n                            {\n                                let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };\n                                let len: usize = str.len();\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);\n                                lo_ok && hi_ok\n                            }\n                            else\n                            { false }\n                        };" }
  ((.branch "test12"
  ((.statement { binding := "i12", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                        i12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                        =\n                            (&pi)[0];" }
  ((.statement { binding := "is_done2", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i12)", source := "\n                        let is_done2: bool =\n                            crate::cbordetver::cbor_det_array_iterator_is_empty(i12);" }
  ((.statement { binding := "test13", rustType := "bool", expression := "if is_done2\n                            { false }\n                            else\n                            {\n                                let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                if mt == 2u8\n                                {\n                                    let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };\n                                    let len: usize = str.len();\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(98u64, len);\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 98u64);\n                                    lo_ok && hi_ok\n                                }\n                                else\n                                { false }\n                            }", source := "\n                        let test13: bool =\n                            if is_done2\n                            { false }\n                            else\n                            {\n                                let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                if mt == 2u8\n                                {\n                                    let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };\n                                    let len: usize = str.len();\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(98u64, len);\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 98u64);\n                                    lo_ok && hi_ok\n                                }\n                                else\n                                { false }\n                            };" }
  ((.branch "test13"
  ((.statement { binding := "i13", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                            i13:\n                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                            =\n                                (&pi)[0];" }
  ((.statement { binding := "is_done3", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i13)", source := "\n                            let is_done3: bool =\n                                crate::cbordetver::cbor_det_array_iterator_is_empty(i13);" }
  ((.statement { binding := "test14", rustType := "bool", expression := "if is_done3\n                                { false }\n                                else\n                                {\n                                    let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                    if mt == 2u8\n                                    {\n                                        let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };\n                                        let len: usize = str.len();\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(98u64, len);\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 98u64);\n                                        lo_ok && hi_ok\n                                    }\n                                    else\n                                    { false }\n                                }", source := "\n                            let test14: bool =\n                                if is_done3\n                                { false }\n                                else\n                                {\n                                    let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                    if mt == 2u8\n                                    {\n                                        let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };\n                                        let len: usize = str.len();\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(98u64, len);\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 98u64);\n                                        lo_ok && hi_ok\n                                    }\n                                    else\n                                    { false }\n                                };" }
  ((.branch "test14"
  ((.statement { binding := "i14", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                i14:\n                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                =\n                                    (&pi)[0];" }
  ((.statement { binding := "is_done4", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i14)", source := "\n                                let is_done4: bool =\n                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i14);" }
  ((.statement { binding := "test15", rustType := "bool", expression := "if is_done4\n                                    { false }\n                                    else\n                                    {\n                                        let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                        if mt == 2u8\n                                        {\n                                            let v10: crate::cbordetver::cbor_det_view =\n                                                crate::cbordetver::cbor_det_destruct(c1);\n                                            let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                v10;\n                                            let str: &[u8] =\n                                                match _letpattern0\n                                                {\n                                                    crate::cbordetver::cbor_det_view::String\n                                                    { payload: a, .. }\n                                                    => a,\n                                                    _ => panic!(\"Incomplete pattern matching\")\n                                                };\n                                            let len: usize = str.len();\n                                            let lo_ok: bool =\n                                                crate::cbordetveraux::u64_lte_sizet(1249u64, len);\n                                            let hi_ok: bool =\n                                                crate::cbordetveraux::sizet_lte_u64(len, 1249u64);\n                                            lo_ok && hi_ok\n                                        }\n                                        else\n                                        { false }\n                                    }", source := "\n                                let test15: bool =\n                                    if is_done4\n                                    { false }\n                                    else\n                                    {\n                                        let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                        if mt == 2u8\n                                        {\n                                            let v10: crate::cbordetver::cbor_det_view =\n                                                crate::cbordetver::cbor_det_destruct(c1);\n                                            let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                v10;\n                                            let str: &[u8] =\n                                                match _letpattern0\n                                                {\n                                                    crate::cbordetver::cbor_det_view::String\n                                                    { payload: a, .. }\n                                                    => a,\n                                                    _ => panic!(\"Incomplete pattern matching\")\n                                                };\n                                            let len: usize = str.len();\n                                            let lo_ok: bool =\n                                                crate::cbordetveraux::u64_lte_sizet(1249u64, len);\n                                            let hi_ok: bool =\n                                                crate::cbordetveraux::sizet_lte_u64(len, 1249u64);\n                                            lo_ok && hi_ok\n                                        }\n                                        else\n                                        { false }\n                                    };" }
  ((.branch "test15"
  ((.statement { binding := "i15", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                    i15:\n                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                    =\n                                        (&pi)[0];" }
  ((.statement { binding := "is_done5", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i15)", source := "\n                                    let is_done5: bool =\n                                        crate::cbordetver::cbor_det_array_iterator_is_empty(i15);" }
  ((.statement { binding := "test16", rustType := "bool", expression := "if is_done5\n                                        { false }\n                                        else\n                                        {\n                                            let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                            if mt == 2u8\n                                            {\n                                                let v10: crate::cbordetver::cbor_det_view =\n                                                    crate::cbordetver::cbor_det_destruct(c1);\n                                                let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                    v10;\n                                                let str: &[u8] =\n                                                    match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    };\n                                                let len: usize = str.len();\n                                                let lo_ok: bool =\n                                                    crate::cbordetveraux::u64_lte_sizet(\n                                                        1952u64,\n                                                        len\n                                                    );\n                                                let hi_ok: bool =\n                                                    crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        1952u64\n                                                    );\n                                                lo_ok && hi_ok\n                                            }\n                                            else\n                                            { false }\n                                        }", source := "\n                                    let test16: bool =\n                                        if is_done5\n                                        { false }\n                                        else\n                                        {\n                                            let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                            if mt == 2u8\n                                            {\n                                                let v10: crate::cbordetver::cbor_det_view =\n                                                    crate::cbordetver::cbor_det_destruct(c1);\n                                                let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                    v10;\n                                                let str: &[u8] =\n                                                    match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    };\n                                                let len: usize = str.len();\n                                                let lo_ok: bool =\n                                                    crate::cbordetveraux::u64_lte_sizet(\n                                                        1952u64,\n                                                        len\n                                                    );\n                                                let hi_ok: bool =\n                                                    crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        1952u64\n                                                    );\n                                                lo_ok && hi_ok\n                                            }\n                                            else\n                                            { false }\n                                        };" }
  ((.branch "test16"
  ((.statement { binding := "i16", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                        i16:\n                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                        =\n                                            (&pi)[0];" }
  ((.statement { binding := "is_done6", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i16)", source := "\n                                        let is_done6: bool =\n                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i16);" }
  ((.branch "is_done6"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                                    crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                                let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                    v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    }", source := "\n                                                let str: &[u8] =\n                                                    match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                                let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(\n                                                        3309u64,\n                                                        len\n                                                    )", source := "\n                                                let lo_ok: bool =\n                                                    crate::cbordetveraux::u64_lte_sizet(\n                                                        3309u64,\n                                                        len\n                                                    );" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        3309u64\n                                                    )", source := "\n                                                let hi_ok: bool =\n                                                    crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        3309u64\n                                                    );" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false)))))))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false))

theorem validateinitkexFragment7_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validateinitkexFragment7 environment) =
      evaluate (controlTree semantics validateinitkexFragment7 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment0 : Control :=
  (.branch "is_done5"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  (.expression "validate_uint(c1)"))))

theorem validatekexresponseFragment0_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment0 environment) =
      evaluate (controlTree semantics validatekexresponseFragment0 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment1 : Control :=
  (.branch "is_done4"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  (.expression "validate_bstr(c1)"))))

theorem validatekexresponseFragment1_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment1 environment) =
      evaluate (controlTree semantics validatekexresponseFragment1 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment2 : Control :=
  (.branch "is_done3"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            }", source := "\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                        let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(1088u64, len)", source := "\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(1088u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 1088u64)", source := "\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 1088u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validatekexresponseFragment2_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment2 environment) =
      evaluate (controlTree semantics validatekexresponseFragment2 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment3 : Control :=
  (.branch "is_done2"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        }", source := "\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                    let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(32u64, len)", source := "\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(32u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 32u64)", source := "\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 32u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validatekexresponseFragment3_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment3 environment) =
      evaluate (controlTree semantics validatekexresponseFragment3 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment4 : Control :=
  (.branch "is_done1"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    }", source := "\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(32u64, len)", source := "\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(len, 32u64)", source := "\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false))))))))

theorem validatekexresponseFragment4_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment4 environment) =
      evaluate (controlTree semantics validatekexresponseFragment4 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment5 : Control :=
  .expression "mt == crate::cbordetveraux::cbor_major_type_uint64"

theorem validatekexresponseFragment5_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment5 environment) =
      evaluate (controlTree semantics validatekexresponseFragment5 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment6 : Control :=
  (.branch "is_done0"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.statement { binding := "is_uint", rustType := "bool", expression := "mt == crate::cbordetveraux::cbor_major_type_uint64", source := "\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;" }
  ((.branch "is_uint"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;" }
  ((.statement { binding := "i2", rustType := "u64", expression := "match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                }", source := "\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };" }
  (.expression "i2 == 1u64")))))))
  (.done false))))))))))

theorem validatekexresponseFragment6_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment6 environment) =
      evaluate (controlTree semantics validatekexresponseFragment6 environment) >>= next :=
  fragment_preserved _ _ _ _

def validatekexresponseFragment7 : Control :=
  (.branch "test1"
  ((.statement { binding := "i10", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =\n                    (&pi)[0];" }
  ((.statement { binding := "is_done0", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i10)", source := "\n                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);" }
  ((.statement { binding := "test11", rustType := "bool", expression := "if is_done0\n                    { false }\n                    else\n                    {\n                        let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;\n                        if is_uint\n                        {\n                            let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };\n                            i2 == 1u64\n                        }\n                        else\n                        { false }\n                    }", source := "\n                let test11: bool =\n                    if is_done0\n                    { false }\n                    else\n                    {\n                        let c1: crate::cbordetveraux::cbor_raw =\n                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;\n                        if is_uint\n                        {\n                            let v10: crate::cbordetver::cbor_det_view =\n                                crate::cbordetver::cbor_det_destruct(c1);\n                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                            let i2: u64 =\n                                match _letpattern0\n                                {\n                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>\n                                      res,\n                                    _ => panic!(\"Incomplete pattern matching\")\n                                };\n                            i2 == 1u64\n                        }\n                        else\n                        { false }\n                    };" }
  ((.branch "test11"
  ((.statement { binding := "i11", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =\n                        (&pi)[0];" }
  ((.statement { binding := "is_done1", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i11)", source := "\n                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);" }
  ((.statement { binding := "test12", rustType := "bool", expression := "if is_done1\n                        { false }\n                        else\n                        {\n                            let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                            if mt == 2u8\n                            {\n                                let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };\n                                let len: usize = str.len();\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);\n                                lo_ok && hi_ok\n                            }\n                            else\n                            { false }\n                        }", source := "\n                    let test12: bool =\n                        if is_done1\n                        { false }\n                        else\n                        {\n                            let c1: crate::cbordetveraux::cbor_raw =\n                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                            if mt == 2u8\n                            {\n                                let v10: crate::cbordetver::cbor_det_view =\n                                    crate::cbordetver::cbor_det_destruct(c1);\n                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                let str: &[u8] =\n                                    match _letpattern0\n                                    {\n                                        crate::cbordetver::cbor_det_view::String\n                                        { payload: a, .. }\n                                        => a,\n                                        _ => panic!(\"Incomplete pattern matching\")\n                                    };\n                                let len: usize = str.len();\n                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);\n                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);\n                                lo_ok && hi_ok\n                            }\n                            else\n                            { false }\n                        };" }
  ((.branch "test12"
  ((.statement { binding := "i12", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                        i12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                        =\n                            (&pi)[0];" }
  ((.statement { binding := "is_done2", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i12)", source := "\n                        let is_done2: bool =\n                            crate::cbordetver::cbor_det_array_iterator_is_empty(i12);" }
  ((.statement { binding := "test13", rustType := "bool", expression := "if is_done2\n                            { false }\n                            else\n                            {\n                                let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                if mt == 2u8\n                                {\n                                    let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };\n                                    let len: usize = str.len();\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(32u64, len);\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 32u64);\n                                    lo_ok && hi_ok\n                                }\n                                else\n                                { false }\n                            }", source := "\n                        let test13: bool =\n                            if is_done2\n                            { false }\n                            else\n                            {\n                                let c1: crate::cbordetveraux::cbor_raw =\n                                    { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                if mt == 2u8\n                                {\n                                    let v10: crate::cbordetver::cbor_det_view =\n                                        crate::cbordetver::cbor_det_destruct(c1);\n                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                    let str: &[u8] =\n                                        match _letpattern0\n                                        {\n                                            crate::cbordetver::cbor_det_view::String\n                                            { payload: a, .. }\n                                            => a,\n                                            _ => panic!(\"Incomplete pattern matching\")\n                                        };\n                                    let len: usize = str.len();\n                                    let lo_ok: bool =\n                                        crate::cbordetveraux::u64_lte_sizet(32u64, len);\n                                    let hi_ok: bool =\n                                        crate::cbordetveraux::sizet_lte_u64(len, 32u64);\n                                    lo_ok && hi_ok\n                                }\n                                else\n                                { false }\n                            };" }
  ((.branch "test13"
  ((.statement { binding := "i13", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                            i13:\n                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                            =\n                                (&pi)[0];" }
  ((.statement { binding := "is_done3", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i13)", source := "\n                            let is_done3: bool =\n                                crate::cbordetver::cbor_det_array_iterator_is_empty(i13);" }
  ((.statement { binding := "test14", rustType := "bool", expression := "if is_done3\n                                { false }\n                                else\n                                {\n                                    let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                    if mt == 2u8\n                                    {\n                                        let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };\n                                        let len: usize = str.len();\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(1088u64, len);\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 1088u64);\n                                        lo_ok && hi_ok\n                                    }\n                                    else\n                                    { false }\n                                }", source := "\n                            let test14: bool =\n                                if is_done3\n                                { false }\n                                else\n                                {\n                                    let c1: crate::cbordetveraux::cbor_raw =\n                                        { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);\n                                    if mt == 2u8\n                                    {\n                                        let v10: crate::cbordetver::cbor_det_view =\n                                            crate::cbordetver::cbor_det_destruct(c1);\n                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;\n                                        let str: &[u8] =\n                                            match _letpattern0\n                                            {\n                                                crate::cbordetver::cbor_det_view::String\n                                                { payload: a, .. }\n                                                => a,\n                                                _ => panic!(\"Incomplete pattern matching\")\n                                            };\n                                        let len: usize = str.len();\n                                        let lo_ok: bool =\n                                            crate::cbordetveraux::u64_lte_sizet(1088u64, len);\n                                        let hi_ok: bool =\n                                            crate::cbordetveraux::sizet_lte_u64(len, 1088u64);\n                                        lo_ok && hi_ok\n                                    }\n                                    else\n                                    { false }\n                                };" }
  ((.branch "test14"
  ((.statement { binding := "i14", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                i14:\n                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                =\n                                    (&pi)[0];" }
  ((.statement { binding := "is_done4", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i14)", source := "\n                                let is_done4: bool =\n                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i14);" }
  ((.statement { binding := "test15", rustType := "bool", expression := "if is_done4\n                                    { false }\n                                    else\n                                    {\n                                        let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                        validate_bstr(c1)\n                                    }", source := "\n                                let test15: bool =\n                                    if is_done4\n                                    { false }\n                                    else\n                                    {\n                                        let c1: crate::cbordetveraux::cbor_raw =\n                                            { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                        validate_bstr(c1)\n                                    };" }
  ((.branch "test15"
  ((.statement { binding := "i15", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                    i15:\n                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                    =\n                                        (&pi)[0];" }
  ((.statement { binding := "is_done5", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i15)", source := "\n                                    let is_done5: bool =\n                                        crate::cbordetver::cbor_det_array_iterator_is_empty(i15);" }
  ((.statement { binding := "test16", rustType := "bool", expression := "if is_done5\n                                        { false }\n                                        else\n                                        {\n                                            let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                            validate_uint(c1)\n                                        }", source := "\n                                    let test16: bool =\n                                        if is_done5\n                                        { false }\n                                        else\n                                        {\n                                            let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };\n                                            validate_uint(c1)\n                                        };" }
  ((.branch "test16"
  ((.statement { binding := "i16", rustType := "crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw", expression := "(&pi)[0]", source := "let\n                                        i16:\n                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw\n                                        =\n                                            (&pi)[0];" }
  ((.statement { binding := "is_done6", rustType := "bool", expression := "crate::cbordetver::cbor_det_array_iterator_is_empty(i16)", source := "\n                                        let is_done6: bool =\n                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i16);" }
  ((.branch "is_done6"
  (.done false)
  ((.statement { binding := "c1", rustType := "crate::cbordetveraux::cbor_raw", expression := "{ let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value }", source := "let c1: crate::cbordetveraux::cbor_raw =\n                                                { let (extraction_value, extraction_after) = crate::extraction_iterator_next_value(pi[0]); pi[0] = extraction_after; extraction_value };" }
  ((.statement { binding := "mt", rustType := "u8", expression := "crate::cbordetver::cbor_det_major_type(c1)", source := "\n                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);" }
  ((.branch "mt == 2u8"
  ((.statement { binding := "v10", rustType := "crate::cbordetver::cbor_det_view", expression := "crate::cbordetver::cbor_det_destruct(c1)", source := "let v10: crate::cbordetver::cbor_det_view =\n                                                    crate::cbordetver::cbor_det_destruct(c1);" }
  ((.statement { binding := "_letpattern0", rustType := "crate::cbordetver::cbor_det_view", expression := "v10", source := "\n                                                let _letpattern0: crate::cbordetver::cbor_det_view =\n                                                    v10;" }
  ((.statement { binding := "str", rustType := "&[u8]", expression := "match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    }", source := "\n                                                let str: &[u8] =\n                                                    match _letpattern0\n                                                    {\n                                                        crate::cbordetver::cbor_det_view::String\n                                                        { payload: a, .. }\n                                                        => a,\n                                                        _ => panic!(\"Incomplete pattern matching\")\n                                                    };" }
  ((.statement { binding := "len", rustType := "usize", expression := "str.len()", source := "\n                                                let len: usize = str.len();" }
  ((.statement { binding := "lo_ok", rustType := "bool", expression := "crate::cbordetveraux::u64_lte_sizet(\n                                                        3309u64,\n                                                        len\n                                                    )", source := "\n                                                let lo_ok: bool =\n                                                    crate::cbordetveraux::u64_lte_sizet(\n                                                        3309u64,\n                                                        len\n                                                    );" }
  ((.statement { binding := "hi_ok", rustType := "bool", expression := "crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        3309u64\n                                                    )", source := "\n                                                let hi_ok: bool =\n                                                    crate::cbordetveraux::sizet_lte_u64(\n                                                        len,\n                                                        3309u64\n                                                    );" }
  (.expression "lo_ok && hi_ok")))))))))))))
  (.done false)))))))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false)))))))))
  (.done false))

theorem validatekexresponseFragment7_preserves (semantics : Semantics m Environment)
    (environment : Environment) (next : Bool × Environment → m Result) :
    cps next (controlTree semantics validatekexresponseFragment7 environment) =
      evaluate (controlTree semantics validatekexresponseFragment7 environment) >>= next :=
  fragment_preserved _ _ _ _

abbrev Iterator := beaconcrypt_parse.cbordetveraux.bcExtractedToken63626f725f7261775f6974657261746f725f5f43424f525f50756c73655f5261775f547970655f63626f725f726177

theorem extractionparseinitkexcheck0State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck1State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck2State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck3State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck4State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck5State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparseinitkexcheck6State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck0State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck1State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck2State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck3State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck4State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck5State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

theorem extractionparsekexresponsecheck6State (work : RegistrationCodecArraySingleton.Single Iterator →
    m (Bool × RegistrationCodecArraySingleton.Single Iterator))
    (before : RegistrationCodecArraySingleton.Single Iterator)
    (next : RegistrationCodecArraySingleton.Single Iterator → m Result) :
    (RegistrationCodecArraySingleton.restore (RegistrationCodecArraySingleton.scalarize work) before >>=
      fun result => next result.2) = (work before >>= fun result => next result.2) :=
  RegistrationCodecArraySingleton.ignored_result_preserved work before next

end BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment0_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment0_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment1_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment1_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment2_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment2_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment3_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment3_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment4_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment4_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment5_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment5_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment6_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment6_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment7_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validateinitkexFragment7_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment0_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment0_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment1_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment1_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment2_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment2_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment3_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment3_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment4_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment4_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment5_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment5_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment6_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment6_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment7_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.validatekexresponseFragment7_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck0State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck0State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck1State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck1State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck2State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck2State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck3State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck3State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck4State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck4State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck5State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck5State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck6State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparseinitkexcheck6State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck0State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck0State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck1State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck1State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck2State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck2State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck3State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck3State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck4State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck4State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck5State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck5State

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck6State' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecSourceCertificates.extractionparsekexresponsecheck6State
