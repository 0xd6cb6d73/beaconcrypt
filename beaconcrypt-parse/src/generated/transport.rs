#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn validate_bool(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    let test: bool = mt == crate::cbordetveraux::cbor_major_type_simple_value;
    let test0: bool =
        if test
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let v10: u8 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v10 == crate::cbordetveraux::cddl_simple_value_false
        }
        else
        { false };
    if test0
    { true }
    else
    {
        let mt0: u8 = crate::cbordetver::cbor_det_major_type(c);
        let test1: bool = mt0 == crate::cbordetveraux::cbor_major_type_simple_value;
        if test1
        {
            let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
            let _letpattern: crate::cbordetver::cbor_det_view = v1;
            let v10: u8 =
                match _letpattern
                {
                    crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            v10 == crate::cbordetveraux::cddl_simple_value_true
        }
        else
        { false }
    }
}

pub type evercddl_bool = bool;

pub fn uu___is_Mkevercddl_bool0(projectee: bool) -> bool
{
    crate::lowstar::ignore::ignore::<bool>(projectee);
    true
}

fn evercddl_bool_right(x1: bool) -> bool { x1 }

fn evercddl_bool_left(x3: bool) -> bool { x3 }

/**
Parser for evercddl_bool
*/
pub fn
parse_bool(c: crate::cbordetveraux::cbor_raw) ->
    bool
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let w: u8 =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::SimpleValue { _0: res } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res: bool = w == crate::cbordetveraux::simple_value_true;
    let res1: bool = res;
    evercddl_bool_right(res1)
}

/**
Serializer for evercddl_bool
*/
pub fn
serialize_bool(c: bool, out: &mut [u8]) ->
    usize
{
    let c·: bool = evercddl_bool_left(c);
    if c·
    {
        if
        crate::cbordetveraux::simple_value_true
        <=
        crate::cbordetveraux::max_simple_value_additional_info
        ||
        crate::cbordetveraux::min_simple_value_long_argument
        <=
        crate::cbordetveraux::simple_value_true
        {
            let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
                crate::cbordetver::cbor_det_mk_simple_value(crate::cbordetveraux::simple_value_true);
            let x: crate::cbordetveraux::cbor_raw =
                match _letpattern
                {
                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
                    _ => panic!("Incomplete pattern matching")
                };
            let ser: crate::cbordetver::option__size_t =
                crate::cbordetver::cbor_det_serialize(x, out);
            match ser
            {
                crate::cbordetver::option__size_t::None => 0usize,
                crate::cbordetver::option__size_t::Some { v: sz } => sz,
                _ => panic!("Incomplete pattern matching")
            }
        }
        else
        { 0usize }
    }
    else if
    crate::cbordetveraux::simple_value_false
    <=
    crate::cbordetveraux::max_simple_value_additional_info
    ||
    crate::cbordetveraux::min_simple_value_long_argument
    <=
    crate::cbordetveraux::simple_value_false
    {
        let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            crate::cbordetver::cbor_det_mk_simple_value(crate::cbordetveraux::simple_value_false);
        let x: crate::cbordetveraux::cbor_raw =
            match _letpattern
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: res } => res,
                _ => panic!("Incomplete pattern matching")
            };
        let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
        match ser
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: sz } => sz,
            _ => panic!("Incomplete pattern matching")
        }
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (bool, &'a [u8]) }
}

pub fn validate_and_parse_bool <'a>(s: &'a [u8]) ->
    option__·Transport_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_bool(rl);
              if test
              {
                  let x: bool = parse_bool(rl);
                  option__·Transport_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_evercddl_bool···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_everparsenomatch(c: crate::cbordetveraux::cbor_raw) -> bool
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    false
}

#[derive(PartialEq, Clone, Copy)] pub enum everparsenomatch { Mkeverparsenomatch0 }

pub fn uu___is_Mkeverparsenomatch0(projectee: everparsenomatch) -> bool
{
    crate::lowstar::ignore::ignore::<everparsenomatch>(projectee);
    true
}

fn everparsenomatch_right() -> everparsenomatch { everparsenomatch::Mkeverparsenomatch0 }

/**
Parser for everparsenomatch
*/
pub fn
parse_everparsenomatch(c: crate::cbordetveraux::cbor_raw) ->
    everparsenomatch
{
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(c);
    everparsenomatch_right()
}

/**
Serializer for everparsenomatch
*/
pub fn
serialize_everparsenomatch(c: everparsenomatch, out: &[u8]) ->
    usize
{
    crate::lowstar::ignore::ignore::<everparsenomatch>(c);
    crate::lowstar::ignore::ignore::<&[u8]>(out);
    0usize
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (everparsenomatch, &'a [u8]) }
}

pub fn validate_and_parse_everparsenomatch <'a>(s: &'a [u8]) ->
    option__·Transport_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_everparsenomatch(rl);
              if test
              {
                  let x: everparsenomatch = parse_everparsenomatch(rl);
                  option__·Transport_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_everparsenomatch···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_bstr(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_byte_string
}

pub type bstr_ugly <'a> = &'a [u8];

pub type bstr <'a> = &'a [u8];

pub fn uu___is_Mkbstr0(projectee: &[u8]) -> bool
{
    crate::lowstar::ignore::ignore::<&[u8]>(projectee);
    true
}

fn bstr_right <'a>(x1: &'a [u8]) -> &'a [u8] { x1 }

fn bstr_left <'a>(x3: &'a [u8]) -> &'a [u8] { x3 }

/**
Parser for bstr
*/
pub fn
parse_bstr
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    &'a [u8]
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let s: &[u8] =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: &[u8] = s;
    bstr_right(res1)
}

/**
Serializer for bstr
*/
pub fn
serialize_bstr(c: &[u8], out: &mut [u8]) ->
    usize
{
    let len: usize = (bstr_left(c)).len();
    let __anf0: bool = crate::cbordetveraux::sizet_lte_u64(len, 18446744073709551615u64);
    if __anf0
    {
        let mty: crate::cbordetver::cbor_det_string_kind =
            crate::cbordetver::cbor_det_string_kind::ByteString;
        let res: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw =
            crate::cbordetver::cbor_det_mk_string(mty, bstr_left(c));
        let _letpattern: crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw = res;
        let x: crate::cbordetveraux::cbor_raw =
            match _letpattern
            {
                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some { v: c1 } => c1,
                _ => panic!("Incomplete pattern matching")
            };
        let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
        match ser
        {
            crate::cbordetver::option__size_t::None => 0usize,
            crate::cbordetver::option__size_t::Some { v: sz } => sz,
            _ => panic!("Incomplete pattern matching")
        }
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_bstr···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (&'a [u8], &'a [u8]) }
}

pub fn validate_and_parse_bstr <'a>(s: &'a [u8]) ->
    option__·Transport_bstr···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_bstr···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_bstr(rl);
              if test
              {
                  let x: &[u8] = parse_bstr(rl);
                  option__·Transport_bstr···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_bstr···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_uint(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let mt: u8 = crate::cbordetver::cbor_det_major_type(c);
    mt == crate::cbordetveraux::cbor_major_type_uint64
}

pub type evercddl_uint = u64;

pub fn uu___is_Mkevercddl_uint0(projectee: u64) -> bool
{
    crate::lowstar::ignore::ignore::<u64>(projectee);
    true
}

fn evercddl_uint_right(x1: u64) -> u64 { x1 }

fn evercddl_uint_left(x3: u64) -> u64 { x3 }

/**
Parser for evercddl_uint
*/
pub fn
parse_uint(c: crate::cbordetveraux::cbor_raw) ->
    u64
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let res: u64 =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
            _ => panic!("Incomplete pattern matching")
        };
    let res1: u64 = res;
    evercddl_uint_right(res1)
}

/**
Serializer for evercddl_uint
*/
pub fn
serialize_uint(c: u64, out: &mut [u8]) ->
    usize
{
    let mty: crate::cbordetver::cbor_det_int_kind = crate::cbordetver::cbor_det_int_kind::UInt64;
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_mk_int64(mty, evercddl_uint_left(c));
    let ser: crate::cbordetver::option__size_t = crate::cbordetver::cbor_det_serialize(x, out);
    match ser
    {
        crate::cbordetver::option__size_t::None => 0usize,
        crate::cbordetver::option__size_t::Some { v: sz } => sz,
        _ => panic!("Incomplete pattern matching")
    }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (u64, &'a [u8]) }
}

pub fn validate_and_parse_uint <'a>(s: &'a [u8]) ->
    option__·Transport_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_uint(rl);
              if test
              {
                  let x: u64 = parse_uint(rl);
                  option__·Transport_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_evercddl_uint···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_cryptoframe(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                if is_uint
                {
                    let v10: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                    let i2: u64 =
                        match _letpattern0
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i2 == 1u64
                }
                else
                { false }
            };
        let b_success: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                        if is_uint
                        {
                            let v10: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c1);
                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                            let i2: u64 =
                                match _letpattern0
                                {
                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>
                                      res,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            i2 == 2u64
                        }
                        else
                        { false }
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                    let test12: bool =
                        if is_done1
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            validate_uint(c1)
                        };
                    if test12
                    {
                        let
                        i12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done2: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i12);
                        let test13: bool =
                            if is_done2
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                validate_uint(c1)
                            };
                        if test13
                        {
                            let
                            i13:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i13);
                            if is_done3
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                validate_bstr(c1)
                            }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct cryptoframe <'a>
{ pub seq: u64, pub key_id: u64, pub cipher_text: &'a [u8] }

pub fn uu___is_Mkcryptoframe0(projectee: cryptoframe) -> bool
{
    crate::lowstar::ignore::ignore::<cryptoframe>(projectee);
    true
}

fn cryptoframe_right <'a>(x5: ((), ((), (u64, (u64, &'a [u8]))))) -> cryptoframe <'a>
{
    match x5 { (_x6,(_x7,(x8,(x9,x10)))) => cryptoframe { seq: x8, key_id: x9, cipher_text: x10 } }
}

fn cryptoframe_left <'a>(x11: cryptoframe <'a>) -> ((), ((), (u64, (u64, &'a [u8]))))
{
    let x20: u64 = x11.seq;
    let x21: u64 = x11.key_id;
    let x22: &[u8] = x11.cipher_text;
    ((),((),(x20,(x21,x22))))
}

/**
Parser for cryptoframe
*/
pub fn
parse_cryptoframe
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    cryptoframe
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let _tmp: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c1);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 1u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x);
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 2u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x0);
    let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let _tmp2: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
            validate_uint(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp2);
    let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c11, rlen02.wrapping_sub(rlen12));
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·2; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let w12: u64 = parse_uint(x1);
    let rlen03: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let mut pc30: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c12; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let _tmp3: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc30);
            validate_uint(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp3);
    let c13: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let rlen13: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
    let c0·3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c12, rlen03.wrapping_sub(rlen13));
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·3; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
    let w13: u64 = parse_uint(x2);
    let mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c13; 1usize];
    let x3: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
    let w2: &[u8] = parse_bstr(x3);
    let w20: (u64, &[u8]) = (w13,w2);
    let w21: (u64, (u64, &[u8])) = (w12,w20);
    let w22: ((), (u64, (u64, &[u8]))) = ((),w21);
    let res1: ((), ((), (u64, (u64, &[u8])))) = ((),w22);
    cryptoframe_right(res1)
}

/**
Serializer for cryptoframe
*/
pub fn
serialize_cryptoframe(c: cryptoframe, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let _letpattern: ((), ((), (u64, (u64, &[u8])))) = cryptoframe_left(c);
    let res: bool =
        {
            _letpattern.0;
            let c2: ((), (u64, (u64, &[u8]))) = _letpattern.1;
            let count: u64 = (&pcount)[0];
            let res1: bool =
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let mty: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c3: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
                    let res: crate::cbordetver::option__size_t =
                        crate::cbordetver::cbor_det_serialize(c3, out1);
                    let size1: usize =
                        match res
                        {
                            crate::cbordetver::option__size_t::None => 0usize,
                            crate::cbordetver::option__size_t::Some { v: r } => r,
                            _ => panic!("Incomplete pattern matching")
                        };
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0] = count.wrapping_add(1u64);
                        (&mut psize)[0] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false };
            if res1
            {
                let _letpattern1: ((), (u64, (u64, &[u8]))) = c2;
                _letpattern1.0;
                let c21: (u64, (u64, &[u8])) = _letpattern1.1;
                let count0: u64 = (&pcount)[0];
                let res11: bool =
                    if count0 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern2.0;
                        let out1: &mut [u8] = _letpattern2.1;
                        let mty: crate::cbordetver::cbor_det_int_kind =
                            crate::cbordetver::cbor_det_int_kind::UInt64;
                        let c3: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_mk_int64(mty, 2u64);
                        let res: crate::cbordetver::option__size_t =
                            crate::cbordetver::cbor_det_serialize(c3, out1);
                        let size1: usize =
                            match res
                            {
                                crate::cbordetver::option__size_t::None => 0usize,
                                crate::cbordetver::option__size_t::Some { v: r } => r,
                                _ => panic!("Incomplete pattern matching")
                            };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0] = count0.wrapping_add(1u64);
                            (&mut psize)[0] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    let _letpattern2: (u64, (u64, &[u8])) = c21;
                    let c12: u64 = _letpattern2.0;
                    let c22: (u64, &[u8]) = _letpattern2.1;
                    let count1: u64 = (&pcount)[0];
                    let res12: bool =
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern3: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern3.0;
                            let out1: &mut [u8] = _letpattern3.1;
                            let size1: usize = serialize_uint(c12, out1);
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count1.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res12
                    {
                        let _letpattern3: (u64, &[u8]) = c22;
                        let c13: u64 = _letpattern3.0;
                        let c23: &[u8] = _letpattern3.1;
                        let count2: u64 = (&pcount)[0];
                        let res13: bool =
                            if count2 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern4: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern4.0;
                                let out1: &mut [u8] = _letpattern4.1;
                                let size1: usize = serialize_uint(c13, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count2.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res13
                        {
                            let count3: u64 = (&pcount)[0];
                            if count3 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern4: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern4.0;
                                let out1: &mut [u8] = _letpattern4.1;
                                let size1: usize = serialize_bstr(c23, out1);
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count3.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (cryptoframe <'a>, &'a [u8]) }
}

pub fn validate_and_parse_cryptoframe <'a>(s: &'a [u8]) ->
    option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_cryptoframe(rl);
              if test
              {
                  let x: cryptoframe = parse_cryptoframe(rl);
                  option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_cryptoframe···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_kexresponse(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                if is_uint
                {
                    let v10: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                    let i2: u64 =
                        match _letpattern0
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i2 == 2u64
                }
                else
                { false }
            };
        let b_success: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                        if is_uint
                        {
                            let v10: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c1);
                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                            let i2: u64 =
                                match _letpattern0
                                {
                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>
                                      res,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            i2 == 1u64
                        }
                        else
                        { false }
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                    let test12: bool =
                        if is_done1
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                            if mt == 2u8
                            {
                                let v10: crate::cbordetver::cbor_det_view =
                                    crate::cbordetver::cbor_det_destruct(c1);
                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                let str: &[u8] =
                                    match _letpattern0
                                    {
                                        crate::cbordetver::cbor_det_view::String
                                        { payload: a, .. }
                                        => a,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let len: usize = str.len();
                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);
                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                                lo_ok && hi_ok
                            }
                            else
                            { false }
                        };
                    if test12
                    {
                        let
                        i12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done2: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i12);
                        let test13: bool =
                            if is_done2
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                if mt == 2u8
                                {
                                    let v10: crate::cbordetver::cbor_det_view =
                                        crate::cbordetver::cbor_det_destruct(c1);
                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                    let str: &[u8] =
                                        match _letpattern0
                                        {
                                            crate::cbordetver::cbor_det_view::String
                                            { payload: a, .. }
                                            => a,
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let len: usize = str.len();
                                    let lo_ok: bool =
                                        crate::cbordetveraux::u64_lte_sizet(32u64, len);
                                    let hi_ok: bool =
                                        crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                                    lo_ok && hi_ok
                                }
                                else
                                { false }
                            };
                        if test13
                        {
                            let
                            i13:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i13);
                            let test14: bool =
                                if is_done3
                                { false }
                                else
                                {
                                    let c1: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                    if mt == 2u8
                                    {
                                        let v10: crate::cbordetver::cbor_det_view =
                                            crate::cbordetver::cbor_det_destruct(c1);
                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                        let str: &[u8] =
                                            match _letpattern0
                                            {
                                                crate::cbordetver::cbor_det_view::String
                                                { payload: a, .. }
                                                => a,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let len: usize = str.len();
                                        let lo_ok: bool =
                                            crate::cbordetveraux::u64_lte_sizet(1088u64, len);
                                        let hi_ok: bool =
                                            crate::cbordetveraux::sizet_lte_u64(len, 1088u64);
                                        lo_ok && hi_ok
                                    }
                                    else
                                    { false }
                                };
                            if test14
                            {
                                let
                                i14:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0];
                                let is_done4: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i14);
                                let test15: bool =
                                    if is_done4
                                    { false }
                                    else
                                    {
                                        let c1: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        validate_bstr(c1)
                                    };
                                if test15
                                {
                                    let
                                    i15:
                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        (&pi)[0];
                                    let is_done5: bool =
                                        crate::cbordetver::cbor_det_array_iterator_is_empty(i15);
                                    let test16: bool =
                                        if is_done5
                                        { false }
                                        else
                                        {
                                            let c1: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_array_iterator_next(
                                                    &mut pi
                                                );
                                            validate_uint(c1)
                                        };
                                    if test16
                                    {
                                        let
                                        i16:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi)[0];
                                        let is_done6: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i16);
                                        if is_done6
                                        { false }
                                        else
                                        {
                                            let c1: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_array_iterator_next(
                                                    &mut pi
                                                );
                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                            if mt == 2u8
                                            {
                                                let v10: crate::cbordetver::cbor_det_view =
                                                    crate::cbordetver::cbor_det_destruct(c1);
                                                let _letpattern0: crate::cbordetver::cbor_det_view =
                                                    v10;
                                                let str: &[u8] =
                                                    match _letpattern0
                                                    {
                                                        crate::cbordetver::cbor_det_view::String
                                                        { payload: a, .. }
                                                        => a,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let len: usize = str.len();
                                                let lo_ok: bool =
                                                    crate::cbordetveraux::u64_lte_sizet(
                                                        3309u64,
                                                        len
                                                    );
                                                let hi_ok: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len,
                                                        3309u64
                                                    );
                                                lo_ok && hi_ok
                                            }
                                            else
                                            { false }
                                        }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct kexresponse <'a>
{
    pub identity_key: &'a [u8],
    pub ephemeral_key: &'a [u8],
    pub kem_cipher_text: &'a [u8],
    pub app_cipher_text: &'a [u8],
    pub key_id: u64,
    pub signature: &'a [u8]
}

pub fn uu___is_Mkkexresponse0(projectee: kexresponse) -> bool
{
    crate::lowstar::ignore::ignore::<kexresponse>(projectee);
    true
}

fn kexresponse_right <'a>(
    x8: ((), ((), (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], (u64, &'a [u8])))))))
) ->
    kexresponse
    <'a>
{
    match x8
    {
        (_x9,(_x10,(x11,(x12,(x13,(x14,(x15,x16))))))) =>
          kexresponse
          {
              identity_key: x11,
              ephemeral_key: x12,
              kem_cipher_text: x13,
              app_cipher_text: x14,
              key_id: x15,
              signature: x16
          }
    }
}

fn kexresponse_left <'a>(x17: kexresponse <'a>) ->
    ((), ((), (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], (u64, &'a [u8])))))))
{
    let x29: &[u8] = x17.identity_key;
    let x30: &[u8] = x17.ephemeral_key;
    let x31: &[u8] = x17.kem_cipher_text;
    let x32: &[u8] = x17.app_cipher_text;
    let x33: u64 = x17.key_id;
    let x34: &[u8] = x17.signature;
    ((),((),(x29,(x30,(x31,(x32,(x33,x34)))))))
}

/**
Parser for kexresponse
*/
pub fn
parse_kexresponse
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    kexresponse
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let _tmp: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c1);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 2u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x);
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 1u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x0);
    let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let _tmp2: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let str: &[u8] =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp2);
    let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c11, rlen02.wrapping_sub(rlen12));
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·2; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x1);
    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
    let s: &[u8] =
        match _letpattern0
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w12: &[u8] = s;
    let rlen03: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let mut pc30: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c12; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let _tmp3: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc30);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v11: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern1: crate::cbordetver::cbor_det_view = v11;
                let str: &[u8] =
                    match _letpattern1
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp3);
    let c13: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let rlen13: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
    let c0·3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c12, rlen03.wrapping_sub(rlen13));
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·3; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
    let v11: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x2);
    let _letpattern1: crate::cbordetver::cbor_det_view = v11;
    let s0: &[u8] =
        match _letpattern1
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w13: &[u8] = s0;
    let rlen04: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
    let mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c13; 1usize];
    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc40)[0];
    let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
    let _tmp4: bool =
        if is_done3
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v12: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern2: crate::cbordetver::cbor_det_view = v12;
                let str: &[u8] =
                    match _letpattern2
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(1088u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 1088u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp4);
    let c14: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc40)[0];
    let rlen14: u64 = crate::cbordetver::cbor_det_array_iterator_length(c14);
    let c0·4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c13, rlen04.wrapping_sub(rlen14));
    let mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·4; 1usize];
    let x3: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
    let v12: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x3);
    let _letpattern2: crate::cbordetver::cbor_det_view = v12;
    let s1: &[u8] =
        match _letpattern2
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w14: &[u8] = s1;
    let rlen05: u64 = crate::cbordetver::cbor_det_array_iterator_length(c14);
    let mut pc50: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c14; 1usize];
    let i4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc50)[0];
    let is_done4: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i4);
    let _tmp5: bool =
        if is_done4
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc50);
            validate_bstr(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp5);
    let c15: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc50)[0];
    let rlen15: u64 = crate::cbordetver::cbor_det_array_iterator_length(c15);
    let c0·5: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c14, rlen05.wrapping_sub(rlen15));
    let mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·5; 1usize];
    let x4: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
    let w15: &[u8] = parse_bstr(x4);
    let rlen06: u64 = crate::cbordetver::cbor_det_array_iterator_length(c15);
    let mut pc60: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c15; 1usize];
    let i5: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc60)[0];
    let is_done5: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i5);
    let _tmp6: bool =
        if is_done5
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc60);
            validate_uint(c2)
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp6);
    let c16: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc60)[0];
    let rlen16: u64 = crate::cbordetver::cbor_det_array_iterator_length(c16);
    let c0·6: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c15, rlen06.wrapping_sub(rlen16));
    let mut pc7: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·6; 1usize];
    let x5: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc7);
    let w16: u64 = parse_uint(x5);
    let mut pc70: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c16; 1usize];
    let x6: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc70);
    let v13: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x6);
    let _letpattern3: crate::cbordetver::cbor_det_view = v13;
    let s2: &[u8] =
        match _letpattern3
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w2: &[u8] = s2;
    let w20: (u64, &[u8]) = (w16,w2);
    let w21: (&[u8], (u64, &[u8])) = (w15,w20);
    let w22: (&[u8], (&[u8], (u64, &[u8]))) = (w14,w21);
    let w23: (&[u8], (&[u8], (&[u8], (u64, &[u8])))) = (w13,w22);
    let w24: (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8]))))) = (w12,w23);
    let w25: ((), (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8])))))) = ((),w24);
    let res1: ((), ((), (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8]))))))) = ((),w25);
    kexresponse_right(res1)
}

/**
Serializer for kexresponse
*/
pub fn
serialize_kexresponse(c: kexresponse, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let _letpattern: ((), ((), (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8]))))))) =
        kexresponse_left(c);
    let res: bool =
        {
            _letpattern.0;
            let c2: ((), (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8])))))) = _letpattern.1;
            let count: u64 = (&pcount)[0];
            let res1: bool =
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let mty: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c3: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty, 2u64);
                    let res: crate::cbordetver::option__size_t =
                        crate::cbordetver::cbor_det_serialize(c3, out1);
                    let size1: usize =
                        match res
                        {
                            crate::cbordetver::option__size_t::None => 0usize,
                            crate::cbordetver::option__size_t::Some { v: r } => r,
                            _ => panic!("Incomplete pattern matching")
                        };
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0] = count.wrapping_add(1u64);
                        (&mut psize)[0] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false };
            if res1
            {
                let _letpattern1: ((), (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8])))))) = c2;
                _letpattern1.0;
                let c21: (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8]))))) = _letpattern1.1;
                let count0: u64 = (&pcount)[0];
                let res11: bool =
                    if count0 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern2.0;
                        let out1: &mut [u8] = _letpattern2.1;
                        let mty: crate::cbordetver::cbor_det_int_kind =
                            crate::cbordetver::cbor_det_int_kind::UInt64;
                        let c3: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_mk_int64(mty, 1u64);
                        let res: crate::cbordetver::option__size_t =
                            crate::cbordetver::cbor_det_serialize(c3, out1);
                        let size1: usize =
                            match res
                            {
                                crate::cbordetver::option__size_t::None => 0usize,
                                crate::cbordetver::option__size_t::Some { v: r } => r,
                                _ => panic!("Incomplete pattern matching")
                            };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0] = count0.wrapping_add(1u64);
                            (&mut psize)[0] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    let _letpattern2: (&[u8], (&[u8], (&[u8], (&[u8], (u64, &[u8]))))) = c21;
                    let c12: &[u8] = _letpattern2.0;
                    let c22: (&[u8], (&[u8], (&[u8], (u64, &[u8])))) = _letpattern2.1;
                    let count1: u64 = (&pcount)[0];
                    let res12: bool =
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern3: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern3.0;
                            let out1: &mut [u8] = _letpattern3.1;
                            let len: usize = c12.len();
                            let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);
                            let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                            let size1: usize =
                                if lo_ok && hi_ok
                                {
                                    if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                    {
                                        let len1: usize = c12.len();
                                        let __anf0: bool =
                                            crate::cbordetveraux::sizet_lte_u64(
                                                len1,
                                                18446744073709551615u64
                                            );
                                        if __anf0
                                        {
                                            let mty: crate::cbordetver::cbor_det_string_kind =
                                                crate::cbordetver::cbor_det_string_kind::ByteString;
                                            let
                                            res:
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                crate::cbordetver::cbor_det_mk_string(mty, c12);
                                            let
                                            _letpattern4:
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                res;
                                            let x: crate::cbordetveraux::cbor_raw =
                                                match _letpattern4
                                                {
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                    { v: c3 }
                                                    => c3,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let ser: crate::cbordetver::option__size_t =
                                                crate::cbordetver::cbor_det_serialize(x, out1);
                                            match ser
                                            {
                                                crate::cbordetver::option__size_t::None => 0usize,
                                                crate::cbordetver::option__size_t::Some { v: sz } =>
                                                  sz,
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        }
                                        else
                                        { 0usize }
                                    }
                                    else
                                    {
                                        let len1: usize = c12.len();
                                        let __anf0: bool =
                                            crate::cbordetveraux::sizet_lte_u64(
                                                len1,
                                                18446744073709551615u64
                                            );
                                        if __anf0
                                        {
                                            let correct: bool =
                                                crate::cbordetver::cbor_impl_utf8_correct(c12);
                                            if correct
                                            {
                                                let mty: crate::cbordetver::cbor_det_string_kind =
                                                    if
                                                    crate::cbordetveraux::cbor_major_type_text_string
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                    {
                                                        crate::cbordetver::cbor_det_string_kind::ByteString
                                                    }
                                                    else
                                                    {
                                                        crate::cbordetver::cbor_det_string_kind::TextString
                                                    };
                                                let
                                                res:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    crate::cbordetver::cbor_det_mk_string(mty, c12);
                                                let
                                                _letpattern4:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    res;
                                                let x: crate::cbordetveraux::cbor_raw =
                                                    match _letpattern4
                                                    {
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                        { v: c3 }
                                                        => c3,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let ser: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(x, out1);
                                                match ser
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: sz }
                                                    => sz,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { 0usize }
                                        }
                                        else
                                        { 0usize }
                                    }
                                }
                                else
                                { 0usize };
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count1.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res12
                    {
                        let _letpattern3: (&[u8], (&[u8], (&[u8], (u64, &[u8])))) = c22;
                        let c13: &[u8] = _letpattern3.0;
                        let c23: (&[u8], (&[u8], (u64, &[u8]))) = _letpattern3.1;
                        let count2: u64 = (&pcount)[0];
                        let res13: bool =
                            if count2 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern4: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern4.0;
                                let out1: &mut [u8] = _letpattern4.1;
                                let len: usize = c13.len();
                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(32u64, len);
                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 32u64);
                                let size1: usize =
                                    if lo_ok && hi_ok
                                    {
                                        if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                        {
                                            let len1: usize = c13.len();
                                            let __anf0: bool =
                                                crate::cbordetveraux::sizet_lte_u64(
                                                    len1,
                                                    18446744073709551615u64
                                                );
                                            if __anf0
                                            {
                                                let mty: crate::cbordetver::cbor_det_string_kind =
                                                    crate::cbordetver::cbor_det_string_kind::ByteString;
                                                let
                                                res:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    crate::cbordetver::cbor_det_mk_string(mty, c13);
                                                let
                                                _letpattern5:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    res;
                                                let x: crate::cbordetveraux::cbor_raw =
                                                    match _letpattern5
                                                    {
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                        { v: c3 }
                                                        => c3,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let ser: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(x, out1);
                                                match ser
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: sz }
                                                    => sz,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { 0usize }
                                        }
                                        else
                                        {
                                            let len1: usize = c13.len();
                                            let __anf0: bool =
                                                crate::cbordetveraux::sizet_lte_u64(
                                                    len1,
                                                    18446744073709551615u64
                                                );
                                            if __anf0
                                            {
                                                let correct: bool =
                                                    crate::cbordetver::cbor_impl_utf8_correct(c13);
                                                if correct
                                                {
                                                    let
                                                    mty: crate::cbordetver::cbor_det_string_kind
                                                    =
                                                        if
                                                        crate::cbordetveraux::cbor_major_type_text_string
                                                        ==
                                                        crate::cbordetveraux::cbor_major_type_byte_string
                                                        {
                                                            crate::cbordetver::cbor_det_string_kind::ByteString
                                                        }
                                                        else
                                                        {
                                                            crate::cbordetver::cbor_det_string_kind::TextString
                                                        };
                                                    let
                                                    res:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        crate::cbordetver::cbor_det_mk_string(
                                                            mty,
                                                            c13
                                                        );
                                                    let
                                                    _letpattern5:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        res;
                                                    let x: crate::cbordetveraux::cbor_raw =
                                                        match _letpattern5
                                                        {
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                            { v: c3 }
                                                            => c3,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let ser: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            x,
                                                            out1
                                                        );
                                                    match ser
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: sz }
                                                        => sz,
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                }
                                                else
                                                { 0usize }
                                            }
                                            else
                                            { 0usize }
                                        }
                                    }
                                    else
                                    { 0usize };
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count2.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res13
                        {
                            let _letpattern4: (&[u8], (&[u8], (u64, &[u8]))) = c23;
                            let c14: &[u8] = _letpattern4.0;
                            let c24: (&[u8], (u64, &[u8])) = _letpattern4.1;
                            let count3: u64 = (&pcount)[0];
                            let res14: bool =
                                if count3 < 18446744073709551615u64
                                {
                                    let size: usize = (&psize)[0];
                                    let _letpattern5: (&mut [u8], &mut [u8]) =
                                        out.split_at_mut(size);
                                    let _out0: &[u8] = _letpattern5.0;
                                    let out1: &mut [u8] = _letpattern5.1;
                                    let len: usize = c14.len();
                                    let lo_ok: bool =
                                        crate::cbordetveraux::u64_lte_sizet(1088u64, len);
                                    let hi_ok: bool =
                                        crate::cbordetveraux::sizet_lte_u64(len, 1088u64);
                                    let size1: usize =
                                        if lo_ok && hi_ok
                                        {
                                            if
                                            2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                            {
                                                let len1: usize = c14.len();
                                                let __anf0: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len1,
                                                        18446744073709551615u64
                                                    );
                                                if __anf0
                                                {
                                                    let
                                                    mty: crate::cbordetver::cbor_det_string_kind
                                                    =
                                                        crate::cbordetver::cbor_det_string_kind::ByteString;
                                                    let
                                                    res:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        crate::cbordetver::cbor_det_mk_string(
                                                            mty,
                                                            c14
                                                        );
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        res;
                                                    let x: crate::cbordetveraux::cbor_raw =
                                                        match _letpattern6
                                                        {
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                            { v: c3 }
                                                            => c3,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let ser: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            x,
                                                            out1
                                                        );
                                                    match ser
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: sz }
                                                        => sz,
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                }
                                                else
                                                { 0usize }
                                            }
                                            else
                                            {
                                                let len1: usize = c14.len();
                                                let __anf0: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len1,
                                                        18446744073709551615u64
                                                    );
                                                if __anf0
                                                {
                                                    let correct: bool =
                                                        crate::cbordetver::cbor_impl_utf8_correct(
                                                            c14
                                                        );
                                                    if correct
                                                    {
                                                        let
                                                        mty: crate::cbordetver::cbor_det_string_kind
                                                        =
                                                            if
                                                            crate::cbordetveraux::cbor_major_type_text_string
                                                            ==
                                                            crate::cbordetveraux::cbor_major_type_byte_string
                                                            {
                                                                crate::cbordetver::cbor_det_string_kind::ByteString
                                                            }
                                                            else
                                                            {
                                                                crate::cbordetver::cbor_det_string_kind::TextString
                                                            };
                                                        let
                                                        res:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            crate::cbordetver::cbor_det_mk_string(
                                                                mty,
                                                                c14
                                                            );
                                                        let
                                                        _letpattern6:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            res;
                                                        let x: crate::cbordetveraux::cbor_raw =
                                                            match _letpattern6
                                                            {
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                { v: c3 }
                                                                => c3,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        let ser: crate::cbordetver::option__size_t =
                                                            crate::cbordetver::cbor_det_serialize(
                                                                x,
                                                                out1
                                                            );
                                                        match ser
                                                        {
                                                            crate::cbordetver::option__size_t::None
                                                            => 0usize,
                                                            crate::cbordetver::option__size_t::Some
                                                            { v: sz }
                                                            => sz,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        }
                                                    }
                                                    else
                                                    { 0usize }
                                                }
                                                else
                                                { 0usize }
                                            }
                                        }
                                        else
                                        { 0usize };
                                    if size1 == 0usize
                                    { false }
                                    else
                                    {
                                        (&mut pcount)[0] = count3.wrapping_add(1u64);
                                        (&mut psize)[0] = size.wrapping_add(size1);
                                        true
                                    }
                                }
                                else
                                { false };
                            if res14
                            {
                                let _letpattern5: (&[u8], (u64, &[u8])) = c24;
                                let c15: &[u8] = _letpattern5.0;
                                let c25: (u64, &[u8]) = _letpattern5.1;
                                let count4: u64 = (&pcount)[0];
                                let res15: bool =
                                    if count4 < 18446744073709551615u64
                                    {
                                        let size: usize = (&psize)[0];
                                        let _letpattern6: (&mut [u8], &mut [u8]) =
                                            out.split_at_mut(size);
                                        let _out0: &[u8] = _letpattern6.0;
                                        let out1: &mut [u8] = _letpattern6.1;
                                        let size1: usize = serialize_bstr(c15, out1);
                                        if size1 == 0usize
                                        { false }
                                        else
                                        {
                                            (&mut pcount)[0] = count4.wrapping_add(1u64);
                                            (&mut psize)[0] = size.wrapping_add(size1);
                                            true
                                        }
                                    }
                                    else
                                    { false };
                                if res15
                                {
                                    let _letpattern6: (u64, &[u8]) = c25;
                                    let c16: u64 = _letpattern6.0;
                                    let c26: &[u8] = _letpattern6.1;
                                    let count5: u64 = (&pcount)[0];
                                    let res16: bool =
                                        if count5 < 18446744073709551615u64
                                        {
                                            let size: usize = (&psize)[0];
                                            let _letpattern7: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size);
                                            let _out0: &[u8] = _letpattern7.0;
                                            let out1: &mut [u8] = _letpattern7.1;
                                            let size1: usize = serialize_uint(c16, out1);
                                            if size1 == 0usize
                                            { false }
                                            else
                                            {
                                                (&mut pcount)[0] = count5.wrapping_add(1u64);
                                                (&mut psize)[0] = size.wrapping_add(size1);
                                                true
                                            }
                                        }
                                        else
                                        { false };
                                    if res16
                                    {
                                        let count6: u64 = (&pcount)[0];
                                        if count6 < 18446744073709551615u64
                                        {
                                            let size: usize = (&psize)[0];
                                            let _letpattern7: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size);
                                            let _out0: &[u8] = _letpattern7.0;
                                            let out1: &mut [u8] = _letpattern7.1;
                                            let len: usize = c26.len();
                                            let lo_ok: bool =
                                                crate::cbordetveraux::u64_lte_sizet(3309u64, len);
                                            let hi_ok: bool =
                                                crate::cbordetveraux::sizet_lte_u64(len, 3309u64);
                                            let size1: usize =
                                                if lo_ok && hi_ok
                                                {
                                                    if
                                                    2u8
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                    {
                                                        let len1: usize = c26.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let
                                                            mty:
                                                            crate::cbordetver::cbor_det_string_kind
                                                            =
                                                                crate::cbordetver::cbor_det_string_kind::ByteString;
                                                            let
                                                            res:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                crate::cbordetver::cbor_det_mk_string(
                                                                    mty,
                                                                    c26
                                                                );
                                                            let
                                                            _letpattern8:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                res;
                                                            let x: crate::cbordetveraux::cbor_raw =
                                                                match _letpattern8
                                                                {
                                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                    { v: c3 }
                                                                    => c3,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            let
                                                            ser: crate::cbordetver::option__size_t
                                                            =
                                                                crate::cbordetver::cbor_det_serialize(
                                                                    x,
                                                                    out1
                                                                );
                                                            match ser
                                                            {
                                                                crate::cbordetver::option__size_t::None
                                                                => 0usize,
                                                                crate::cbordetver::option__size_t::Some
                                                                { v: sz }
                                                                => sz,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                    else
                                                    {
                                                        let len1: usize = c26.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let correct: bool =
                                                                crate::cbordetver::cbor_impl_utf8_correct(
                                                                    c26
                                                                );
                                                            if correct
                                                            {
                                                                let
                                                                mty:
                                                                crate::cbordetver::cbor_det_string_kind
                                                                =
                                                                    if
                                                                    crate::cbordetveraux::cbor_major_type_text_string
                                                                    ==
                                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::ByteString
                                                                    }
                                                                    else
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::TextString
                                                                    };
                                                                let
                                                                res:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_mk_string(
                                                                        mty,
                                                                        c26
                                                                    );
                                                                let
                                                                _letpattern8:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    res;
                                                                let
                                                                x: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    match _letpattern8
                                                                    {
                                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                        { v: c3 }
                                                                        => c3,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let
                                                                ser:
                                                                crate::cbordetver::option__size_t
                                                                =
                                                                    crate::cbordetver::cbor_det_serialize(
                                                                        x,
                                                                        out1
                                                                    );
                                                                match ser
                                                                {
                                                                    crate::cbordetver::option__size_t::None
                                                                    => 0usize,
                                                                    crate::cbordetver::option__size_t::Some
                                                                    { v: sz }
                                                                    => sz,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                }
                                                            }
                                                            else
                                                            { 0usize }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                }
                                                else
                                                { 0usize };
                                            if size1 == 0usize
                                            { false }
                                            else
                                            {
                                                (&mut pcount)[0] = count6.wrapping_add(1u64);
                                                (&mut psize)[0] = size.wrapping_add(size1);
                                                true
                                            }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (kexresponse <'a>, &'a [u8]) }
}

pub fn validate_and_parse_kexresponse <'a>(s: &'a [u8]) ->
    option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_kexresponse(rl);
              if test
              {
                  let x: kexresponse = parse_kexresponse(rl);
                  option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_kexresponse···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}

pub fn validate_initkex(c: crate::cbordetveraux::cbor_raw) -> bool
{
    let ty: u8 = crate::cbordetver::cbor_det_major_type(c);
    if ty == crate::cbordetveraux::cbor_major_type_array
    {
        let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
        let _letpattern: crate::cbordetver::cbor_det_view = v1;
        let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
            match _letpattern
            {
                crate::cbordetver::cbor_det_view::Array { _0: a } =>
                  crate::cbordetver::cbor_det_array_iterator_start(a),
                _ => panic!("Incomplete pattern matching")
            };
        let mut pi: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
            [i; 1usize];
        let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pi)[0];
        let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
        let test1: bool =
            if is_done
            { false }
            else
            {
                let c1: crate::cbordetveraux::cbor_raw =
                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                if is_uint
                {
                    let v10: crate::cbordetver::cbor_det_view =
                        crate::cbordetver::cbor_det_destruct(c1);
                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                    let i2: u64 =
                        match _letpattern0
                        {
                            crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                            _ => panic!("Incomplete pattern matching")
                        };
                    i2 == 2u64
                }
                else
                { false }
            };
        let b_success: bool =
            if test1
            {
                let i10: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                    (&pi)[0];
                let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i10);
                let test11: bool =
                    if is_done0
                    { false }
                    else
                    {
                        let c1: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                        let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
                        if is_uint
                        {
                            let v10: crate::cbordetver::cbor_det_view =
                                crate::cbordetver::cbor_det_destruct(c1);
                            let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                            let i2: u64 =
                                match _letpattern0
                                {
                                    crate::cbordetver::cbor_det_view::Int64 { value: res, .. } =>
                                      res,
                                    _ => panic!("Incomplete pattern matching")
                                };
                            i2 == 0u64
                        }
                        else
                        { false }
                    };
                if test11
                {
                    let i11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                        (&pi)[0];
                    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i11);
                    let test12: bool =
                        if is_done1
                        { false }
                        else
                        {
                            let c1: crate::cbordetveraux::cbor_raw =
                                crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                            if mt == 2u8
                            {
                                let v10: crate::cbordetver::cbor_det_view =
                                    crate::cbordetver::cbor_det_destruct(c1);
                                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                let str: &[u8] =
                                    match _letpattern0
                                    {
                                        crate::cbordetver::cbor_det_view::String
                                        { payload: a, .. }
                                        => a,
                                        _ => panic!("Incomplete pattern matching")
                                    };
                                let len: usize = str.len();
                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);
                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);
                                lo_ok && hi_ok
                            }
                            else
                            { false }
                        };
                    if test12
                    {
                        let
                        i12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                        =
                            (&pi)[0];
                        let is_done2: bool =
                            crate::cbordetver::cbor_det_array_iterator_is_empty(i12);
                        let test13: bool =
                            if is_done2
                            { false }
                            else
                            {
                                let c1: crate::cbordetveraux::cbor_raw =
                                    crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                if mt == 2u8
                                {
                                    let v10: crate::cbordetver::cbor_det_view =
                                        crate::cbordetver::cbor_det_destruct(c1);
                                    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                    let str: &[u8] =
                                        match _letpattern0
                                        {
                                            crate::cbordetver::cbor_det_view::String
                                            { payload: a, .. }
                                            => a,
                                            _ => panic!("Incomplete pattern matching")
                                        };
                                    let len: usize = str.len();
                                    let lo_ok: bool =
                                        crate::cbordetveraux::u64_lte_sizet(98u64, len);
                                    let hi_ok: bool =
                                        crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                                    lo_ok && hi_ok
                                }
                                else
                                { false }
                            };
                        if test13
                        {
                            let
                            i13:
                            crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                            =
                                (&pi)[0];
                            let is_done3: bool =
                                crate::cbordetver::cbor_det_array_iterator_is_empty(i13);
                            let test14: bool =
                                if is_done3
                                { false }
                                else
                                {
                                    let c1: crate::cbordetveraux::cbor_raw =
                                        crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                    let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                    if mt == 2u8
                                    {
                                        let v10: crate::cbordetver::cbor_det_view =
                                            crate::cbordetver::cbor_det_destruct(c1);
                                        let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                                        let str: &[u8] =
                                            match _letpattern0
                                            {
                                                crate::cbordetver::cbor_det_view::String
                                                { payload: a, .. }
                                                => a,
                                                _ => panic!("Incomplete pattern matching")
                                            };
                                        let len: usize = str.len();
                                        let lo_ok: bool =
                                            crate::cbordetveraux::u64_lte_sizet(98u64, len);
                                        let hi_ok: bool =
                                            crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                                        lo_ok && hi_ok
                                    }
                                    else
                                    { false }
                                };
                            if test14
                            {
                                let
                                i14:
                                crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                =
                                    (&pi)[0];
                                let is_done4: bool =
                                    crate::cbordetver::cbor_det_array_iterator_is_empty(i14);
                                let test15: bool =
                                    if is_done4
                                    { false }
                                    else
                                    {
                                        let c1: crate::cbordetveraux::cbor_raw =
                                            crate::cbordetver::cbor_det_array_iterator_next(&mut pi);
                                        let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                        if mt == 2u8
                                        {
                                            let v10: crate::cbordetver::cbor_det_view =
                                                crate::cbordetver::cbor_det_destruct(c1);
                                            let _letpattern0: crate::cbordetver::cbor_det_view =
                                                v10;
                                            let str: &[u8] =
                                                match _letpattern0
                                                {
                                                    crate::cbordetver::cbor_det_view::String
                                                    { payload: a, .. }
                                                    => a,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let len: usize = str.len();
                                            let lo_ok: bool =
                                                crate::cbordetveraux::u64_lte_sizet(1249u64, len);
                                            let hi_ok: bool =
                                                crate::cbordetveraux::sizet_lte_u64(len, 1249u64);
                                            lo_ok && hi_ok
                                        }
                                        else
                                        { false }
                                    };
                                if test15
                                {
                                    let
                                    i15:
                                    crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                    =
                                        (&pi)[0];
                                    let is_done5: bool =
                                        crate::cbordetver::cbor_det_array_iterator_is_empty(i15);
                                    let test16: bool =
                                        if is_done5
                                        { false }
                                        else
                                        {
                                            let c1: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_array_iterator_next(
                                                    &mut pi
                                                );
                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                            if mt == 2u8
                                            {
                                                let v10: crate::cbordetver::cbor_det_view =
                                                    crate::cbordetver::cbor_det_destruct(c1);
                                                let _letpattern0: crate::cbordetver::cbor_det_view =
                                                    v10;
                                                let str: &[u8] =
                                                    match _letpattern0
                                                    {
                                                        crate::cbordetver::cbor_det_view::String
                                                        { payload: a, .. }
                                                        => a,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let len: usize = str.len();
                                                let lo_ok: bool =
                                                    crate::cbordetveraux::u64_lte_sizet(
                                                        1952u64,
                                                        len
                                                    );
                                                let hi_ok: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len,
                                                        1952u64
                                                    );
                                                lo_ok && hi_ok
                                            }
                                            else
                                            { false }
                                        };
                                    if test16
                                    {
                                        let
                                        i16:
                                        crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw
                                        =
                                            (&pi)[0];
                                        let is_done6: bool =
                                            crate::cbordetver::cbor_det_array_iterator_is_empty(i16);
                                        if is_done6
                                        { false }
                                        else
                                        {
                                            let c1: crate::cbordetveraux::cbor_raw =
                                                crate::cbordetver::cbor_det_array_iterator_next(
                                                    &mut pi
                                                );
                                            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
                                            if mt == 2u8
                                            {
                                                let v10: crate::cbordetver::cbor_det_view =
                                                    crate::cbordetver::cbor_det_destruct(c1);
                                                let _letpattern0: crate::cbordetver::cbor_det_view =
                                                    v10;
                                                let str: &[u8] =
                                                    match _letpattern0
                                                    {
                                                        crate::cbordetver::cbor_det_view::String
                                                        { payload: a, .. }
                                                        => a,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let len: usize = str.len();
                                                let lo_ok: bool =
                                                    crate::cbordetveraux::u64_lte_sizet(
                                                        3309u64,
                                                        len
                                                    );
                                                let hi_ok: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len,
                                                        3309u64
                                                    );
                                                lo_ok && hi_ok
                                            }
                                            else
                                            { false }
                                        }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false };
        if b_success
        {
            let i·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
                (&pi)[0];
            crate::cbordetver::cbor_det_array_iterator_is_empty(i·)
        }
        else
        { false }
    }
    else
    { false }
}

#[derive(PartialEq, Clone, Copy)]
pub struct initkex <'a>
{
    pub identity_key: &'a [u8],
    pub pre_key: &'a [u8],
    pub one_time_key: &'a [u8],
    pub pq_key: &'a [u8],
    pub mldsa_public_key: &'a [u8],
    pub signature: &'a [u8]
}

pub fn uu___is_Mkinitkex0(projectee: initkex) -> bool
{
    crate::lowstar::ignore::ignore::<initkex>(projectee);
    true
}

fn initkex_right <'a>(
    x8: ((), ((), (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], &'a [u8])))))))
) ->
    initkex
    <'a>
{
    match x8
    {
        (_x9,(_x10,(x11,(x12,(x13,(x14,(x15,x16))))))) =>
          initkex
          {
              identity_key: x11,
              pre_key: x12,
              one_time_key: x13,
              pq_key: x14,
              mldsa_public_key: x15,
              signature: x16
          }
    }
}

fn initkex_left <'a>(x17: initkex <'a>) ->
    ((), ((), (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], (&'a [u8], &'a [u8])))))))
{
    let x29: &[u8] = x17.identity_key;
    let x30: &[u8] = x17.pre_key;
    let x31: &[u8] = x17.one_time_key;
    let x32: &[u8] = x17.pq_key;
    let x33: &[u8] = x17.mldsa_public_key;
    let x34: &[u8] = x17.signature;
    ((),((),(x29,(x30,(x31,(x32,(x33,x34)))))))
}

/**
Parser for initkex
*/
pub fn
parse_initkex
<'a>(c: crate::cbordetveraux::cbor_raw <'a>) ->
    initkex
    <'a>
{
    let v1: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(c);
    let _letpattern: crate::cbordetver::cbor_det_view = v1;
    let ar: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        match _letpattern
        {
            crate::cbordetver::cbor_det_view::Array { _0: a } =>
              crate::cbordetver::cbor_det_array_iterator_start(a),
            _ => panic!("Incomplete pattern matching")
        };
    let rlen0: u64 = crate::cbordetver::cbor_det_array_iterator_length(ar);
    let mut pc: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [ar; 1usize];
    let i: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let is_done: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i);
    let _tmp: bool =
        if is_done
        { false }
        else
        {
            let c1: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c1);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c1);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 2u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp);
    let c1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc)[0];
    let rlen1: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let c0·: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(ar, rlen0.wrapping_sub(rlen1));
    let mut pc1: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·; 1usize];
    let x: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc1);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x);
    let rlen01: u64 = crate::cbordetver::cbor_det_array_iterator_length(c1);
    let mut pc10: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c1; 1usize];
    let i0: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let is_done0: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i0);
    let _tmp1: bool =
        if is_done0
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc10);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            let is_uint: bool = mt == crate::cbordetveraux::cbor_major_type_uint64;
            if is_uint
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let i1: u64 =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::Int64 { value: res, .. } => res,
                        _ => panic!("Incomplete pattern matching")
                    };
                i1 == 0u64
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp1);
    let c11: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc10)[0];
    let rlen11: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let c0·1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c1, rlen01.wrapping_sub(rlen11));
    let mut pc2: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·1; 1usize];
    let x0: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc2);
    crate::lowstar::ignore::ignore::<crate::cbordetveraux::cbor_raw>(x0);
    let rlen02: u64 = crate::cbordetver::cbor_det_array_iterator_length(c11);
    let mut pc20: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c11; 1usize];
    let i1: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let is_done1: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i1);
    let _tmp2: bool =
        if is_done1
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc20);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v10: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern0: crate::cbordetver::cbor_det_view = v10;
                let str: &[u8] =
                    match _letpattern0
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp2);
    let c12: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc20)[0];
    let rlen12: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let c0·2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c11, rlen02.wrapping_sub(rlen12));
    let mut pc3: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·2; 1usize];
    let x1: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc3);
    let v10: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x1);
    let _letpattern0: crate::cbordetver::cbor_det_view = v10;
    let s: &[u8] =
        match _letpattern0
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w12: &[u8] = s;
    let rlen03: u64 = crate::cbordetver::cbor_det_array_iterator_length(c12);
    let mut pc30: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c12; 1usize];
    let i2: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let is_done2: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i2);
    let _tmp3: bool =
        if is_done2
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc30);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v11: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern1: crate::cbordetver::cbor_det_view = v11;
                let str: &[u8] =
                    match _letpattern1
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(98u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp3);
    let c13: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc30)[0];
    let rlen13: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
    let c0·3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c12, rlen03.wrapping_sub(rlen13));
    let mut pc4: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·3; 1usize];
    let x2: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc4);
    let v11: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x2);
    let _letpattern1: crate::cbordetver::cbor_det_view = v11;
    let s0: &[u8] =
        match _letpattern1
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w13: &[u8] = s0;
    let rlen04: u64 = crate::cbordetver::cbor_det_array_iterator_length(c13);
    let mut pc40: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c13; 1usize];
    let i3: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc40)[0];
    let is_done3: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i3);
    let _tmp4: bool =
        if is_done3
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc40);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v12: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern2: crate::cbordetver::cbor_det_view = v12;
                let str: &[u8] =
                    match _letpattern2
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(98u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp4);
    let c14: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc40)[0];
    let rlen14: u64 = crate::cbordetver::cbor_det_array_iterator_length(c14);
    let c0·4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c13, rlen04.wrapping_sub(rlen14));
    let mut pc5: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·4; 1usize];
    let x3: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc5);
    let v12: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x3);
    let _letpattern2: crate::cbordetver::cbor_det_view = v12;
    let s1: &[u8] =
        match _letpattern2
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w14: &[u8] = s1;
    let rlen05: u64 = crate::cbordetver::cbor_det_array_iterator_length(c14);
    let mut pc50: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c14; 1usize];
    let i4: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc50)[0];
    let is_done4: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i4);
    let _tmp5: bool =
        if is_done4
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc50);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v13: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern3: crate::cbordetver::cbor_det_view = v13;
                let str: &[u8] =
                    match _letpattern3
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(1249u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 1249u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp5);
    let c15: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc50)[0];
    let rlen15: u64 = crate::cbordetver::cbor_det_array_iterator_length(c15);
    let c0·5: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c14, rlen05.wrapping_sub(rlen15));
    let mut pc6: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·5; 1usize];
    let x4: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc6);
    let v13: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x4);
    let _letpattern3: crate::cbordetver::cbor_det_view = v13;
    let s2: &[u8] =
        match _letpattern3
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w15: &[u8] = s2;
    let rlen06: u64 = crate::cbordetver::cbor_det_array_iterator_length(c15);
    let mut pc60: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c15; 1usize];
    let i5: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc60)[0];
    let is_done5: bool = crate::cbordetver::cbor_det_array_iterator_is_empty(i5);
    let _tmp6: bool =
        if is_done5
        { false }
        else
        {
            let c2: crate::cbordetveraux::cbor_raw =
                crate::cbordetver::cbor_det_array_iterator_next(&mut pc60);
            let mt: u8 = crate::cbordetver::cbor_det_major_type(c2);
            if mt == 2u8
            {
                let v14: crate::cbordetver::cbor_det_view =
                    crate::cbordetver::cbor_det_destruct(c2);
                let _letpattern4: crate::cbordetver::cbor_det_view = v14;
                let str: &[u8] =
                    match _letpattern4
                    {
                        crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
                        _ => panic!("Incomplete pattern matching")
                    };
                let len: usize = str.len();
                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(1952u64, len);
                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 1952u64);
                lo_ok && hi_ok
            }
            else
            { false }
        };
    crate::lowstar::ignore::ignore::<bool>(_tmp6);
    let c16: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw = (&pc60)[0];
    let rlen16: u64 = crate::cbordetver::cbor_det_array_iterator_length(c16);
    let c0·6: crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_truncate(c15, rlen06.wrapping_sub(rlen16));
    let mut pc7: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c0·6; 1usize];
    let x5: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc7);
    let v14: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x5);
    let _letpattern4: crate::cbordetver::cbor_det_view = v14;
    let s3: &[u8] =
        match _letpattern4
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w16: &[u8] = s3;
    let mut pc70: [crate::cbordetveraux::cbor_raw_iterator__CBOR_Pulse_Raw_Type_cbor_raw; 1] =
        [c16; 1usize];
    let x6: crate::cbordetveraux::cbor_raw =
        crate::cbordetver::cbor_det_array_iterator_next(&mut pc70);
    let v15: crate::cbordetver::cbor_det_view = crate::cbordetver::cbor_det_destruct(x6);
    let _letpattern5: crate::cbordetver::cbor_det_view = v15;
    let s4: &[u8] =
        match _letpattern5
        {
            crate::cbordetver::cbor_det_view::String { payload: a, .. } => a,
            _ => panic!("Incomplete pattern matching")
        };
    let w2: &[u8] = s4;
    let w20: (&[u8], &[u8]) = (w16,w2);
    let w21: (&[u8], (&[u8], &[u8])) = (w15,w20);
    let w22: (&[u8], (&[u8], (&[u8], &[u8]))) = (w14,w21);
    let w23: (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))) = (w13,w22);
    let w24: (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8]))))) = (w12,w23);
    let w25: ((), (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))))) = ((),w24);
    let res1: ((), ((), (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8]))))))) = ((),w25);
    initkex_right(res1)
}

/**
Serializer for initkex
*/
pub fn
serialize_initkex(c: initkex, out: &mut [u8]) ->
    usize
{
    let mut pcount: [u64; 1] = [0u64; 1usize];
    let mut psize: [usize; 1] = [0usize; 1usize];
    let _letpattern: ((), ((), (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8]))))))) =
        initkex_left(c);
    let res: bool =
        {
            _letpattern.0;
            let c2: ((), (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))))) = _letpattern.1;
            let count: u64 = (&pcount)[0];
            let res1: bool =
                if count < 18446744073709551615u64
                {
                    let size: usize = (&psize)[0];
                    let _letpattern1: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                    let _out0: &[u8] = _letpattern1.0;
                    let out1: &mut [u8] = _letpattern1.1;
                    let mty: crate::cbordetver::cbor_det_int_kind =
                        crate::cbordetver::cbor_det_int_kind::UInt64;
                    let c3: crate::cbordetveraux::cbor_raw =
                        crate::cbordetver::cbor_det_mk_int64(mty, 2u64);
                    let res: crate::cbordetver::option__size_t =
                        crate::cbordetver::cbor_det_serialize(c3, out1);
                    let size1: usize =
                        match res
                        {
                            crate::cbordetver::option__size_t::None => 0usize,
                            crate::cbordetver::option__size_t::Some { v: r } => r,
                            _ => panic!("Incomplete pattern matching")
                        };
                    if size1 == 0usize
                    { false }
                    else
                    {
                        (&mut pcount)[0] = count.wrapping_add(1u64);
                        (&mut psize)[0] = size.wrapping_add(size1);
                        true
                    }
                }
                else
                { false };
            if res1
            {
                let _letpattern1: ((), (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))))) = c2;
                _letpattern1.0;
                let c21: (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8]))))) = _letpattern1.1;
                let count0: u64 = (&pcount)[0];
                let res11: bool =
                    if count0 < 18446744073709551615u64
                    {
                        let size: usize = (&psize)[0];
                        let _letpattern2: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                        let _out0: &[u8] = _letpattern2.0;
                        let out1: &mut [u8] = _letpattern2.1;
                        let mty: crate::cbordetver::cbor_det_int_kind =
                            crate::cbordetver::cbor_det_int_kind::UInt64;
                        let c3: crate::cbordetveraux::cbor_raw =
                            crate::cbordetver::cbor_det_mk_int64(mty, 0u64);
                        let res: crate::cbordetver::option__size_t =
                            crate::cbordetver::cbor_det_serialize(c3, out1);
                        let size1: usize =
                            match res
                            {
                                crate::cbordetver::option__size_t::None => 0usize,
                                crate::cbordetver::option__size_t::Some { v: r } => r,
                                _ => panic!("Incomplete pattern matching")
                            };
                        if size1 == 0usize
                        { false }
                        else
                        {
                            (&mut pcount)[0] = count0.wrapping_add(1u64);
                            (&mut psize)[0] = size.wrapping_add(size1);
                            true
                        }
                    }
                    else
                    { false };
                if res11
                {
                    let _letpattern2: (&[u8], (&[u8], (&[u8], (&[u8], (&[u8], &[u8]))))) = c21;
                    let c12: &[u8] = _letpattern2.0;
                    let c22: (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))) = _letpattern2.1;
                    let count1: u64 = (&pcount)[0];
                    let res12: bool =
                        if count1 < 18446744073709551615u64
                        {
                            let size: usize = (&psize)[0];
                            let _letpattern3: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                            let _out0: &[u8] = _letpattern3.0;
                            let out1: &mut [u8] = _letpattern3.1;
                            let len: usize = c12.len();
                            let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(33u64, len);
                            let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 33u64);
                            let size1: usize =
                                if lo_ok && hi_ok
                                {
                                    if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                    {
                                        let len1: usize = c12.len();
                                        let __anf0: bool =
                                            crate::cbordetveraux::sizet_lte_u64(
                                                len1,
                                                18446744073709551615u64
                                            );
                                        if __anf0
                                        {
                                            let mty: crate::cbordetver::cbor_det_string_kind =
                                                crate::cbordetver::cbor_det_string_kind::ByteString;
                                            let
                                            res:
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                crate::cbordetver::cbor_det_mk_string(mty, c12);
                                            let
                                            _letpattern4:
                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                            =
                                                res;
                                            let x: crate::cbordetveraux::cbor_raw =
                                                match _letpattern4
                                                {
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                    { v: c3 }
                                                    => c3,
                                                    _ => panic!("Incomplete pattern matching")
                                                };
                                            let ser: crate::cbordetver::option__size_t =
                                                crate::cbordetver::cbor_det_serialize(x, out1);
                                            match ser
                                            {
                                                crate::cbordetver::option__size_t::None => 0usize,
                                                crate::cbordetver::option__size_t::Some { v: sz } =>
                                                  sz,
                                                _ => panic!("Incomplete pattern matching")
                                            }
                                        }
                                        else
                                        { 0usize }
                                    }
                                    else
                                    {
                                        let len1: usize = c12.len();
                                        let __anf0: bool =
                                            crate::cbordetveraux::sizet_lte_u64(
                                                len1,
                                                18446744073709551615u64
                                            );
                                        if __anf0
                                        {
                                            let correct: bool =
                                                crate::cbordetver::cbor_impl_utf8_correct(c12);
                                            if correct
                                            {
                                                let mty: crate::cbordetver::cbor_det_string_kind =
                                                    if
                                                    crate::cbordetveraux::cbor_major_type_text_string
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                    {
                                                        crate::cbordetver::cbor_det_string_kind::ByteString
                                                    }
                                                    else
                                                    {
                                                        crate::cbordetver::cbor_det_string_kind::TextString
                                                    };
                                                let
                                                res:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    crate::cbordetver::cbor_det_mk_string(mty, c12);
                                                let
                                                _letpattern4:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    res;
                                                let x: crate::cbordetveraux::cbor_raw =
                                                    match _letpattern4
                                                    {
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                        { v: c3 }
                                                        => c3,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let ser: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(x, out1);
                                                match ser
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: sz }
                                                    => sz,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { 0usize }
                                        }
                                        else
                                        { 0usize }
                                    }
                                }
                                else
                                { 0usize };
                            if size1 == 0usize
                            { false }
                            else
                            {
                                (&mut pcount)[0] = count1.wrapping_add(1u64);
                                (&mut psize)[0] = size.wrapping_add(size1);
                                true
                            }
                        }
                        else
                        { false };
                    if res12
                    {
                        let _letpattern3: (&[u8], (&[u8], (&[u8], (&[u8], &[u8])))) = c22;
                        let c13: &[u8] = _letpattern3.0;
                        let c23: (&[u8], (&[u8], (&[u8], &[u8]))) = _letpattern3.1;
                        let count2: u64 = (&pcount)[0];
                        let res13: bool =
                            if count2 < 18446744073709551615u64
                            {
                                let size: usize = (&psize)[0];
                                let _letpattern4: (&mut [u8], &mut [u8]) = out.split_at_mut(size);
                                let _out0: &[u8] = _letpattern4.0;
                                let out1: &mut [u8] = _letpattern4.1;
                                let len: usize = c13.len();
                                let lo_ok: bool = crate::cbordetveraux::u64_lte_sizet(98u64, len);
                                let hi_ok: bool = crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                                let size1: usize =
                                    if lo_ok && hi_ok
                                    {
                                        if 2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                        {
                                            let len1: usize = c13.len();
                                            let __anf0: bool =
                                                crate::cbordetveraux::sizet_lte_u64(
                                                    len1,
                                                    18446744073709551615u64
                                                );
                                            if __anf0
                                            {
                                                let mty: crate::cbordetver::cbor_det_string_kind =
                                                    crate::cbordetver::cbor_det_string_kind::ByteString;
                                                let
                                                res:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    crate::cbordetver::cbor_det_mk_string(mty, c13);
                                                let
                                                _letpattern5:
                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                =
                                                    res;
                                                let x: crate::cbordetveraux::cbor_raw =
                                                    match _letpattern5
                                                    {
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                        { v: c3 }
                                                        => c3,
                                                        _ => panic!("Incomplete pattern matching")
                                                    };
                                                let ser: crate::cbordetver::option__size_t =
                                                    crate::cbordetver::cbor_det_serialize(x, out1);
                                                match ser
                                                {
                                                    crate::cbordetver::option__size_t::None =>
                                                      0usize,
                                                    crate::cbordetver::option__size_t::Some
                                                    { v: sz }
                                                    => sz,
                                                    _ => panic!("Incomplete pattern matching")
                                                }
                                            }
                                            else
                                            { 0usize }
                                        }
                                        else
                                        {
                                            let len1: usize = c13.len();
                                            let __anf0: bool =
                                                crate::cbordetveraux::sizet_lte_u64(
                                                    len1,
                                                    18446744073709551615u64
                                                );
                                            if __anf0
                                            {
                                                let correct: bool =
                                                    crate::cbordetver::cbor_impl_utf8_correct(c13);
                                                if correct
                                                {
                                                    let
                                                    mty: crate::cbordetver::cbor_det_string_kind
                                                    =
                                                        if
                                                        crate::cbordetveraux::cbor_major_type_text_string
                                                        ==
                                                        crate::cbordetveraux::cbor_major_type_byte_string
                                                        {
                                                            crate::cbordetver::cbor_det_string_kind::ByteString
                                                        }
                                                        else
                                                        {
                                                            crate::cbordetver::cbor_det_string_kind::TextString
                                                        };
                                                    let
                                                    res:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        crate::cbordetver::cbor_det_mk_string(
                                                            mty,
                                                            c13
                                                        );
                                                    let
                                                    _letpattern5:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        res;
                                                    let x: crate::cbordetveraux::cbor_raw =
                                                        match _letpattern5
                                                        {
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                            { v: c3 }
                                                            => c3,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let ser: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            x,
                                                            out1
                                                        );
                                                    match ser
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: sz }
                                                        => sz,
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                }
                                                else
                                                { 0usize }
                                            }
                                            else
                                            { 0usize }
                                        }
                                    }
                                    else
                                    { 0usize };
                                if size1 == 0usize
                                { false }
                                else
                                {
                                    (&mut pcount)[0] = count2.wrapping_add(1u64);
                                    (&mut psize)[0] = size.wrapping_add(size1);
                                    true
                                }
                            }
                            else
                            { false };
                        if res13
                        {
                            let _letpattern4: (&[u8], (&[u8], (&[u8], &[u8]))) = c23;
                            let c14: &[u8] = _letpattern4.0;
                            let c24: (&[u8], (&[u8], &[u8])) = _letpattern4.1;
                            let count3: u64 = (&pcount)[0];
                            let res14: bool =
                                if count3 < 18446744073709551615u64
                                {
                                    let size: usize = (&psize)[0];
                                    let _letpattern5: (&mut [u8], &mut [u8]) =
                                        out.split_at_mut(size);
                                    let _out0: &[u8] = _letpattern5.0;
                                    let out1: &mut [u8] = _letpattern5.1;
                                    let len: usize = c14.len();
                                    let lo_ok: bool =
                                        crate::cbordetveraux::u64_lte_sizet(98u64, len);
                                    let hi_ok: bool =
                                        crate::cbordetveraux::sizet_lte_u64(len, 98u64);
                                    let size1: usize =
                                        if lo_ok && hi_ok
                                        {
                                            if
                                            2u8 == crate::cbordetveraux::cbor_major_type_byte_string
                                            {
                                                let len1: usize = c14.len();
                                                let __anf0: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len1,
                                                        18446744073709551615u64
                                                    );
                                                if __anf0
                                                {
                                                    let
                                                    mty: crate::cbordetver::cbor_det_string_kind
                                                    =
                                                        crate::cbordetver::cbor_det_string_kind::ByteString;
                                                    let
                                                    res:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        crate::cbordetver::cbor_det_mk_string(
                                                            mty,
                                                            c14
                                                        );
                                                    let
                                                    _letpattern6:
                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                    =
                                                        res;
                                                    let x: crate::cbordetveraux::cbor_raw =
                                                        match _letpattern6
                                                        {
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                            { v: c3 }
                                                            => c3,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        };
                                                    let ser: crate::cbordetver::option__size_t =
                                                        crate::cbordetver::cbor_det_serialize(
                                                            x,
                                                            out1
                                                        );
                                                    match ser
                                                    {
                                                        crate::cbordetver::option__size_t::None =>
                                                          0usize,
                                                        crate::cbordetver::option__size_t::Some
                                                        { v: sz }
                                                        => sz,
                                                        _ => panic!("Incomplete pattern matching")
                                                    }
                                                }
                                                else
                                                { 0usize }
                                            }
                                            else
                                            {
                                                let len1: usize = c14.len();
                                                let __anf0: bool =
                                                    crate::cbordetveraux::sizet_lte_u64(
                                                        len1,
                                                        18446744073709551615u64
                                                    );
                                                if __anf0
                                                {
                                                    let correct: bool =
                                                        crate::cbordetver::cbor_impl_utf8_correct(
                                                            c14
                                                        );
                                                    if correct
                                                    {
                                                        let
                                                        mty: crate::cbordetver::cbor_det_string_kind
                                                        =
                                                            if
                                                            crate::cbordetveraux::cbor_major_type_text_string
                                                            ==
                                                            crate::cbordetveraux::cbor_major_type_byte_string
                                                            {
                                                                crate::cbordetver::cbor_det_string_kind::ByteString
                                                            }
                                                            else
                                                            {
                                                                crate::cbordetver::cbor_det_string_kind::TextString
                                                            };
                                                        let
                                                        res:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            crate::cbordetver::cbor_det_mk_string(
                                                                mty,
                                                                c14
                                                            );
                                                        let
                                                        _letpattern6:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            res;
                                                        let x: crate::cbordetveraux::cbor_raw =
                                                            match _letpattern6
                                                            {
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                { v: c3 }
                                                                => c3,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        let ser: crate::cbordetver::option__size_t =
                                                            crate::cbordetver::cbor_det_serialize(
                                                                x,
                                                                out1
                                                            );
                                                        match ser
                                                        {
                                                            crate::cbordetver::option__size_t::None
                                                            => 0usize,
                                                            crate::cbordetver::option__size_t::Some
                                                            { v: sz }
                                                            => sz,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        }
                                                    }
                                                    else
                                                    { 0usize }
                                                }
                                                else
                                                { 0usize }
                                            }
                                        }
                                        else
                                        { 0usize };
                                    if size1 == 0usize
                                    { false }
                                    else
                                    {
                                        (&mut pcount)[0] = count3.wrapping_add(1u64);
                                        (&mut psize)[0] = size.wrapping_add(size1);
                                        true
                                    }
                                }
                                else
                                { false };
                            if res14
                            {
                                let _letpattern5: (&[u8], (&[u8], &[u8])) = c24;
                                let c15: &[u8] = _letpattern5.0;
                                let c25: (&[u8], &[u8]) = _letpattern5.1;
                                let count4: u64 = (&pcount)[0];
                                let res15: bool =
                                    if count4 < 18446744073709551615u64
                                    {
                                        let size: usize = (&psize)[0];
                                        let _letpattern6: (&mut [u8], &mut [u8]) =
                                            out.split_at_mut(size);
                                        let _out0: &[u8] = _letpattern6.0;
                                        let out1: &mut [u8] = _letpattern6.1;
                                        let len: usize = c15.len();
                                        let lo_ok: bool =
                                            crate::cbordetveraux::u64_lte_sizet(1249u64, len);
                                        let hi_ok: bool =
                                            crate::cbordetveraux::sizet_lte_u64(len, 1249u64);
                                        let size1: usize =
                                            if lo_ok && hi_ok
                                            {
                                                if
                                                2u8
                                                ==
                                                crate::cbordetveraux::cbor_major_type_byte_string
                                                {
                                                    let len1: usize = c15.len();
                                                    let __anf0: bool =
                                                        crate::cbordetveraux::sizet_lte_u64(
                                                            len1,
                                                            18446744073709551615u64
                                                        );
                                                    if __anf0
                                                    {
                                                        let
                                                        mty: crate::cbordetver::cbor_det_string_kind
                                                        =
                                                            crate::cbordetver::cbor_det_string_kind::ByteString;
                                                        let
                                                        res:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            crate::cbordetver::cbor_det_mk_string(
                                                                mty,
                                                                c15
                                                            );
                                                        let
                                                        _letpattern7:
                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                        =
                                                            res;
                                                        let x: crate::cbordetveraux::cbor_raw =
                                                            match _letpattern7
                                                            {
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                { v: c3 }
                                                                => c3,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            };
                                                        let ser: crate::cbordetver::option__size_t =
                                                            crate::cbordetver::cbor_det_serialize(
                                                                x,
                                                                out1
                                                            );
                                                        match ser
                                                        {
                                                            crate::cbordetver::option__size_t::None
                                                            => 0usize,
                                                            crate::cbordetver::option__size_t::Some
                                                            { v: sz }
                                                            => sz,
                                                            _ =>
                                                              panic!("Incomplete pattern matching")
                                                        }
                                                    }
                                                    else
                                                    { 0usize }
                                                }
                                                else
                                                {
                                                    let len1: usize = c15.len();
                                                    let __anf0: bool =
                                                        crate::cbordetveraux::sizet_lte_u64(
                                                            len1,
                                                            18446744073709551615u64
                                                        );
                                                    if __anf0
                                                    {
                                                        let correct: bool =
                                                            crate::cbordetver::cbor_impl_utf8_correct(
                                                                c15
                                                            );
                                                        if correct
                                                        {
                                                            let
                                                            mty:
                                                            crate::cbordetver::cbor_det_string_kind
                                                            =
                                                                if
                                                                crate::cbordetveraux::cbor_major_type_text_string
                                                                ==
                                                                crate::cbordetveraux::cbor_major_type_byte_string
                                                                {
                                                                    crate::cbordetver::cbor_det_string_kind::ByteString
                                                                }
                                                                else
                                                                {
                                                                    crate::cbordetver::cbor_det_string_kind::TextString
                                                                };
                                                            let
                                                            res:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                crate::cbordetver::cbor_det_mk_string(
                                                                    mty,
                                                                    c15
                                                                );
                                                            let
                                                            _letpattern7:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                res;
                                                            let x: crate::cbordetveraux::cbor_raw =
                                                                match _letpattern7
                                                                {
                                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                    { v: c3 }
                                                                    => c3,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            let
                                                            ser: crate::cbordetver::option__size_t
                                                            =
                                                                crate::cbordetver::cbor_det_serialize(
                                                                    x,
                                                                    out1
                                                                );
                                                            match ser
                                                            {
                                                                crate::cbordetver::option__size_t::None
                                                                => 0usize,
                                                                crate::cbordetver::option__size_t::Some
                                                                { v: sz }
                                                                => sz,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                    else
                                                    { 0usize }
                                                }
                                            }
                                            else
                                            { 0usize };
                                        if size1 == 0usize
                                        { false }
                                        else
                                        {
                                            (&mut pcount)[0] = count4.wrapping_add(1u64);
                                            (&mut psize)[0] = size.wrapping_add(size1);
                                            true
                                        }
                                    }
                                    else
                                    { false };
                                if res15
                                {
                                    let _letpattern6: (&[u8], &[u8]) = c25;
                                    let c16: &[u8] = _letpattern6.0;
                                    let c26: &[u8] = _letpattern6.1;
                                    let count5: u64 = (&pcount)[0];
                                    let res16: bool =
                                        if count5 < 18446744073709551615u64
                                        {
                                            let size: usize = (&psize)[0];
                                            let _letpattern7: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size);
                                            let _out0: &[u8] = _letpattern7.0;
                                            let out1: &mut [u8] = _letpattern7.1;
                                            let len: usize = c16.len();
                                            let lo_ok: bool =
                                                crate::cbordetveraux::u64_lte_sizet(1952u64, len);
                                            let hi_ok: bool =
                                                crate::cbordetveraux::sizet_lte_u64(len, 1952u64);
                                            let size1: usize =
                                                if lo_ok && hi_ok
                                                {
                                                    if
                                                    2u8
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                    {
                                                        let len1: usize = c16.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let
                                                            mty:
                                                            crate::cbordetver::cbor_det_string_kind
                                                            =
                                                                crate::cbordetver::cbor_det_string_kind::ByteString;
                                                            let
                                                            res:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                crate::cbordetver::cbor_det_mk_string(
                                                                    mty,
                                                                    c16
                                                                );
                                                            let
                                                            _letpattern8:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                res;
                                                            let x: crate::cbordetveraux::cbor_raw =
                                                                match _letpattern8
                                                                {
                                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                    { v: c3 }
                                                                    => c3,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            let
                                                            ser: crate::cbordetver::option__size_t
                                                            =
                                                                crate::cbordetver::cbor_det_serialize(
                                                                    x,
                                                                    out1
                                                                );
                                                            match ser
                                                            {
                                                                crate::cbordetver::option__size_t::None
                                                                => 0usize,
                                                                crate::cbordetver::option__size_t::Some
                                                                { v: sz }
                                                                => sz,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                    else
                                                    {
                                                        let len1: usize = c16.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let correct: bool =
                                                                crate::cbordetver::cbor_impl_utf8_correct(
                                                                    c16
                                                                );
                                                            if correct
                                                            {
                                                                let
                                                                mty:
                                                                crate::cbordetver::cbor_det_string_kind
                                                                =
                                                                    if
                                                                    crate::cbordetveraux::cbor_major_type_text_string
                                                                    ==
                                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::ByteString
                                                                    }
                                                                    else
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::TextString
                                                                    };
                                                                let
                                                                res:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_mk_string(
                                                                        mty,
                                                                        c16
                                                                    );
                                                                let
                                                                _letpattern8:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    res;
                                                                let
                                                                x: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    match _letpattern8
                                                                    {
                                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                        { v: c3 }
                                                                        => c3,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let
                                                                ser:
                                                                crate::cbordetver::option__size_t
                                                                =
                                                                    crate::cbordetver::cbor_det_serialize(
                                                                        x,
                                                                        out1
                                                                    );
                                                                match ser
                                                                {
                                                                    crate::cbordetver::option__size_t::None
                                                                    => 0usize,
                                                                    crate::cbordetver::option__size_t::Some
                                                                    { v: sz }
                                                                    => sz,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                }
                                                            }
                                                            else
                                                            { 0usize }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                }
                                                else
                                                { 0usize };
                                            if size1 == 0usize
                                            { false }
                                            else
                                            {
                                                (&mut pcount)[0] = count5.wrapping_add(1u64);
                                                (&mut psize)[0] = size.wrapping_add(size1);
                                                true
                                            }
                                        }
                                        else
                                        { false };
                                    if res16
                                    {
                                        let count6: u64 = (&pcount)[0];
                                        if count6 < 18446744073709551615u64
                                        {
                                            let size: usize = (&psize)[0];
                                            let _letpattern7: (&mut [u8], &mut [u8]) =
                                                out.split_at_mut(size);
                                            let _out0: &[u8] = _letpattern7.0;
                                            let out1: &mut [u8] = _letpattern7.1;
                                            let len: usize = c26.len();
                                            let lo_ok: bool =
                                                crate::cbordetveraux::u64_lte_sizet(3309u64, len);
                                            let hi_ok: bool =
                                                crate::cbordetveraux::sizet_lte_u64(len, 3309u64);
                                            let size1: usize =
                                                if lo_ok && hi_ok
                                                {
                                                    if
                                                    2u8
                                                    ==
                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                    {
                                                        let len1: usize = c26.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let
                                                            mty:
                                                            crate::cbordetver::cbor_det_string_kind
                                                            =
                                                                crate::cbordetver::cbor_det_string_kind::ByteString;
                                                            let
                                                            res:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                crate::cbordetver::cbor_det_mk_string(
                                                                    mty,
                                                                    c26
                                                                );
                                                            let
                                                            _letpattern8:
                                                            crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                            =
                                                                res;
                                                            let x: crate::cbordetveraux::cbor_raw =
                                                                match _letpattern8
                                                                {
                                                                    crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                    { v: c3 }
                                                                    => c3,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                };
                                                            let
                                                            ser: crate::cbordetver::option__size_t
                                                            =
                                                                crate::cbordetver::cbor_det_serialize(
                                                                    x,
                                                                    out1
                                                                );
                                                            match ser
                                                            {
                                                                crate::cbordetver::option__size_t::None
                                                                => 0usize,
                                                                crate::cbordetver::option__size_t::Some
                                                                { v: sz }
                                                                => sz,
                                                                _ =>
                                                                  panic!(
                                                                      "Incomplete pattern matching"
                                                                  )
                                                            }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                    else
                                                    {
                                                        let len1: usize = c26.len();
                                                        let __anf0: bool =
                                                            crate::cbordetveraux::sizet_lte_u64(
                                                                len1,
                                                                18446744073709551615u64
                                                            );
                                                        if __anf0
                                                        {
                                                            let correct: bool =
                                                                crate::cbordetver::cbor_impl_utf8_correct(
                                                                    c26
                                                                );
                                                            if correct
                                                            {
                                                                let
                                                                mty:
                                                                crate::cbordetver::cbor_det_string_kind
                                                                =
                                                                    if
                                                                    crate::cbordetveraux::cbor_major_type_text_string
                                                                    ==
                                                                    crate::cbordetveraux::cbor_major_type_byte_string
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::ByteString
                                                                    }
                                                                    else
                                                                    {
                                                                        crate::cbordetver::cbor_det_string_kind::TextString
                                                                    };
                                                                let
                                                                res:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    crate::cbordetver::cbor_det_mk_string(
                                                                        mty,
                                                                        c26
                                                                    );
                                                                let
                                                                _letpattern8:
                                                                crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw
                                                                =
                                                                    res;
                                                                let
                                                                x: crate::cbordetveraux::cbor_raw
                                                                =
                                                                    match _letpattern8
                                                                    {
                                                                        crate::cbordetver::option__CBOR_Pulse_Raw_Type_cbor_raw::Some
                                                                        { v: c3 }
                                                                        => c3,
                                                                        _ =>
                                                                          panic!(
                                                                              "Incomplete pattern matching"
                                                                          )
                                                                    };
                                                                let
                                                                ser:
                                                                crate::cbordetver::option__size_t
                                                                =
                                                                    crate::cbordetver::cbor_det_serialize(
                                                                        x,
                                                                        out1
                                                                    );
                                                                match ser
                                                                {
                                                                    crate::cbordetver::option__size_t::None
                                                                    => 0usize,
                                                                    crate::cbordetver::option__size_t::Some
                                                                    { v: sz }
                                                                    => sz,
                                                                    _ =>
                                                                      panic!(
                                                                          "Incomplete pattern matching"
                                                                      )
                                                                }
                                                            }
                                                            else
                                                            { 0usize }
                                                        }
                                                        else
                                                        { 0usize }
                                                    }
                                                }
                                                else
                                                { 0usize };
                                            if size1 == 0usize
                                            { false }
                                            else
                                            {
                                                (&mut pcount)[0] = count6.wrapping_add(1u64);
                                                (&mut psize)[0] = size.wrapping_add(size1);
                                                true
                                            }
                                        }
                                        else
                                        { false }
                                    }
                                    else
                                    { false }
                                }
                                else
                                { false }
                            }
                            else
                            { false }
                        }
                        else
                        { false }
                    }
                    else
                    { false }
                }
                else
                { false }
            }
            else
            { false }
        };
    if res
    {
        let size: usize = (&psize)[0];
        let count: u64 = (&pcount)[0];
        crate::cbordetver::cbor_det_serialize_array(count, out, size)
    }
    else
    { 0usize }
}

#[derive(PartialEq, Clone, Copy)]
pub enum option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t· <'a>
{
    None,
    Some { v: (initkex <'a>, &'a [u8]) }
}

pub fn validate_and_parse_initkex <'a>(s: &'a [u8]) ->
    option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t·
    <'a>
{
    let
    q:
    crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·
    =
        crate::cbordetver::cbor_det_parse(s);
    match q
    {
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::None
        => option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t·::None,
        crate::cbordetver::option__·CBOR_Pulse_Raw_Type_cbor_raw···Pulse_Lib_Slice_slice·uint8_t·::Some
        { v: rlrem }
        =>
          {
              let _letpattern: (crate::cbordetveraux::cbor_raw, &[u8]) = rlrem;
              let rl: crate::cbordetveraux::cbor_raw = _letpattern.0;
              let rem: &[u8] = _letpattern.1;
              let test: bool = validate_initkex(rl);
              if test
              {
                  let x: initkex = parse_initkex(rl);
                  option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t·::Some
                  { v: (x,rem) }
              }
              else
              { option__·Transport_initkex···Pulse_Lib_Slice_slice·uint8_t·::None }
          },
        _ => panic!("Incomplete pattern matching")
    }
}
