//! Sys-bindings to `libkstat`.

// Copyright 2021 Oxide Computer Company
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![allow(non_camel_case_types)]

use crate::Error;
use libc::{c_char, c_int, c_longlong, c_uchar, c_uint, c_ulonglong, c_void, size_t};
use std::convert::TryFrom;
use std::ffi::CStr;
use std::fmt::{self, Debug};
use std::mem::size_of;

// Rust FFI equivalent to `libkstat`'s `kstat_ctl_t`.
#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_ctl_t {
    pub kc_chain_id: kid_t,
    pub kc_chain: *mut kstat_t,
    pub kc_kd: c_int,
}

// Type alias for system high-resolution time, expressed in nanoseconds.
pub type hrtime_t = c_longlong;

// Type alias for kstat identifiers.
pub type kid_t = c_int;

// Length of string array fields
pub const KSTAT_STRLEN: usize = 31;

// Kstat types
pub const KSTAT_TYPE_RAW: u8 = 0;
pub const KSTAT_TYPE_NAMED: u8 = 1;
pub const KSTAT_TYPE_INTR: u8 = 2;
pub const KSTAT_TYPE_IO: u8 = 3;
pub const KSTAT_TYPE_TIMER: u8 = 4;

// Rust FFI equivalent to `libkstat`'s `kstat_t`.
#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_t {
    pub ks_crtime: hrtime_t,
    pub ks_next: *mut kstat_t,
    pub ks_kid: kid_t,
    pub ks_module: [c_char; KSTAT_STRLEN],
    _ks_resv: c_uchar,
    pub ks_instance: c_int,
    pub ks_name: [c_char; KSTAT_STRLEN],
    pub ks_type: c_uchar,
    pub ks_class: [c_char; KSTAT_STRLEN],
    pub ks_flags: c_char,
    pub ks_data: *mut c_void,
    pub ks_ndata: c_uint,
    pub ks_data_size: size_t,
    pub ks_snaptime: hrtime_t,
}

// Named kstat data types
pub const KSTAT_DATA_CHAR: u8 = 0;
pub const KSTAT_DATA_INT32: u8 = 1;
pub const KSTAT_DATA_UINT32: u8 = 2;
pub const KSTAT_DATA_INT64: u8 = 3;
pub const KSTAT_DATA_UINT64: u8 = 4;
pub const KSTAT_DATA_STRING: u8 = 9;

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_named_t {
    pub name: [c_char; KSTAT_STRLEN],
    pub data_type: c_uchar,
    pub value: NamedDataUnion,
}

#[derive(Copy, Clone)]
#[repr(C)]
pub union NamedDataUnion {
    pub charc: [c_uchar; 16],
    pub str: NamedStr,
    pub i32: i32,
    pub ui32: u32,
    pub i64: i64,
    pub ui64: u64,
}

impl Debug for NamedDataUnion {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "NamedDataUnion(0x{:#x?})", self as *const _)
    }
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct NamedStr {
    pub addr: *const c_char,
    pub len: u32,
}

impl TryFrom<&NamedStr> for &str {
    type Error = Error;
    fn try_from(n: &NamedStr) -> Result<Self, Self::Error> {
        if n.addr.is_null() {
            Err(Error::NullData)
        } else {
            unsafe { CStr::from_ptr(n.addr) }
                .to_str()
                .map_err(|_| Error::InvalidString)
        }
    }
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_intr_t {
    pub intr_hard: u32,
    pub intr_soft: u32,
    pub intr_watchdog: u32,
    pub intr_spurious: u32,
    pub intr_multisvc: u32,
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_timer_t {
    pub name: [c_char; KSTAT_STRLEN],
    _resv: c_uchar,
    pub num_events: c_ulonglong,
    pub elapsed_time: hrtime_t,
    pub min_time: hrtime_t,
    pub max_time: hrtime_t,
    pub start_time: hrtime_t,
    pub stop_time: hrtime_t,
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct kstat_io_t {
    pub nread: c_ulonglong,
    pub nwritten: c_ulonglong,
    pub reads: c_uint,
    pub writes: c_uint,
    pub wtime: hrtime_t,
    pub wlentime: hrtime_t,
    pub wlastupdate: hrtime_t,
    pub rtime: hrtime_t,
    pub rlentime: hrtime_t,
    pub rlastupdate: hrtime_t,
    pub wcnt: c_uint,
    pub rcnt: c_uint,
}

// Read a list of raw kstat data items from the given kstat.
pub fn kstat_data_raw(kstat: &kstat_t) -> Vec<&[u8]> {
    let n_data: usize = kstat.ks_ndata as _;
    if n_data == 0 {
        Vec::new()
    } else {
        let item_size = kstat.ks_data_size / n_data;
        let mut start = kstat.ks_data as *const u8;
        let mut out = Vec::with_capacity(n_data);
        for _ in 0..kstat.ks_ndata {
            out.push(unsafe { std::slice::from_raw_parts(start, item_size) });
            start = unsafe { start.offset(item_size as _) };
        }
        out
    }
}

// Read an IO kstat from the given kstat.
pub fn kstat_data_io(kstat: &kstat_t) -> &kstat_io_t {
    assert!(kstat.ks_ndata == 1);
    assert!(kstat.ks_data_size == size_of::<kstat_io_t>());
    unsafe { (kstat.ks_data as *const kstat_io_t).as_ref() }.unwrap()
}

// Read an interrupt kstat from the given kstat.
pub fn kstat_data_intr(kstat: &kstat_t) -> &kstat_intr_t {
    assert!(kstat.ks_ndata == 1);
    assert!(kstat.ks_data_size == size_of::<kstat_intr_t>());
    unsafe { (kstat.ks_data as *const kstat_intr_t).as_ref() }.unwrap()
}

// Read a list of timer kstats from the given kstat.
pub fn kstat_data_timer(kstat: &kstat_t) -> &[kstat_timer_t] {
    assert!(kstat.ks_data_size == (kstat.ks_ndata as usize * size_of::<kstat_timer_t>()));
    unsafe { std::slice::from_raw_parts(kstat.ks_ndata as *const _, kstat.ks_ndata as _) }
}

// Read a list of name-value kstats from the given kstat
pub fn kstat_data_named(kstat: &kstat_t) -> &[kstat_named_t] {
    let reported_count = kstat.ks_ndata as usize;
    let actual_count = kstat.ks_data_size as usize / size_of::<kstat_named_t>();
    let count = reported_count.min(actual_count);
    unsafe { std::slice::from_raw_parts(kstat.ks_data as *const _, count) }
}

#[link(name = "kstat")]
extern "C" {
    pub fn kstat_open() -> *mut kstat_ctl_t;
    pub fn kstat_close(_: *mut kstat_ctl_t) -> i32;
    pub fn kstat_read(_: *mut kstat_ctl_t, _: *mut kstat_t, _: *mut c_void) -> kid_t;
    pub fn kstat_chain_update(_: *mut kstat_ctl_t) -> kid_t;
}

// Helper to convert a Kstat string array to a &str.
pub(crate) fn array_to_cstr<'a>(s: &'a [c_char; KSTAT_STRLEN]) -> Result<&'a str, Error> {
    unsafe { CStr::from_ptr(s.as_ptr() as *const _) }
        .to_str()
        .map_err(|_| Error::InvalidString)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_kstat_ctl() {
        let ctl = unsafe { kstat_open() };
        assert!(!ctl.is_null());
        assert_eq!(unsafe { kstat_close(ctl) }, 0);
    }

    /*
    #[test]
    fn foo() {
        let ctl = unsafe { kstat_open() };
        let mut kstat = unsafe { (*ctl).kc_chain };
        while !kstat.is_null() {
            let kid = unsafe { kstat_read(ctl, kstat, std::ptr::null_mut()) };
            let ks = unsafe { kstat.as_ref() }.unwrap();
            if kid == -1 {
                println!("ERR: {}", std::io::Error::last_os_error());
            } else {
                let ty = Type::try_from(ks.ks_type).unwrap();
                if matches!(ty, Type::Io) {
                    let data = Io::from(kstat_data_io(ks));
                    println!("name: {}\n{:#?}", array_to_cstr(&ks.ks_name).unwrap(), data);
                } else if matches!(ty, Type::Named) {
                    let data = kstat_data_named(ks).iter().map(|d| Named::try_from(d).unwrap()).collect::<Vec<_>>();
                    println!("{:#?}", data);
                }
            }
            kstat = ks.ks_next;
        }
    }
    */
}
