//! Rust library for interfacing with illumos kernel statistics, `libkstat`.
//!
//! The illumos `kstat` system is a kernel module for exporting data about the system to user
//! processes. Users create a control handle to the system with [`Ctl::new`], which gives them
//! access to the statistics exported by their system.
//!
//! Individual statistics are represented by the [`Kstat`] type, which includes information about
//! the type of data, when it was created or last updated, and the actual data itself. The `Ctl`
//! handle maintains a linked list of `Kstat` objects, which users may walk with the [`Ctl::iter`]
//! method.
//!
//! Each kstat is identified by a module, an instance number, and a name. In addition, the data may
//! be of several different types, such as name/value pairs or interrupt statistics. These types
//! are captured by the [`Data`] enum, which can be read and returned by using the [`Ctl::read`]
//! method.

// Copyright 2023 Oxide Computer Company
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

use std::cmp::Ord;
use std::cmp::Ordering;
use std::cmp::PartialOrd;
use std::convert::TryFrom;
use std::marker::PhantomData;
use thiserror::Error;
use std::collections::BTreeMap;
use std::cell::Cell;
use std::cell::RefCell;

mod sys;

/// Kinds of errors returned by the library.
#[derive(Debug, Error)]
pub enum Error {
    /// An attempt to convert a byte-string to a Rust string failed.
    #[error("The byte-string is not a valid Rust string")]
    InvalidString,

    /// Encountered an invalid kstat type.
    #[error("Kstat type {0} is invalid")]
    InvalidType(u8),

    /// Encountered an invalid named kstat data type.
    #[error("The named kstat data type {0} is invalid")]
    InvalidNamedType(u8),

    /// Encountered a null pointer or empty data.
    #[error("A null pointer or empty kstat was encountered")]
    NullData,

    /// Error bubbled up from operating on `libkstat`.
    #[error(transparent)]
    Io(#[from] std::io::Error),

    #[error("Tracking function matches zero kstats")]
    NoTrackedKstats,

    #[error("Invalid tracking ID")]
    InvalidTrackingId,
}

/// An ID used to refer to tracked kernel statistics.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TrackingId(u64);

// A set of tracked kstats, those matching a tracking function.
#[derive(Clone, Debug)]
#[allow(dead_code)]
struct TrackedKstats<'a> {
    // The ID of these tracked stats.
    id: TrackingId,
    // A function returning true for kstats that should be tracked
    track_fn: fn(Kstat<'a>) -> bool,
    // The current set of tracked stats.
    kstats: Vec<Kstat<'a>>,
}

/// `Ctl` is a handle to the kstat library.
///
/// Users instantiate a control handle and access the kstat's it contains, for example via the
/// [`Ctl::iter`] method.
#[derive(Debug)]
pub struct Ctl<'a> {
    ctl: *mut sys::kstat_ctl_t,
    tracking_id: Cell<TrackingId>,
    tracked_kstats: RefCell<BTreeMap<TrackingId, TrackedKstats<'a>>>,
}

/// The `Ctl` wraps a raw pointer allocated by the `libkstat(3KSTAT)` library.
/// This itself isn't thread-safe, but doesn't refer to any thread-local state.
/// So it's safe to send across threads.
unsafe impl Send for Ctl<'_> {}

impl<'a> Ctl<'a> {
    /// Create a new `Ctl`.
    pub fn new() -> Result<Self, Error> {
        let ctl = unsafe { sys::kstat_open() };
        if ctl.is_null() {
            Err(std::io::Error::last_os_error().into())
        } else {
            Ok(Ctl { ctl, tracking_id: Cell::new(TrackingId(0)), tracked_kstats: RefCell::new(BTreeMap::new()) })
        }
    }

    /// Synchronize this `Ctl` with the kernel's view of the data.
    ///
    /// A `Ctl` is really a snapshot of the kernel's internal list of kstats. This method consumes
    /// and updates a control object, bringing it into sync with the kernel's copy.
    pub fn update(self) -> Result<Self, Error> {
        let kid = unsafe { sys::kstat_chain_update(self.ctl) };
        if kid == -1 {
            return Err(std::io::Error::last_os_error().into());
        } else if kid > 0 {
            for tracked in self.tracked_kstats.borrow_mut().values_mut() {
                tracked.kstats.clear();
                for k in self.iter() {
                    if (tracked.track_fn)(k) {
                        tracked.kstats.push(k);
                    }
                }
            }
        }
        Ok(self)
    }

    /// Return an iterator over the [`Kstat`]s in `self`.
    ///
    /// Note that this will only return `Kstat`s which are successfully read. For example, it will
    /// ignore those with non-UTF-8 names.
    pub fn iter<'b>(&self) -> Iter<'b>
    where
        'a: 'b
    {
        Iter {
            kstat: unsafe { (*self.ctl).kc_chain },
            _d: PhantomData,
        }
    }

    /// Request tracking for kstats which return `true` from a closure.
    pub fn track(&mut self, track_fn: fn(Kstat<'a>) -> bool) -> Result<TrackingId, Error> {
        let kstats: Vec<_> = self.iter().filter(|k| track_fn(*k)).collect();
        if kstats.is_empty() {
            return Err(Error::NoTrackedKstats);
        }
        let id = self.tracking_id.get();
        self.tracking_id.set(TrackingId(id.0 + 1));
        let tracked_kstats = TrackedKstats {
            id,
            track_fn,
            kstats,
        };
        assert!(self.tracked_kstats.borrow_mut().insert(id, tracked_kstats).is_none());
        Ok(id)
    }

    /// Stop tracking the kstats matching the provided ID.
    pub fn stop_tracking(&mut self, id: &TrackingId) {
        self.tracked_kstats.borrow_mut().remove(id);
    }

    /// Return the set of tracked stats matching the provided ID.
    pub fn fetch_tracked(&self, id: &TrackingId) -> Result<Vec<Kstat<'a>>, Error> {
        match self.tracked_kstats.borrow().get(id) {
            None => Err(Error::InvalidTrackingId),
            Some(s) => Ok(s.kstats.clone()),
        }
    }

    /// Read a [`Kstat`], returning the data for it.
    pub fn read(&self, kstat: &mut Kstat<'a>) -> Result<Data<'a>, Error> {
        kstat.read(self.ctl)?;
        kstat.data()
    }

    /// Find [`Kstat`]s by module, instance, and/or name.
    ///
    /// If a field is `None`, any matching `Kstat` is returned.
    pub fn filter(
        &self,
        module: Option<&'a str>,
        instance: Option<i32>,
        name: Option<&'a str>,
    ) -> impl Iterator<Item = Kstat<'a>> + 'a {
        self.iter().filter_map(move |kstat| {
            fn should_include<T>(inner: &T, cmp: &Option<T>) -> bool
            where
                T: PartialEq,
            {
                if let Some(cmp) = cmp {
                    inner == cmp
                } else {
                    true // Include if this comparator is None
                }
            }
            let include = should_include(&kstat.ks_module, &module)
                && should_include(&kstat.ks_instance, &instance)
                && should_include(&kstat.ks_name, &name);
            if include {
                Some(kstat)
            } else {
                None
            }
        })
    }
}

impl Drop for Ctl<'_> {
    fn drop(&mut self) {
        unsafe {
            sys::kstat_close(self.ctl);
        }
    }
}

/// An iterator over all [`Kstat`] on a chain.
#[derive(Debug)]
pub struct Iter<'a> {
    kstat: *mut sys::kstat_t,
    _d: PhantomData<&'a ()>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = Kstat<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(ks) = unsafe { self.kstat.as_ref() } {
                self.kstat = unsafe { *self.kstat }.ks_next;
                if let Ok(ks) = Kstat::try_from(ks) {
                    break Some(ks);
                }
                // continue to next kstat
            } else {
                break None;
            }
        }
    }
}

unsafe impl<'a> Send for Iter<'a> {}

/// `Kstat` represents a single kernel statistic.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Kstat<'a> {
    /// The creation time of the stat, in nanoseconds.
    pub ks_crtime: i64,
    /// The time of the last update, in nanoseconds.
    pub ks_snaptime: i64,
    /// The module of the kstat.
    pub ks_module: &'a str,
    /// The instance of the kstat.
    pub ks_instance: i32,
    /// The name of the kstat.
    pub ks_name: &'a str,
    /// The type of the kstat.
    pub ks_type: Type,
    /// The class of the kstat.
    pub ks_class: &'a str,
    ks: *mut sys::kstat_t,
}

impl<'a> PartialOrd for Kstat<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(
            self.ks_class
                .cmp(other.ks_class)
                .then_with(|| self.ks_module.cmp(other.ks_module))
                .then_with(|| self.ks_instance.cmp(&other.ks_instance))
                .then_with(|| self.ks_name.cmp(other.ks_name))
                .then_with(|| self.ks_class.cmp(other.ks_name)),
        )
    }
}

impl<'a> Ord for Kstat<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

unsafe impl<'a> Send for Kstat<'a> {}

impl<'a> Kstat<'a> {
    fn read(&mut self, ctl: *mut sys::kstat_ctl_t) -> Result<(), Error> {
        if unsafe { sys::kstat_read(ctl, self.ks, std::ptr::null_mut()) } == -1 {
            Err(std::io::Error::last_os_error().into())
        } else {
            self.ks_snaptime = unsafe { (*self.ks).ks_snaptime };
            Ok(())
        }
    }

    fn data(&self) -> Result<Data<'a>, Error> {
        let ks = unsafe { self.ks.as_ref() }.ok_or_else(|| Error::NullData)?;
        match self.ks_type {
            Type::Raw => Ok(Data::Raw(sys::kstat_data_raw(ks))),
            Type::Named => Ok(Data::Named(
                sys::kstat_data_named(ks)
                    .iter()
                    .map(Named::try_from)
                    .collect::<Result<_, _>>()?,
            )),
            Type::Intr => Ok(Data::Intr(Intr::from(sys::kstat_data_intr(ks)))),
            Type::Io => Ok(Data::Io(Io::from(sys::kstat_data_io(ks)))),
            Type::Timer => Ok(Data::Timer(
                sys::kstat_data_timer(ks)
                    .iter()
                    .map(Timer::try_from)
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
}

impl<'a> TryFrom<&'a sys::kstat_t> for Kstat<'a> {
    type Error = Error;
    fn try_from(k: &'a sys::kstat_t) -> Result<Self, Self::Error> {
        Ok(Kstat {
            ks_crtime: k.ks_crtime,
            ks_snaptime: k.ks_snaptime,
            ks_module: sys::array_to_cstr(&k.ks_module)?,
            ks_instance: k.ks_instance,
            ks_name: sys::array_to_cstr(&k.ks_name)?,
            ks_type: Type::try_from(k.ks_type)?,
            ks_class: sys::array_to_cstr(&k.ks_name)?,
            ks: k as *const _ as *mut _,
        })
    }
}

impl<'a> TryFrom<&'a *mut sys::kstat_t> for Kstat<'a> {
    type Error = Error;
    fn try_from(k: &'a *mut sys::kstat_t) -> Result<Self, Self::Error> {
        if let Some(k) = unsafe { k.as_ref() } {
            Kstat::try_from(k)
        } else {
            Err(Error::NullData)
        }
    }
}

/// The type of a kstat.
#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub enum Type {
    Raw,
    Named,
    Intr,
    Io,
    Timer,
}

impl TryFrom<u8> for Type {
    type Error = Error;
    fn try_from(t: u8) -> Result<Self, Self::Error> {
        match t {
            sys::KSTAT_TYPE_RAW => Ok(Type::Raw),
            sys::KSTAT_TYPE_NAMED => Ok(Type::Named),
            sys::KSTAT_TYPE_INTR => Ok(Type::Intr),
            sys::KSTAT_TYPE_IO => Ok(Type::Io),
            sys::KSTAT_TYPE_TIMER => Ok(Type::Timer),
            other => Err(Self::Error::InvalidType(other)),
        }
    }
}

/// The data type of a single name/value pair of a named kstat.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum NamedType {
    Char,
    Int32,
    UInt32,
    Int64,
    UInt64,
    String,
}

impl TryFrom<u8> for NamedType {
    type Error = Error;
    fn try_from(t: u8) -> Result<Self, Self::Error> {
        match t {
            sys::KSTAT_DATA_CHAR => Ok(NamedType::Char),
            sys::KSTAT_DATA_INT32 => Ok(NamedType::Int32),
            sys::KSTAT_DATA_UINT32 => Ok(NamedType::UInt32),
            sys::KSTAT_DATA_INT64 => Ok(NamedType::Int64),
            sys::KSTAT_DATA_UINT64 => Ok(NamedType::UInt64),
            sys::KSTAT_DATA_STRING => Ok(NamedType::String),
            other => Err(Self::Error::InvalidNamedType(other)),
        }
    }
}

/// Data from a single kstat.
#[derive(Clone, Debug)]
pub enum Data<'a> {
    Raw(Vec<&'a [u8]>),
    Named(Vec<Named<'a>>),
    Intr(Intr),
    Io(Io),
    Timer(Vec<Timer<'a>>),
    Null,
}

/// An I/O kernel statistic
#[derive(Debug, Clone, Copy)]
pub struct Io {
    pub nread: u64,
    pub nwritten: u64,
    pub reads: u32,
    pub writes: u32,
    pub wtime: i64,
    pub wlentime: i64,
    pub wlastupdate: i64,
    pub rtime: i64,
    pub rlentime: i64,
    pub rlastupdate: i64,
    pub wcnt: u32,
    pub rcnt: u32,
}

impl From<&sys::kstat_io_t> for Io {
    fn from(k: &sys::kstat_io_t) -> Self {
        Io {
            nread: k.nread,
            nwritten: k.nwritten,
            reads: k.reads,
            writes: k.writes,
            wtime: k.wtime,
            wlentime: k.wlentime,
            wlastupdate: k.wlastupdate,
            rtime: k.rtime,
            rlentime: k.rlentime,
            rlastupdate: k.rlastupdate,
            wcnt: k.wcnt,
            rcnt: k.rcnt,
        }
    }
}

impl TryFrom<&*const sys::kstat_io_t> for Io {
    type Error = Error;
    fn try_from(k: &*const sys::kstat_io_t) -> Result<Self, Self::Error> {
        if let Some(k) = unsafe { k.as_ref() } {
            Ok(Io::from(k))
        } else {
            Err(Error::NullData)
        }
    }
}

/// A timer kernel statistic.
#[derive(Debug, Copy, Clone)]
pub struct Timer<'a> {
    pub name: &'a str,
    pub num_events: usize,
    pub elapsed_time: i64,
    pub min_time: i64,
    pub max_time: i64,
    pub start_time: i64,
    pub stop_time: i64,
}

impl<'a> TryFrom<&'a sys::kstat_timer_t> for Timer<'a> {
    type Error = Error;
    fn try_from(k: &'a sys::kstat_timer_t) -> Result<Self, Self::Error> {
        Ok(Self {
            name: sys::array_to_cstr(&k.name)?,
            num_events: k.num_events as _,
            elapsed_time: k.elapsed_time,
            min_time: k.min_time,
            max_time: k.max_time,
            start_time: k.start_time,
            stop_time: k.stop_time,
        })
    }
}

impl<'a> TryFrom<&'a *const sys::kstat_timer_t> for Timer<'a> {
    type Error = Error;
    fn try_from(k: &'a *const sys::kstat_timer_t) -> Result<Self, Self::Error> {
        if let Some(k) = unsafe { k.as_ref() } {
            Timer::try_from(k)
        } else {
            Err(Error::NullData)
        }
    }
}

/// Interrupt kernel statistic.
#[derive(Debug, Copy, Clone)]
pub struct Intr {
    pub hard: u32,
    pub soft: u32,
    pub watchdog: u32,
    pub spurious: u32,
    pub multisvc: u32,
}

impl From<&sys::kstat_intr_t> for Intr {
    fn from(k: &sys::kstat_intr_t) -> Self {
        Self {
            hard: k.intr_hard,
            soft: k.intr_soft,
            watchdog: k.intr_watchdog,
            spurious: k.intr_spurious,
            multisvc: k.intr_multisvc,
        }
    }
}

impl TryFrom<&*const sys::kstat_intr_t> for Intr {
    type Error = Error;
    fn try_from(k: &*const sys::kstat_intr_t) -> Result<Self, Self::Error> {
        if let Some(k) = unsafe { k.as_ref() } {
            Ok(Intr::from(k))
        } else {
            Err(Error::NullData)
        }
    }
}

/// A name/value data element from a named kernel statistic.
#[derive(Clone, Debug)]
pub struct Named<'a> {
    pub name: &'a str,
    pub value: NamedData<'a>,
}

impl<'a> Named<'a> {
    /// Return the data type of a named kernel statistic.
    pub fn data_type(&self) -> NamedType {
        self.value.data_type()
    }
}

/// The value part of a name-value kernel statistic.
#[derive(Clone, Debug)]
pub enum NamedData<'a> {
    Char(&'a [u8]),
    Int32(i32),
    UInt32(u32),
    Int64(i64),
    UInt64(u64),
    String(&'a str),
}

impl<'a> NamedData<'a> {
    /// Return the data type of a named kernel statistic.
    pub fn data_type(&self) -> NamedType {
        match self {
            NamedData::Char(_) => NamedType::Char,
            NamedData::Int32(_) => NamedType::Int32,
            NamedData::UInt32(_) => NamedType::UInt32,
            NamedData::Int64(_) => NamedType::Int64,
            NamedData::UInt64(_) => NamedType::UInt64,
            NamedData::String(_) => NamedType::String,
        }
    }
}

impl<'a> TryFrom<&'a sys::kstat_named_t> for Named<'a> {
    type Error = Error;
    fn try_from(k: &'a sys::kstat_named_t) -> Result<Self, Self::Error> {
        let name = sys::array_to_cstr(&k.name)?;
        match NamedType::try_from(k.data_type)? {
            NamedType::Char => {
                let slice = unsafe {
                    let p = k.value.charc.as_ptr() as *const u8;
                    let len = k.value.charc.len();
                    std::slice::from_raw_parts(p, len)
                };
                Ok(Named {
                    name,
                    value: NamedData::Char(slice),
                })
            }
            NamedType::Int32 => Ok(Named {
                name,
                value: NamedData::Int32(unsafe { k.value.i32 }),
            }),
            NamedType::UInt32 => Ok(Named {
                name,
                value: NamedData::UInt32(unsafe { k.value.ui32 }),
            }),
            NamedType::Int64 => Ok(Named {
                name,
                value: NamedData::Int64(unsafe { k.value.i64 }),
            }),

            NamedType::UInt64 => Ok(Named {
                name,
                value: NamedData::UInt64(unsafe { k.value.ui64 }),
            }),
            NamedType::String => {
                let s = (&unsafe { k.value.str }).try_into()?;
                Ok(Named {
                    name,
                    value: NamedData::String(s),
                })
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn basic_test() {
        let ctl = Ctl::new().expect("Failed to create kstat control");
        for mut kstat in ctl.iter() {
            match ctl.read(&mut kstat) {
                Ok(_) => {}
                Err(e) => {
                    println!("{}", e);
                }
            }
        }
    }

    #[test]
    fn compare_with_kstat_cli() {
        let ctl = Ctl::new().expect("Failed to create kstat control");
        let mut kstat = ctl
            .filter(Some("cpu_info"), Some(0), Some("cpu_info0"))
            .next()
            .expect("Failed to find kstat cpu_info:0:cpu_info0");
        if let Data::Named(data) = ctl.read(&mut kstat).expect("Failed to read kstat") {
            let mut items = BTreeMap::new();
            for item in data.iter() {
                items.insert(item.name, item);
            }
            let out = subprocess::Exec::cmd("/usr/bin/kstat")
                .arg("-p")
                .arg("cpu_info:0:cpu_info0:")
                .stdout(subprocess::Redirection::Pipe)
                .capture()
                .expect("Failed to run /usr/bin/kstat");
            let kstat_items: BTreeMap<_, _> = String::from_utf8(out.stdout)
                .expect("Non UTF-8 output from kstat")
                .lines()
                .filter_map(|line| {
                    let parts = line.trim().split('\t').collect::<Vec<_>>();
                    assert_eq!(
                        parts.len(),
                        2,
                        "Lines from kstat should be 2 tab-separated items, found {:#?}",
                        parts
                    );
                    let (id, value) = (parts[0], parts[1]);
                    if id.ends_with("crtime") {
                        let crtime: f64 = value.parse().expect("Expected a crtime in nanoseconds");
                        let crtime = (crtime * 1e9) as i64;
                        assert!(
                            (crtime - kstat.ks_crtime) < 5 || (kstat.ks_crtime - crtime) < 5,
                            "Expected nearly equal crtimes"
                        );
                        // Don't push this value
                        None
                    } else if id.ends_with("snaptime") {
                        let snaptime: f64 =
                            value.parse().expect("Expected a snaptime in nanoseconds");
                        let snaptime = (snaptime * 1e9) as i64;
                        assert!(
                            (snaptime - kstat.ks_snaptime) < 5
                                || (kstat.ks_snaptime - snaptime) < 5,
                            "Expected nearly equal snaptimes"
                        );
                        // Don't push this value
                        None
                    } else if id.ends_with("class") {
                        // Don't push this value
                        None
                    } else {
                        Some((id.to_string(), value.to_string()))
                    }
                })
                .collect();
            assert_eq!(
                items.len(),
                kstat_items.len(),
                "Expected the same number of items from /usr/bin/kstat:\n{:#?}\n{:#?}",
                items,
                kstat_items
            );
            const SKIPPED_STATS: &[&'static str] = &["current_clock_Hz", "current_cstate"];
            for (key, value) in kstat_items.iter() {
                let name = key.split(':').last().expect("Expected to split on ':'");
                if SKIPPED_STATS.contains(&name) {
                    println!("Skipping stat '{}', not stable enough for testing", name);
                    continue;
                }
                let item = items
                    .get(name)
                    .expect(&format!("Expected a name/value pair with name '{}'", name));
                println!("key: {:#?}\nvalue: {:#?}", key, value);
                println!("item: {:#?}", item);
                match item.value {
                    NamedData::Char(slice) => {
                        for (sl, by) in slice.iter().zip(value.as_bytes().iter()) {
                            if by == &0 {
                                break;
                            }
                            assert_eq!(sl, by, "Expected equal bytes, found {} and {}", sl, by);
                        }
                    }
                    NamedData::Int32(i) => assert_eq!(i, value.parse().unwrap()),
                    NamedData::UInt32(u) => assert_eq!(u, value.parse().unwrap()),
                    NamedData::Int64(i) => assert_eq!(i, value.parse().unwrap()),
                    NamedData::UInt64(u) => assert_eq!(u, value.parse().unwrap()),
                    NamedData::String(s) => assert_eq!(s, value),
                }
            }
        }
    }

    #[test]
    fn test_tracking() {
        let mut ctl = Ctl::new().expect("Failed to create kstat control");
        let track = |kstat: Kstat| {
            kstat.ks_module == "link" &&
                kstat.ks_instance == 0 &&
                kstat.ks_name == "igb0"
        };
        let id = ctl.track(track).unwrap();
        for mut st in ctl.fetch_tracked(&id).unwrap() {
            let Data::Named(named) = ctl.read(&mut st).unwrap() else {
                panic!();
            };
            println!("{:#?}", named.iter().find(|n| n.name == "rbytes64").unwrap());
        }
        let ctl = ctl.update().unwrap();
        std::thread::sleep(std::time::Duration::from_secs(1));
        for mut st in ctl.fetch_tracked(&id).unwrap() {
            let Data::Named(named) = ctl.read(&mut st).unwrap() else {
                panic!();
            };
            println!("{:#?}", named.iter().find(|n| n.name == "rbytes64").unwrap());
        }

        let mut d = std::time::Duration::ZERO;
        const ITERS: u32 = 10_000;
        for _ in 0..ITERS {
            let start = std::time::Instant::now();
            ctl.fetch_tracked(&id).unwrap();
            d += start.elapsed();
        }
        println!("{:?}", d / ITERS);


        let mut d = std::time::Duration::ZERO;
        for _ in 0..ITERS {
            let start = std::time::Instant::now();
            ctl.filter(Some("link"), Some(0), Some("igb0")).next().unwrap();
            d += start.elapsed();
        }
        println!("{:?}", d / ITERS);
    }
}
