/*
 * depile: translate three-address code back to C code.
 * Copyright (C) 2021  Ruifeng Xie
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

#![allow(unused)]

macro_rules! count {
    () => { 0 };
    ($x: tt $(, $xs: tt)*) => { 1 + count!($($xs),*) }
}
macro_rules! include_sample {
    ($name: ident) => {
        pub const $name: &str = include_str!(concat!("samples/", stringify!($name), ".txt"));
    }
}
macro_rules! include_samples {
    ($($name: ident),+ $(,)?) => {
        $(
            pub const $name: &str = include_str!(concat!("samples/", stringify!($name), ".txt"));
        )+
        pub const ALL_SAMPLES: [&str; count!($($name),+)] = [$($name),+];
    }
}

// SIMPLE does not have an entry point, so not suitable for most tests.
include_sample!(SIMPLE);
include_samples! {
    COLLATZ,
    GCD,
    HANOIFIBFAC,
    LOOP,
    MMM,
    PRIME,
    REGSLARGE,
    SIEVE,
    SORT,
    STRUCT,
}
