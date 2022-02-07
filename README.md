# depile

[![language](https://img.shields.io/badge/language-Rust-red)](https://www.rust-lang.org/)
[![license](https://img.shields.io/badge/License-AGPL--v3.0-blueviolet)](https://www.gnu.org/licenses/agpl-3.0.html)
[![CI](https://github.com/ruifengx/depile/actions/workflows/build.yaml/badge.svg)](https://github.com/ruifengx/depile/actions/workflows/build.yaml)
[![docs](https://img.shields.io/badge/Doc-GitHub%20Pages-brightgreen)](https://ruifengx.github.io/depile/)

_"de-" for "apart", as opposed to "com-" for "together"._

---

Translate three-address code back to C code. 

In principle, one should be able to find specification of the input format on [this lab description page](https://www.cs.utexas.edu/users/mckinley/380C/labs/lab1.html). However, there is no formal definition (in BNF, EBNF, or whichever variant of BNF at your choice, as one would usually expect); only some informal discussion can be found in Section "The 3-Address Intermediate Format".

Fortunately, this three-address code format is used nowhere else (and we are, and hopefully will be, the only ones to suffer from poor documentation). Since no other tool than `csc` (bundled in lab materials) should ever be producing files in this format, we assume that the input will always appear as if it were generated by `csc`, with a few relaxations.

> **Did You Know?:** year 2022 has arrived, yet the whole build process of `csc` is managed not even with `Makefile` (!), but with a _minimalistic_ Bash script assuming the local C compiler always being `gcc`...
>
> _"Take this, noob! This is how we program in the REAL WORLD!"_

## License

This project is licensed under the _GNU Affero General Public License_ as published by the _Free Software Foundation_, either version 3 of the License, or (at your option) any later version.
