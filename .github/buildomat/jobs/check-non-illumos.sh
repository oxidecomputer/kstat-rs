#!/bin/bash
#:
#: name = "ubuntu / build-and-test"
#: variety = "basic"
#: target = "ubuntu-22.04"
#: rust_toolchain = "stable"
#: output_rules = []
#:

set -o errexit
set -o pipefail
set -o xtrace

cargo --version
rustc --version

export RUST_BACKTRACE=1

banner fmt
ptime -m cargo fmt -- --check

banner test
ptime -m cargo test --release --no-fail-fast --verbose
