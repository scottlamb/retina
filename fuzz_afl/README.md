# Fuzzing harnesses

## Using the fuzzer

Install afl:

    $ cargo install afl

Build fuzz target:

    $ cargo afl build --release --bin <fuzz_target>

Run afl:

    $ mkdir out/
    $ cargo afl fuzz -i in/ -o out/ target/release/<fuzz_target>

To reproduce a crash:

    $ cargo run --bin reproduce_<target>
