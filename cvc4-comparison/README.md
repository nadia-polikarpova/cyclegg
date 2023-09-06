# CVC4 comparison

## Notes

The property numbers do not necessarily match those in
[../examples/cycleq.ceg](../examples/cycleq.ceg), which is why in
[cvc4-results.csv](./cvc4-results.csv) there is a `prop` section that indicates
the property. The properties
[../examples/isaplanner.ceg](../examples/isaplanner.ceg) should match exactly.

The properties in [cvc4-results.csv](./cvc4-results.csv) have been reordered to
numeric order instead of the default lexicographic order.

## Install

Download the benchmarks and executable from
[here](https://lara.epfl.ch/~reynolds/VMCAI2015-ind/).

If you are not on Linux, try getting CVC4 from
[here](https://cvc4.github.io/downloads.html).  Version 1.5 is what I've tested to
work, but for some reason it proves fewer properties than the binary included with
the benchmarks.

## Generate the benchmarks

This is the command used to generate the benchmarks in `cvc4-results.csv`.

```bash
python3 run-benchmarks.py PATH-TO-CVC4 ind/benchmarks-dt/isaplanner -t 30000 -o cvc4-results.csv
```

## Custom benchmarks

Custom benchmarks are found in [custom](./custom). These include some new props
as well as some modified props from CVC4's benchmarks (for example, some of the
IsaPlanner benchmarks were written using CVC4's native equality instead of a
custom `eq` function, so we wrote new benchmarks that enforced usage of a custom
`eq` function).

## Running the helper script

Run
```bash
python3 run-benchmarks.py PATH-TO-CVC4 PATH-TO-BENCHMARKS -o results.csv
```

Run with `--help` to see other configuration options.

## Run manually

To run CVC4 with the binary,

```bash
./PATH-TO-CVC4 --quant-ind --quant-cf --full-saturate-quant FILENAME
```

If you get an error about locales, add
```bash
LC_ALL="C.UTF-8" 
```

This will not work with the latest cvc4 binary (version 1.8) that you can get
from e.g. apt, it needs to be 1.5 because of how the datatypes are defined. If
you could port the smt definitions, then you could use it on later versions
which appear to support the flags we want.
