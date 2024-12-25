# Vamp-IR

Vamp-IR is a language for arithmetic circuits. The Vamp-IR compiler can transform an arithmetic circuit into a form that is compatible with any proving system backend.

## Docs

[Vamp-IR book (WIP)](https://github.com/anoma/VampIR-Book)

## Trying Vamp-IR

### Installation
```
git clone git@github.com:anoma/vamp-ir
cd vamp-ir
cargo build
```

### Hello World!

We will build a circuit in Vamp-IR that checks if a pair $(x, y)$ is a point on a circle of a certain radius, $R$, which is given publicly.

In a file `pyth.pir` :
```
// declare R to be public
pub R;

// define the Pythagorean relation we are checking
def pyth a b c = {
  a^2 + b^2 = c^2
};

// appends constraint x^2 + y^2 = R^2 to the circuit
pyth x y R;
```

### Compile
Compile source `pyth.pir` to a circuit that can be used in Halo2 and serialize it to the file `pyth.halo2`.

```
vamp-ir halo2 compile -s pyth.pir -o pyth.halo2
```

### Create a proof

Suppose the target radius $R$ is $25$, and we come up with $(x, y) = (15, 20)$. We can use `vamp-ir` to create a Halo2 proof using these inputs.

First create a file `pyth.inputs` in JSON format which contains our solution.

```
{
  "x": "15",
  "y": "20",
  "R": "25"
}
```
Then run the Halo2 prover using our compiled circuit and our inputs, outputting a Halo2 proof to `pyth.proof`.

```
vamp-ir halo2 prove -c pyth.halo2 -i pyth.inputs -o pyth.proof
```

### Verify the proof

Run the Halo2 verifier using the compiled circuit and the proof.

```
vamp-ir halo2 verify -c pyth.halo2 -p pyth.proof
```

### 

## Benchmarks
These benchmarks are performed on a Lenovo ThinkPad X1 Carbon Gen 9 with 8.0 GiB RAM and 
an 11th Gen Intel® Core™ i5-1135G7 @ 2.40GHz × 8 unless stated otherwise
### Halo2 backend

#### SHA256 1 block message

|         | `Compile`  | `Prove`    | `Verify` |
|:--------|:-----------|:-----------|:---------|
| Vamp-IR | `172.05 s` | `26.72 s`  | `0.61 s` |
| Halo2   | //         | `161.05 s` | `1.06 s` |

#### SHA256 2 block message

|         | `Compile`  | `Prove`    | `Verify` |
|:--------|:-----------|:-----------|:---------|
| Vamp-IR | `353.76 s` | `46.91 s`  | `1.09 s` |
| Halo2   | //         | `160.03 s` | `1.05 s` |

#### SHA256 4 block message

|         | `Compile`  | `Prove`         | `Verify` |
|:--------|:-----------|:----------------|:---------|
| Vamp-IR | `729.47 s` | Memory Failure | X        |
| Halo2   | //         | `160.36 s`      | `1.03 s` |

We re-run the with a device that has 128GB of RAM and these are the results:

|         | `Compile` | `Prove`    | `Verify` |
|:--------|:----------|:-----------|:---------|
| Vamp-IR | `60 s`    | `81.983 s` | `0.6 s ` |

### ZK-garage plonk backend

#### Blake2s

|           | `Compile` | `Prove`   | `Verify` |
|:----------|:----------|:----------|:---------|
| Vamp-IR   | `76.30 s` | `57.59 s` | `0.22 s` |
| ZK-Garage | //        | `32.48 s` | `0.10 s` |

#### Blake2s using only fan-in 2 gates
To have a more fair comparison between Vamp-IR and ZK-Garage, we can use only fan-in 2 gates in the Blake2s circuit.
This is because the current version of Vamp-IR does not uses fan-in 3 gates, as the ZK-Garage backend does, which in a 
speed-up.

|           | `Compile` | `Prove`    | `Verify` |
|:----------|:----------|:-----------|:---------|
| Vamp-IR   | `76.30 s` | `57.59 s`  | `0.22 s` |
| ZK-Garage | //        | `360.48 s` | `0.81 s` |

The version of Blake2 used for the latter benchmark can be found here:
https://github.com/heliaxdev/ark-plonk/blob/blake2s/examples/blake2s_circuit_fain2.rs


## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
