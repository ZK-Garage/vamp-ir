# Vamp-IR

Vamp-IR is a powerful domain-specific language (DSL) designed for creating and manipulating arithmetic circuits. It provides a high-level abstraction for zero-knowledge proof systems, allowing developers to write circuits in a more intuitive way. The Vamp-IR compiler can transform these circuits into formats compatible with various proving system backends like Halo2 and ZK-garage plonk.

## Features

- Simple and intuitive syntax for arithmetic circuit description
- Multiple backend support (Halo2, ZK-garage plonk)
- Built-in optimization for circuit compilation
- Support for public and private inputs
- Efficient proof generation and verification

## Requirements

- Rust 1.65 or higher
- Git
- Cargo (Rust package manager)
- 8GB RAM minimum (128GB recommended for large circuits)

## Documentation

[Vamp-IR book (WIP)](https://github.com/anoma/VampIR-Book)

## Getting Started

### Installation
```bash
git clone git@github.com:anoma/vamp-ir
cd vamp-ir
cargo build
```

### Hello World Example: Circle Point Verification

This example demonstrates how to verify if a point (x, y) lies on a circle with radius R.

#### 1. Create the Circuit

Create a file named `pyth.pir`:
```rust
// declare R to be public
pub R;

// define the Pythagorean relation we are checking
def pyth a b c = {
  a^2 + b^2 = c^2
};

// appends constraint x^2 + y^2 = R^2 to the circuit
pyth x y R;
```

#### 2. Prepare the Inputs

Create `pyth.inputs` with your test values:
```json
{
  "x": "15",
  "y": "20",
  "R": "25"
}
```

#### 3. Compile, Prove, and Verify

```bash
# Compile the circuit
vamp-ir halo2 compile -s pyth.pir -o pyth.halo2

# Generate the proof
vamp-ir halo2 prove -c pyth.halo2 -i pyth.inputs -o pyth.proof

# Verify the proof
vamp-ir halo2 verify -c pyth.halo2 -p pyth.proof
```

## Performance Benchmarks

> Note: Benchmarks were performed on a Lenovo ThinkPad X1 Carbon Gen 9 (i5-1135G7, 8GB RAM)

### Halo2 Backend Performance

| Circuit Type          | Operation | Vamp-IR    | Native Halo2 |
|----------------------|-----------|------------|--------------|
| SHA256 (1 block)     | Compile   | 172.05s    | -            |
|                      | Prove     | 26.72s     | 161.05s      |
|                      | Verify    | 0.61s      | 1.06s        |
| SHA256 (2 blocks)    | Compile   | 353.76s    | -            |
|                      | Prove     | 46.91s     | 160.03s      |
|                      | Verify    | 1.09s      | 1.05s        |

### High-Memory Environment (128GB RAM)
| Circuit Type          | Operation | Vamp-IR    |
|----------------------|-----------|------------|
| SHA256 (4 blocks)    | Compile   | 60s        |
|                      | Prove     | 81.983s    |
|                      | Verify    | 0.6s       |

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
