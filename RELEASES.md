# Select Release Notes

## v1.5.1

- Supports installation from a paclet archive.
- New functions: Q3Release, Q3CheckUpdate, Q3Update.

## v1.5.0

- New function Q3Version.
- No messages printed when Q3` is loaded.
- Symbols commonly used in all packages have context Q3`.
- New function FockAddSpinZ.
- Renamed: Cannon -> Canon
- CNOT now acts on multiple qubits. This is for convenience.
- Improved documentation for GrayCodeSubsets
- New functions: BinaryToGray, GrayToBinary
- New functions: TwoLevelU, GrayTwoLevelU, TwoLevelDecomposition

## v1.4.2

- Fredkin gate.
- New options "Visible" and "Invisible" for QuissoCircuit.
- Qubit specifications S[..., 10] and S[..., 11] are held (instead of being expanded immediately).

## v1.4.1

- New function ReleaseTimes.
- Enhanced SchmidtDecomposition.
- New function QuissoCircuitTrim.
- Improved QuissoCircuit user interface.

## v1.4.0

- Dyad gets major enhancement.
- Projector is improved based on Dyad.
- The feature of restricted Ket or Bra is removed.
- New function Elaborate to unify several functions including CauchyExpand, PauliExpand, QuissoExpand, etc.
- New package Abel, which hosts many algebra-related symbols and functions. Those were scattered around different packages.

## v1.3.2

- Support for Mathematica 12.2
- The option Label to many elements (Phase, ControlledU, etc.) of QuissoCircuit has been renamed as "Label".
- New function Oracle and QuissoOracle.

## v1.3.0

- Measure has been renamed as Measurement.
- Measurement\[q\]\[expr\] is undefined, use Measurement\[expr, q\] instead.
- The input arguments of Readout are exchanged.
- A bug fix in ProductState.

