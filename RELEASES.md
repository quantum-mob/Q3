# Select Release Notes

## v1.9.8

- New functions: CommonEigensystem, CommonEigenvalues, CommonEigenvectors.
- A change in GotttesmanVector and FromGottesmanVector.

## v1.9.6

- New package Stabilizer for stabilizer formalism.
- New functions PauliGroup, CliffordGroup, PauliForm.

## v1.9.5

- Internal code structures and relations have been change. No change from users' point of view.
- All packages included in Q3 are now working in the same context of Q3`.

## v1.9.2

- QuissoXXX, where XXX is for Phase, Rotation, EulerRotation, CZ, CNOT, SWAP, ControlledU, Toffoli, Fredkin, Oracle, is now obsolete. Use Elaborate[XXX[...]] instead.

- WignerRotation and WignerEulerRotation have been superceded by Rotation and EulerRotation, respectively.

## v1.9.0

- QuissoCircuit has been renamed QuantumCircuit.
- A bug fix in Measurement[vec, {q1, q2, ...}].
- New function ExpressionFor to replace PauliExpression, QuissoExpression, QuditExpression, and WignerExpression.
- DyadExpression has been re-implemented.
- More efficient implementation of QuissoOracle.
- New function FlavorThread.

## v1.8.9

- Updates for the Kraus package: Several functions such as LindbladConvert, LindbladGenerator, LindbladStationary have been enhanced and are more robust for inputs specified in the Pauli expressions.

## v1.8.8

- A quick bug fix in KetRule affecting the specification of Ket[{a,b,..}->{v1,v2,...}] for mixed species.

## v1.8.7

- Bug fixes in DampingOperator, LindbladSolve in the Kraus package.
- New function LindbladStationary in the Kraus package.

## v1.8.5

- New package Kraus to facilitate the study of quatum operations.
- New functions Supermap, ChoiMatrix, KrausProduct, LindbladBasis, LindbladGenerator, LindblandConvert, LindbladSolve, etc.

## v1.8.3

- Q3`*`Information`$Version instead of Q3`*`Private`Version

## v1.8.2

- `Qubits[QuissoCircuit[...]]` and `Matrix[QuissoCircuit[...]]` now respect the <code>"Visible"</code> option.

- Refinements in <code>Q3\`Custom\`</code> and a corresponding adjustment in `Options[BlochSphere]`.

## v1.8.1

- The internal structure of package codes has been slightly changed.
- In many cases, QuissoCircuit is automatically converted to an operator expression.

## v1.7.5

- Imroved Elaborate on QuissoCircuit.

## v1.7.4

- Imroved LogicalForm on OSlash, which affects QuissoFactor.

## v1.7.1

- Improved QuissoFactor.
- Distributed using the paclet server.

## v1.6.9

- A bug fix in Rotation for qubits.
- The size of QuissoCircuit display has been readjusted.
- New options to QuissoCircuit: UnitLength, PortSize

## v1.6.5

- New function SchmidtForm.
- SchmidtDecomposition has been generalized and enhanced.
- SchmidtDecomposition recieves a small change in its usage. 

## v1.6.3

- New functions ProperSystem, ProperStates, ProperValues.
- New function JordanWignerTransform.
- Enhanced Elaborate concerning MultiplyExp.

## v1.6.2

- A bug fix in Multiply involving Pauli.
- A bug fix in ProductForm.
- A bug fix in Kind.
- Enhanced SpinForm.
- New function VerifyOracle.

## v1.6.1

- Multiply has been enhanced based on a new mechanism.
- A bug fix in ProductState when used in Multiply.
- Various tutorial pages have been improved.


## v1.6.0

- FockExpand is deprecated now.
- Elaborate has been enhanced further.
- Various broken links in documentation pages have been fixed.
- Documentation pages have been updated to better support Mathematica v12.2.
- CoherentState is enhanced.


## v1.5.3

- Q3Update shows a progress indicator.
- New functions Q3RemoteFetch, Q3RemoteRelease, Q3RemoteURL.
- New functions GreatCircle, Bead, PartialTranspose.
- BlochSphere received modification in usage.
- BlochVector enhanced.
- Bug fixes concerning Dyad.
- Pauli[i->j, ...] and ThePauli[i->j, ...].

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

