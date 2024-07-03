# Release Notes

## 3.4.6

- Further performance improvement for fermionic quantum computing
- ChebyshevCoefficients is based on FourierDCT and is much faster.
- ChebyshevApproximation is renamed ChebyshevSeries.
- Style sheet PlaybookX has been renamed PlaybookNub.

## 3.4.5

- Pfaffian has greatly improved; almost 10 times faster. This also improves the performance of WickState, WickUnitary, WickExpectation, WickGreensFunction, WickLogarithmicNegativity, WickEntanglementEntropy, etc.
- New functions: ChebyshevApproximation, ChebyshevCoefficients
- Matrix and Elaborate support WickState, WickUnitary, WickOperator, Measurement[_?FermionQ].

## 3.4.4

- New functions: NambuMatrix, NambuRandomMatrix, PauliMatrixQ, CliffordMatrixQ.
- Improved: Pfaffian, SkewTridiagonalize, DickeBasis, PauliQ.
- QuantumCircuit supports WickUnitary, WickOperator, Measurement[fermions] and some other fermionic quantum computing elements.

## 3.4.3

- New function WickEntanglementEntropy (cf. EntanglementEntroy) is dedicated to the context of Wick state.
- New option "Data" for WickRandomCircuit.

## 3.4.2

- New function: CrossEntropy
- Enhancement: WeightLog, QuantumLog, EntanglementEntropy, WickGreensFunction, WickHistory
- The output form of WickRandomCircuit has been changed.
- WickOperate has been renamed WickOperator.

## 3.4.1

- New function StabilizerGenerators.
- EntanglementEntropy now supports WickState.

## 3.4.0

- New functions for fermionic quantum computation: WickHistory, WickRandomCircuit, WickOperate, WickGreensFunction.
- Other new function: MatrixObject, RandomPick.
- Syntax arguments of WickExpectation has been changed.
- Changes in the convention for the compact form of unitary matrix in the Nambu space.
- WickLogarithmicNegativity supports WickState.

## 3.3.19

- Further backward compatibility issue concerning PositionLargest.
- Bug fixes for WickExpectation.

## 3.3.18

- New symbol ArrayPermute.
- Backward compatibility issue concerning PositionLargest used in Pfaffian.

## 3.3.17

- New function BlockEncoding and StateForm
- Enhanced KetCanonical
- Bug fixes concerning State and ProductState.

## 3.3.15

- New functions FermionTranspose, FermionTimeReversal, WickTimeReversalMoment, WickLogarithmicNegativity.
- Enhanced WickState and WickExpectaion.

## 3.3.14

- WickState and WickExpectation support fermion pairing.
- A bug fix concerning State.
- A bug fix concerning QFT[..] ** Ket[...]

## 3.3.13

- An emergency bug fix for Dagger[c]**Ket[...], where c is a fermion.

## 3.3.12

- New symbols Pairings, Unpaired, WickState, WickExpectation.
- MajoranaToDirac, DiracToMajorana, BosonToHeisenberg, HeisenbergToBoson are renamed ToDirac, ToMajroana, ToHeisenberg, ToBoson, respectively, with enhancement.
- Bug fixes in Pfaffian and SkewTridiagonalize.
- Enhaced KetVerify.
- Sorting Keys for fermions in Ket[<|...|>] now respects the sign of the required permutation even at the stage of the Ket construction.

## 3.3.11

- Another emergency bug fix, this time, concerning Multiply[..., Ket[...], State[...], ...].

## 3.3.10

- An emergency bug fix concerning QuantumCircuit including both ProductState and Ket.

## 3.3.9

- Elaborate supports Dyad involving Fermions.

## 3.3.7

- New function Pfaffian and SkewTridiagonalize.
- The value of option "Normalized" of CoherentState is now False by default.
- The normalization convention for Majoranas have been changed; a^2 = 1, instead of a^2 = 1/2.
- GD and GIntegrate have been enhanced.

## 3.3.6

- Enhanced support for CoherentState.
- ControlledExp is removed.
- Documentation on some excised symbols are removed.
- Refinements: RealQ, ComplexQ, Rotation

## 3.3.5

- Emerngency bug fix for ReleaseTimes.

## 3.3.4

- Several bug fixes concerning QuantumCircuit.
- Performance boost for Elaborate[QuantumCircuit[...]]

## 3.3.3

- Redefined functions State and Operator.
- The usage of State and Operator has been changed.
- TheState and TheOperator have been excised.
- New functions QCR and QBR, and their relation to QFT.
- QFT enhanced and improved.
- New syntax pattern for QFT.
- Utility tools are separated from Abel. LinearMap and LinearMapFirst are deprecated. New message Q3General::deprecated. New functions ReplaceRules and ReplaceRulesBy.
- Port labels now can be aligned left or right in QuantumCircuit.

## 3.3.2

- New option "Normalized" for CoherentState.
- New function IntegerParity.
- Grassmann is rewritten almost from the scractch.
- Typo correction in the documentation on CoherentState.

## 3.3.1

- Several bug fixes concerning YoungShape, YoungTableau, GelfandPattern in YoungFourier, YoungNormalRepresentation, YoungFourierBasis, YoungRegularBasis, SpechtBasis, etc.
- Performance enhancement for CNOT, CZ, Swap and QFT when acting on Ket, Bra, and Dyad.
- Dagger[QFT[...]] is now handled by the new option "Parameter".
- The usage of CZ has been changed.
- More information about the process in PlaybookTools.
- Experimental built-in functions BlockDiagonalMatrix and PermtuationMatrix are kept in Abel.
- All renamed, obsolete, excised symbols are moved to Einstein.
- Improved FockKet and FermionBasis.

## 3.3.0

- Bug fixes: Matrix[MultiplyExp[...]], KetSpecies, PlaybookTools.
- Matrix[expr, ...] with expr involving fermions have been changed back to the convention before 3.1.1.
- Basis sorts the Keys, but for fermions, put additional signature factor.
- fermionMatrix to properly handle Matrix for fermions
- New fallback for ThePauli[{}]
- GivensFactor and GivensRotation are declared in Pauli.wl, before Matchgate in Quisso.wl uses GivensRotation; Matrix[Matchgate[...], ...]
- "FoldSections" is set True by default in PlaybookTools.

## 3.2.1

- Bug fixes in PlaybookTools; an alert of dynamic content in .Playbook.nb; incomplete printing.
- New stylesheet PlaybookX.nb
- New function PlusTopple
- Bug fixes in TimesDaggerLeft, TimesDaggerRight.
- A bug fix in seaQ that affects AnnihilatorQ, CreatorQ, FockAddSpin, FermionBasis, etc.
- A bug fix in FockMatrix due to toKetForm still lingering, and now being replaced with FockKet.
- A bug fix in KetSpecies, affecting KetRegulate.

## 3.2.0

- Bug fixes: KetSort, Matrix[fermion, ...], Matrix[Ket[fermion], ...]
- Revised implementation of KetRegulate using new theKetRegulate
- More consistent implementation of fermion ** Ket[...] and Dagger[fermion] ** Ket[...]

## 3.1.1

- A serious bug has been fixed concerning Matrix[fermion, ...] and Matrix[Dagger[fermion], ...].

## 3.1.0

- S[..., C[n]], instead of S[..., C[-n]], is equivalent to Phase[2*Pi/2^n, S[..., 3]] for Qubit S.

## v3.0.3

- Improved CliffordFactor::usage
- CliffordDecompose is renamed CliffordFactor; CliffordDecompose is an alias of CliffordFactor.
- NineQubitCode is updated for better demonstration codes.
- Corrections in MakeBoxes for Supermap and LindbladSupermap.
- Emergency code for Expand[Dagger @ QFT] in Quisso.wl
- Further elaboration of Dagger[ControlledPower[...]]
- Expand[QFT] is renamed ExpandAll[QFT]; Expand[QFT] is redefined.
- Bug fix: Matrix[ControlledPower[cc, op]] when cc is not in the canonical order; Expand[Dagger @ QFT]
- Improved documentation: ControlledGate, ControlledPower, QFT, QuantumFourierTransform, Von Neumann Entropy

## v3.0.2

- More flexibility issues for Ket[] and Bra[]
- Readjusted $InOutOffset, $BraceWidth
- Improved documentation: LindbladSimulate, Purification, LindbladSimulate, HadamardTest, QuantumAlgorithms, SwapTest, FullGarner, CliffordFactor
- New documentation: QuantumCircuitTrim
- Removed documentation: QuissoCircuitTrim
- A bug fix in FromGottesmanmatrix

## v3.0.1

- Bug fix concerning Dyad, GroupGenerators[PauliGroup[n]], Basis[expr], DyadForm[mat], Pauli[a -> b], fPauliKetQ, Stabilizer, Qubits[QuantumCircuit[...]], ProperSystem, ProperStates, ReducedMatrix

## v3.0.0

- Starts to use Git for version control.
- Raise, Lower, TheRaise, TheLower, RaiseLower are renamed Raising, Lowering, TheRaising, TheLowering, RaisingLoweringForm, respectively, because of a conflict with Mathematica 14.
- PlaybookTools improved.

## v2.15.4

- New function Matchgate.
- Elaborate[GivensRotation[...]]

## v2.15.3

- A bug fix for Qubits[QuantumCircuit[...]].
- New function PlaybookEpilog.

## v2.15.2

- Quantum circuit model of UnitaryInteraction is changed.

## v2.15.1

- Improved documentation for iSwap and Swap.
- Measurement[{}] is allowed; giving no effect, though.

## v2.15.0

- The syntax of Pauli, ThePauli, Ket, and TheKet has changed significantly.
- New quantum circuit element iSwap.

## v2.14.16

- More tutorial docomentations.

## v2.14.13

- PlaybookTools improved.

## v2.14.12

- New aliases GottesmanGroup and GottesmanGroupElements for BinarySymplecticGroup and BinarySymplecticGroupElements, respectively.

## v2.14.11

- A bug fix concerning Multiply involving Dyad.

## v2.14.10

- The arrange order of elements in the basis resulting from BosonBasis has been changed.
- New function CountsFor.
- Updates in the help documentation on ShiftLeft and ShiftRight.

## v2.14.9

- New function EntanglementEntropy.
- A few minor improvements in ShannonEntropy and VonNeumannEntropy. 

## v2.14.8

- Improved help documentation for GottesmanMatrix, FromGottesmanMatrix, BinarySymplecticGroup, BinarySymplecticGroupElements.
- New function RenyiEntropy.

## v2.14.7

- Small improvements in graphically rendering QuantumCircuit.
- RandomUnitary now generates random unitary matrices distributed uniformly in the sense of the Haar measure.
- Improvements in PlaybookTools`.

## v2.14.6

- Emergency bug fix for QuantumCircuit.

## v2.14.5

- Emergency bug fix concerning S[..., 4] and S[..., 5] acting on Ket[...] for Qubits S[..., $].

## v2.14.4

- Emergency bug fix for UnitaryInteraction.

## v2.14.3

- New function UnitaryInteraction.
- Improved QuantumCircuit.

## v2.14.1

- Quick corrections to a few documentation notebooks.

## v2.14.0

- Improved BosonBasis.
- New function UniformlyControlledGate.
- SWAP is renamed Swap.
- NextGelfandPatterns is renamed GelfandAttach.
- New functions YoungTableau, GelfandPattern.
- SchurBasis looks much more user-friendly.
- WeylHeisenbergBasis is renamed WeylBasis.
- New function LieBasisSupermap.
- LieBasisMatrix now returns supermatrix (not Choi matrix).

## v2.13.10

- Emergency bug fix concerning formatting of Ket and Bra.

## v2.13.9

- New function StabilizerStateCount.
- Improved Garner.
- Bug fixes for GottesmanStandard and GottesmanBasis.
- The meaning of CZ has changed slightly.

## v2.13.8

- Emergcy correction of the help documentation of Oraccle.

## v2.13.6

- New function BitReflect.
- More gate shapes.

## v2.13.6

- A bug fix concerning QuantumCircuitTrim.
- New functions GrayBasis, GrayTransform, TheGrayTransform, GrayToInteger, IntegerToGray, GrayCycles, GrayGivensFactor, GivensRotation, GivensFactor.
- New canonical forms for CNOT, ControlledGate, Gate.

## v2.13.5

- New functions AmplitudeEmbedding, AmmplitudeEmbeddingGate, BasisEmbedding, BasisEmbeddingGate.

## v2.13.4

- New function UniformlyControlledRotation.
- New function GateFactor.

## v2.13.2

- An emergency bug fix affecting Ket formatting.

## v2.13.1

- CoherentState and Displacement have been enhanced.

## v2.13.0

- Support for Mathematica 13.3; in particular, changes concerning new built-in functions Kind and Bra.

## v2.12.7

- Improved PlaybookTools.

## v2.12.6

- Improved FlavorNone.
- Improved Gate.

## v2.12.5

- Some tutorial documents have been revised for better presetnation.

## v2.12.4

- Reimplementation of Supermap based on ChoiMatrix.

## v2.12.3

- ControlledExp is renamed ControlledPower; yet remains as an alias.

## v2.12.2

- A demonstration is added to the tech note on the order-finding algorithm.

## v2.12.1

- Classical oracle Oracle[f, m, n].
- Quantum oracle Oracle[f, {c1,c2,...}, {t1,t2,...}].
- New implementations of Matrix[Oracle[...]] and Elaborate[Oracle[...]] based on Oracle[f, m, n].
- New utility function MapThrough.

## v2.12.0

- New option "LabelAngle" and "LabelStyle" for quantum circuit elements.
- New functions ParseGate, ParsePort, Gate, Port.
- New quantum circuit element ModMultiply.
- Matrix and Elaborate supports for ModMultiply.
- Several internal changes in rendering quantum circuit elements.

## v2.11.11

- New function ModMultiply.

## v2.11.10

- Maintenance updates.

## v2.11.9

- An emergency bug fix for Multiply[..., a_Ket, b_Bra, ...].

## v2.11.8

- A bug fix for KetRegulate.

## v2.11.7

- New low-level function OperatorOn.
- A few tutorial documents have been polished or created.

## v2.11.6

- A bug fix for ProductState.
- Techical Notes on measurement-based quantum computation.

## v2.11.5

- PauliDecompose receives a small change to handle numerical matrices better.
- StabilizerStateQ is changed back to the previous version.
## v2.11.4

- NormalForm has been renamed KetCanonical.
- StabilizerStatesQ is more reliable (or generous) for numerical states.

## v2.11.3

- Bug fixes for ProductState.

## v2.11.2

- Expand[ControlledGate[...]] improved (still EXPERIMENTAL).
- Several other improvements concerning the Specht and Young-Fourier bases.

## v2.11.0

- New function YoungFourierMatrix and YoungFourier.
- New implementation of YoungFourierBasis based on YoungFourierMatrix. 
- EXPERIMENTAL: Ket[...]**Bra[...] is automatically converted to Dyad[...].
- New function KetMutate.
- CircleTimes enhanced.
- The key binding for Playbook style sheet has been changed.

## v2.10.10

- PlaybookTools improved.

## v2.10.9

- PlaybookTools are included.

## v2.10.7

- New function GroupClasses, SymmetricGroupClasses.
- Bug fixes in package extentions.

## v2.10.6

- Bug fixes in XBasisForm and YBasisForm.

## v2.10.5

- New function NormalForm.
- An emergency bug fix in KetRule; the bug hit MaZX package.


## v2.10.4

- Maintenance update of help documents to minimize the use of KetRegulate (previously, LogicalForm).
- The keys of SpechtBasis is arranged so as to be consistent with SchurBasis.

## v2.10.3

- LogicalForm has been renamed KetRegulate.
- A bug fix in MeasurementOdds.
- Improved CliffordDecompose.
- The usage of MeasurementOdds is changed so that it is consistent with that of Measurement and Readout.

## v2.10.2

- New function KetSpecies.
- Kets are not trimmed by default any longer. LogicalForm is not necessary in most cases.

## v2.10.1

- Improved CNOT.
- ControlledU is renamed ControlledGate.

## v2.10.0

- The flavor index referring to the species itself is now $; You can use S[..., $] instead of S[..., None] (still valid).
- Improved QFT, including Expand[QFT[...]].
- Improved ExpressionFor[QuantumCircuit[...]].
- Improved Matrix[QuantumCircuit[...]].
- New functions: MeasurementFunction, Measurements, XBasisForm, YBasisForm.

## v2.9.10

- A bug fix in Matrix[Permutation[...], ...].

## v2.9.9

- New implementation of PauliDecompose for faster performance for 8 or more qubits. BlochVector, RotationSystem, Stabilzer and StabilizerStateQ are updated accordingly.
- Dyad has been generalized and enhanced; Matrix has been generalied and enhanced accordingly.
- TheMatrix has been enhanced.
- DyadExpression has been renamed DyadForm.
- LindbladBasis and LindbladBasisMatrix have been renamed LieBasis and LieBasisMatrix, respectively.

## v2.9.8

- A bug fix concerning Power[_?BinaryQ, ...], which led to 1 / 0 = 0.

## v2.9.7

- A serious bug in Multiply involving S[..., 6].
- "F" for the hexadecant phase gate (instead of "Q").

## v2.9.6

- The Successive function has been enhanced.
- Slightly improvement in Matrix[_QuantumCircuit].

## v2.9.4

- Phase[phi, S[..., k]] with k = 1, 2, 3.

## v2.9.3

- Formatted ouput of Pauli[...].
- QuissoAdd and QuissoAddZ have been renamed QubitAdd and QubitAddZ, respectively.

## v2.9.2

- Hexadecant phase gate.
- Phase gates Pauli[..., C[-n], ...] and S[..., C[-n]] by angle 2*Pi/Power[2, n].

## v2.8.8

- Emergency bug fix concerning Qudit.

## v2.8.7

- Some broken cross-reference links have been fixed.

## v2.8.6

- The titles and filenames of some tutorial documents have been changed.

## v2.8.5

- Formatted outputs may now be copied with the input form preserved.

## v2.8.4

- The Workbook stylesheet has been renamed Playbook.

## v2.8.3

- WeylContent has been renamed WeylType.
- New functions: WeylContents, GelfandContents

## v2.8.2

- One can now specify the values of the control register in CNOT and ControlledU.

## v2.8.1

- An emergency bug fix in CliffordQ.

## v2.8.0

- EXPERIMENTAL: Now, the Q3 package is loaded automatically when the kernel starts.

## v2.7.18

- LogicalForm recieves a major change; it only displays the species that are explicitly specified.

## v2.7.17

- Dyad now requires more stringent syntax.

- Performance of Dyad has been improved.

## v2.7.16

- A bug fix concerning QuantumCircuit[..., Measurement[...], ...] ** state.

- Measurement and MeasurementOdds have been improved.

## v2.7.12

- CliffordDecomposition is now open to the public. Previously, it was a part of another project.

## v2.7.11

- An emergency update to handle some special cases where BasisComplement behaves unexpectedly, the issue of which is inherited from the built-in Orthogonalize function.

## v2.7.9

- LindbladGenerator has been renamed LindbladSupermap.

## v2.7.8

- LindbladSimulate has been further improved in speed.

## v2.7.6

- LindbladSimulate has been significantly improved in speed.

## v2.7.5

- An emergency change in the output form of LindbladSimulate.

## v2.7.4

- An emergency bug fix in LindbladSimulate.

## v2.7.3

- LindbladSimulate for the quantum jump approach.

## v2.7.1

- YoungFourierBasis, YoungRegularBasis, YoungNormalRepresentation.
- Occupation acts like an operator on expressions of state vectors.

## v2.7.0

- PermutationBasis spanning the permuation module for the symmetric group.
- SpechtBasis spanning the Specht module for the symmetric group.

## v2.6.24

- Pauli[-7] and Pauli[-8] have been removed.

- Pauli[-n] introduced to represent a special class of phase gates; consistent with S[...,-n] for labelled qubits. 

## v2.6.23

- LindbladBasisMatrix has been significantly enhanced in speed. It also affects other functions such as LindbladConvert that are relying on it.

## v2.6.22

- Emergency bug fix for ChoiMatrix.

## v2.6.21

- Tutorial on the Choi isomorphism has been rewritten.

## v2.6.20

- Another emergecy bug fix, this time, in PartialTrace.

## v2.6.19

- An emergecy bug fix in WeightedLog.

## v2.6.16

- The sequence pattern of the arguments for GHZState has been changed.
- KetPermute has been rewritten for performance enhancement.
- New functions: SimplifyThrough, FullSimplifyThrough, PileYoungShape, BratteliDiagram, etc.

## v2.6.11

- A bug fix in NormPT

## v2.6.10

- New function ExpressionIn.
- New function NormPT.
- LogarithmicNegativity[rho, {s1, s2, ...}] is allowed now. In this case, rho is assumed to be properly normalized.

## v2.6.7

- New faster implementation of GelfandYoungPatterns.
- More techical notes in Documentation.

## v2.6.4

- An urgent bug fix concerning Q3Info[].

## v2.6.2

- New function LevelsPlot.
- CountWeylTableaux renamed WeylTableauCount.
- CountYoungTableaux renamed YoungTableauCount.

## v2.6.1

- Supermap[tsr_?ChoiMarrixQ][rho] is supported now.
- New functions: ChoiMultiply, ChoiTopple.
- LindbladBasis now uses LieBasis.

## v2.6.0

- Some files have been renamed in the documentation.

## v2.5.2

- Enhancement of LindbladConvert, LindbladBasisMatrix.

## v2.5.1

- New function SmolinState.
- Q3Release check local installation.

## v2.5.0

- Compatibility update for Mathematica 13.1.
- MatrixIn[op, assoc1, assoc2] is now allowed.

## v2.4.1

- Permutation, an operator form of KetPermute, has been improved.
- Another operator form of KetPermute has been removed.

## v2.4.0

- FockBosonToHeisenberg renamed BosonToHeisenberg.
- FockHeisenbergToBoson renamed HeisenbergToBoson.
- FockDiracToMajorana renamed DiracToMajorana.
- FockMajoranaToDirac renamed MajoranaToDirac.

- Heisenberg canonical operators now act directly on Ket[<|...|>].

- WignerFunction is superceded by the WignerD built-in function.

- Several refinements in reference and tutorial documents.

## v2.3.25

- A new experimental function LieBasis.

## v2.3.23

- Minor bug fixes.

## v2.3.14

- Qubit speices takes a negative value for the final flavor index.

## v2.3.7

- A bug fix concerning Matrix[Dyad[...], ...].
- Several new tutorial documents on basic quantum computation.

## v2.3.6

- An emergency fix for an issue affecting KetPurge, KetUpdate, Observation, etc.

## v2.3.4

- GraphState enhanced in usage and performance.
- Stabilizer enhanced in usage and performance.
- QuantumFourierTransform has been renamed QFT.
- Several tutorial documents on quantum algorithms.

## v2.3.3

- More new tech notes.
- Updated tech note, Quantum Fourier Transform.

## v2.3.2

- KetUpdate has been improved.

## v2.3.1

- Removed some garbage files from Documentation. 

## v2.3.0

- New functions GottesmanSplit and GottesmanMerge to handle Gottesman vectors.
- Documentation has been restructured and improved.

## v2.2.2

- Performance improvement in GottesmanMatrix.
- GottesmanVector and GottesmanMatrix can now take a matrix as input.

## v2.2.1

- PauliGroup and CliffordGroup now represent quotient groups. To refer to the corresponding full group, use FullPauliGroup and FullCliffordGroup.
- Improved support for GroupElements on PauliGroup and CliffordGroup.
- New functions GottesmanMatrix and FromGottesmanMatrix to describe Clifford operators.
- New function Permutation, representing a permutation operator on a system of species.

## v2.2.0

- Measurement and Readout have been improved and support more arbitray Pauli operators (including tensor products of single-qubit Pauli operators).
- New function MeasurementOdds.
- Improved QuantumFourierTransform (it has a new optin N which indicates numerically approximate quantum Fourier transform).

## v2.1.5

- New function Occupation and OccupationValue.
- QuantumCircuit is now maintained in Quville`.

## v2.1.4

- A bug fix in Let.
- New functions Observation and ObservationValue.
- A buf fix in KetFactor.

## v2.1.3

- QuantumCircuit has been improved and receives a bug fix.
- The syntax of ParityEvenQ and ParityOddQ has been slightly changed.
- New function ParityValue.

## v2.1.2

- Documentation built with PacletDocumentationBuild from Mathematica 13.

## v2.1.1

- The output format of KeyGroupBy has been slightly changed.
- An operator form of SchurBasis.
- A small change in the usage of SchurBasis.

## v2.1.0

- A complete technical note on the Schur transform.
- Significant improvements of the implementations of SchurBasis and NextSchurBasis.
- The order of input arguments of SchurBasis and DualSchurBasis has been reversed.
- DualSchurBasis is merged into SchurBasis.
- Improved performance of SchurBasis.
- The data structure of the output of SchurBasis has been changed.

## v2.0.2

- More detailed explanations on the Schur transform.

## v2.0.0

- Q3`Schur` package for Schur transform.
- A few changes in Q3`Young` to support Q3`Schur`.

## v1.9.23

- Fixed a bug that caused Series to produce inconsistent results.
- New function Deutsch representing the Deutsch gate.

## v1.9.20

- Let[Species, ...] uses Clear and ClearAttributes instead of ClearAll.
- Pauli and ThePauli have attributes Listable.

## v1.9.18

- New package Q3`Young` for the symmetric group.

## v1.9.17

- The old KetPurge renamed KetDrop.
- KetPurge has a new functionality.
- QuissoFactor is obsolete. Use KetFactor instead.
- Dirac is obsolete. Use Dyad instead.

## v1.9.16

- HermitianProduct has been renamed HilbertSchmidtProduct.
- HermitianNorm has been renamed HilbertSchmidtNorm.
- New function FrobeniusNorm.

## v1.9.15

- Changes in internal filenames.
- Partitions renamed ListPartitions to avoid a conflict with Combinatorica.

## v1.9.12

- A bug fix concerning S[..., 10] and S[..., 11] inside Multiply[...].

## v1.9.10

- QuantumCircuit[...] ** Ket[...] is handled better.

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

