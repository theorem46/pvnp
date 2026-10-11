# Relational Lysis and Computational Efficiency — Validation Archive

### Computational validation for *An Introductory Examination of the P vs NP Problem Using Relational Structure*

**Author:** Dr. David Swanagon
**Affiliation:** ORCID: 0009-0005-9506-4609, Dallas, Texas, United States

---

## 📄 Read the paper

The manuscript is **not** hosted in this repository. It is published open access:

| | |
| --- | --- |
| **Zenodo** | https://doi.org/10.5281/zenodo.23305964 |
| **ResearchGate** | https://www.researchgate.net/publication/415565565_Relational_Lysis_and_Computational_Efficiency_An_Introductory_Examination_of_the_P_vs_NP_Problem_Using_Relational_Structure |

This repository contains only the experiments behind the paper's appendices and their recorded output, so that any claim in the paper can be re-run and checked independently.

---

## 1. What the paper claims

That **structure precedes enumeration**.

A finite configuration is not stored and then searched for. It resides at an address fixed by the act of assertion, and the counts of the assertion say where to read. The paper poses this on the subset-sum decision problem in its weak form and states four theorems — the envelope, the address of zero, the reading law, and the encoding — each derived from the Relational Lysis primitive architecture by a closed dependency chain, and each measured by a protocol in this archive.

Two consequences are measured here rather than asserted:

**Cost is decoupled from magnitude.** On the worked assertion the structural reading forms 2 configurations in 28 operations and returns the answer, where the Bellman table visits 130 cells in 207 operations and returns a bit. Multiplying every magnitude by sixteen raises the table's cost 7.68× and leaves the structural reading's cost unchanged to the operation.

**Upstream cannot cost more than downstream.** Where the counts name no coincident cell, a ceiling computed from the counts confines the reading. Across 440 assertions, including an adversarial family built specifically to defeat the selection, the structural resolution never costs more than the table.

## 2. Foundational papers

This work rests on the Relational Lysis framework:

* Swanagon, D. (2026). *Relational Lysis: The Primitive Architecture of Structure, Constants, and Physical Law.* Zenodo. https://doi.org/10.5281/zenodo.21496929 — cited as **[1]**
* Swanagon, D. (2026). *Relational Lysis and the Necessity of Geometric Solved States: A Structural Resolution of the Yang–Mills Mass Gap.* Zenodo. https://doi.org/10.5281/zenodo.19116249 — cited as **[2]**
* Swanagon, D. (2026). *Relational Lysis and the Three-Body Problem: A Deterministic Derivation of Newtonian Gravity and General Relativity from Solved-State Geometry.* Zenodo. https://doi.org/10.5281/zenodo.19144445

## 3. Contents

```
Scripts/            the five experiment programs, one per appendix
Experiment Logs/    recorded output of each program, as published
```

`Scripts/conventions.py` is not an experiment. It defines the two cost conventions once — structural acts, and RAM elementary operations in the sense of Cook and Reckhow (1973) — so that every method compared is charged identically. All five programs import it, so it must stay beside them.

## 4. Running the experiments

Python 3.8 or later. No third-party dependencies.

```bash
python3 -I Scripts/A_precedence.py
python3 -I Scripts/B_address.py
python3 -I Scripts/C_reading.py
python3 -I Scripts/D_boundary.py
python3 -I Scripts/E_surplus.py
```

Each program is self-contained, resolves its own paths, uses fixed seeds, prints its structural output followed by its verdicts, and exits non-zero if any check fails. They may be run from any working directory. Output should match `Experiment Logs/` exactly.

## 5. What each experiment establishes

| Program | Appendix | Establishes |
| --- | --- | --- |
| `A_precedence.py` | A | **Structure precedes enumeration.** The numerical objects of Section 10 of [1] are withdrawn cumulatively and both resolutions re-run against what remains. The survey fails at the first row; the structural resolution completes at every row with the identical answer. |
| `B_address.py` | B | **Data as an address.** The solved state (Σ, D, S) of an assertion built from [1] and [2], and the address as an oriented path-word with two lengths — one that grows with the magnitudes and one that does not. |
| `C_reading.py` | C | **The reading law.** Reading the envelope by depth, the partition the counts select, the worked comparison against exhaustive survey, Bellman table and meet-in-the-middle under one convention, and the ceiling that bounds the reading where no cell coincides. |
| `D_boundary.py` | D | **Boundary assertion.** Boundary species and their soundness at scale, the two modes of assertion, and the remainder-class relation at depth, which decides an adversarial family at the boundary with no reading at all. |
| `E_surplus.py` | E | **The structural surplus.** What one resolution returns that enumeration does not: the whole target spectrum, multiplicity, an exhaustion certificate with distance, conjugate symmetry, and composition. |

## 6. Current verdicts

```
APPENDIX A       7 checks pass
APPENDIX B      46 checks pass
APPENDIX C      54 checks pass
APPENDIX D      25 checks pass
APPENDIX E      21 checks pass
```

Full output for each is in `Experiment Logs/`.

## 7. Falsifiability

The paper states its failure modes explicitly, each targeting a distinct item of its dependency graph and each tested by a named protocol here. Failure of any protocol in Appendices A–E is a direct refutation, and this archive exists so that the attempt costs one command.

One standing criterion of the framework belongs here, because this is where it would fail first. Relational Lysis is primitive and the classical methods are downstream projections of it, so an RL resolution can never cost more than its own projection at the same resolution. Should a classical method be shown to beat the structural reading on some assertion, the conclusion is that the boundary repertoire used was incomplete — not that the framework is wrong.

## 8. Citation

If you use this work, please cite the paper rather than the repository.

## 9. License

See `LICENSE`.
