[![](logo.svg)](https://axiommath.ai/)

# Formal Certificate for New Rogers–Ramanujan Identities

This repository contains a formal certificate for the arXiv paper [TODO].

The formal challenge is located in [RRA3/problem.lean](RRA3/problem.lean), and the solution is located in [RRA3/solution.lean](RRA3/solution.lean).

This depends on AxiomMath's repository [QSeriesLib](https://github.com/AxiomMath/QSeriesLib).

AxiomProver was used for the generation of these two Lean files.

## Verifying with Comparator

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in [https://github.com/leanprover/comparator](https://github.com/leanprover/comparator) to install comparator. Then, run the following command:

```
lake env comparator comparator.json
```
