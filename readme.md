
# qbffamExt.py - QBF Instance Generator

## Description
`qbffamExt.py` is a specialized Python-based generator for **Quantified Boolean Formula (QBF)** benchmark instances in QDIMACS format.

Originally developed by **Martina Seidl** (JKU Linz) in 2020 and extended by **Agnes Schleitzer** (FSU Jena) in 2026, this tool provides a wide range of benchmark formula families.

## Requirements

The script requires **Python 3.x** and the **PyEDA** library for symbolic logic manipulation and Tseitin transformation.
```bash
pip install pyeda
```

## Usage
The general syntax for the script is as follows: 
```bash 
python3 qbffamExt.py <family> <size> [extra_params]
```
### Required Arguments:

-   **family**: The name of the formula family (e.g., `KBKF`, `GADGETFAM`, `SUCKRAD`).
    
-   **size**: The main parameter for the size or complexity of the generated instance.
    

### Extra Parameters (Family-specific):

-   **GADGETFAM**: Requires `<base>` (`SC`, `IC`, or `EC`) and `<gadget>` (`EQ` or `XOR`).
    
-   **SUCKRAD**: Requires an additional `<radius>` (integer value).

## Examples

**1. Generate a standard KBKF instance (Size 5):**
```bash 
python3 qbffamExt.py KBKF 5
```

**2. Generate a Gadget family instance (Size 10, Base IC, Gadget XOR):**
```bash 
python3 qbffamExt.py GADGETFAM 10 IC XOR
```

**3. Generate a Succinct k-Radius instance (Size 4, Radius 5):**
```bash 
python3 qbffamExt.py SUCKRAD 4 5
```

## Available Formula Families
The generator supports the following families:

### 1. Classic
These are standard benchmarks used in QBF research to analyze solver performance and theoretical hardness.

* **EQ**: Equality formulas.

* **EQ2**: Squared Equality formulas.

* **CP**: Completion Principle.

* **TRAP**: Trapdoor formulas designed to challenge CDCL solvers.

* **LONSING**: Hard instances based on the Pigeonhole Principle.

* **BEQ**: Blocked Equality formulas.

* **PARITY**: Parity Formulas.

* **LQ-PARITY**: Variation of Parity Formulas hard for LD.

* **QU-PARITY**: Variation of Parity Formulas hard for QU.

* **PARITYTrue**: Parity Formulas - Satisfiable.

* **KBKF**: Kleine Buening et al Formulas.

* **KBKF_QU**: Variation of Kleine Buening et al Formulas hard for QU.

* **KBKF_LD**: Variation of Kleine Buening et al Formulas hard for LD.

* **KBKFTrue**: Kleine Buening et al Formulas - Satisfiable.

* **PARITYTrue**: Kleine Buening et al Formulas.

* **KBKFQRE**: Kleine Buening et al Formulas - Satisfiable and quantifier rearranged.

### 2. Additional Families
These families include gadget-based constructions and encodings of hard mathematical problems.
You can find further information in the articles linked under Academic References.

* **GADGETFAM**: Generates formulas by combining a base formula (**SC, IC, EC**) with a specific gadget (**EQ, XOR**).

* **AESAT**: All-Equal-$\exist\forall$-3SAT.

	>*Given a 3-CNF formula $\varphi(X,Y)$, where $(X,Y)$ is a partition of $vars({\varphi})$, All-Equal-$\exist\forall$-3SAT asks, whether there is an assignment to the variables in $X$ such that for each assignment to the variables in $Y$there is at least one clause that contains only true or only false literals.*

* **SUCKRAD**: Succinct-k-Radius, Instances based on the k-radius problem on graphs with succinct representation.
	 >*Given a Galperin-Widgerson representation $C$ of a directed graph $G=(V_G,E_G)$ and an integer $k$. Succinct-k-Radius($C$) asks, whether $G$ has radius at most $k$.*


* **CLIQUECOLOURING**: k-Clique-Colouring, Instances based on $k=3$.
	>*Given a graph $G=(V,E)$ and an integer $k$, $k$-Clique-Colouring asks, whether there is a $k$-clique-colouring for $G$, i.e. a colouring of the Vertices in $V$ such that there are no monochromatic maximal cliques in $G$.*
	
* **SUBSETSUM**: Generalized Subset Sum.
	>*Given two integer vectors $u,v$ with $|u|=k$, $|v|=l$ and an integer $t$, Generalized-Subset-Sum asks, whether $\exists x\forall y\cdot(ux+vy\neq t)$, where $x,y$ are binary vectors with $|x|=k$, $|y|=l$, i.e. it looks for partial sums of $u,v$ that sum up to $t$.*

## Academic References 
If you use this tool or the formula families in your research, please cite the appropriate publications:
* for *Classic* families:
	>Beyersdorff, Olaf, et al. **"[Qbffam: A tool for generating QBF families from proof complexity.](https://doi.org/10.1007/978-3-030-80223-3_3)"** In *International Conference on Theory and Applications of Satisfiability Testing*. Cham: Springer International Publishing, 2021.

* for `GADGETFAM`:
	>Schleitzer, Agnes and Beyersdorff, Olaf. **"[Classes of hard formulas for QBF resolution.](https://doi.org/10.1613/jair.1.14710)"** *Journal of Artificial Intelligence Research* 77 (2023): 1455-1487.
* for `SUCKRAD`, `CLIQUECOLOURING`, `AESAT` and `SUBSETSUM`:
	>Schleitzer, Agnes and Beyersdorff, Olaf. **"[Computationally hard problems are hard for QBF proof systems too.](https://doi.org/10.1609/aaai.v39i11.33233)"** In *Proceedings of the AAAI Conference on Artificial Intelligence*, Vol. 39, No. 11, 2025.
	
## License
**Copyright (c)** 2020 Martina Seidl, Johannes Kepler University Linz, Austria

**Copyright (c)** 2026 Agnes Schleitzer, Friedrich Schiller University Jena, Germany

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the “Software”), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

## Authors & Credits

-   *Original Author:* **Martina Seidl**, Johannes Kepler University Linz, Austria (2020).
    
-   *Extensions:* **Agnes Schleitzer**, Friedrich Schiller University Jena, Germany (2026).
	>Contribution: Integration of advanced formula families including `GADGETFAM`, `AESAT`, `SUBSETSUM`, `CLIQUECOLOURING`, and `SUCKRAD`.
