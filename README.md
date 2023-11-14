# Concurrent Incorrectness Separation Logic in Coq

This repository contains the Coq mechanization of my master thesis.
The mechanization is divided into 7 files.

1. `separation_logic.v`: The basics of separation logic. Also contains the values of both our languages.
2. `memory_error_definitions.v`: The definitions for chapter 3 in the thesis (memory error language and CISL triples)
3. `memory_error_theorems.v`: The lemmas for chapter 3 in the thesis (memory error language and CISL triples)
4. `permutation_definitions.v`: The definitions for permutations (sections 4.2 and 4.3 in the thesis)
5. `permutation_theorems.v`: The lemmas for permutations (sections 4.2 and 4.3 in the thesis)
6. `deadlock_definitions.v`: The definitions for chapter 4 in the thesis (section 4.1, 4.4, and 4.5)
7. `deadlock_theorems.v`: The proof of the soundness theorem of chapter 4 (section 4.6)

## Coq version

This mechanization was done using Coq Platform 2023.03.0 (Coq version 8.17.1~2023.08)  
It uses some lemmas and definitions from packages that are provided by Coq platform.  
Specifically, we use:

- stdpp version 1.8.0
- iris version 4.0.0

This mechanization has been checked to work with the above versions on Windows 10 using the recommended Windows (64 bit) installer of Coq Platform and all default settings.