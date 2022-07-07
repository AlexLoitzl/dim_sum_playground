# Coq development for DimSum: A Decentralized Approach to Multi-language Semantics and Verification

This is the Coq development for the POPL'23 submission "DimSum: A Decentralized Approach to Multi-language Semantics and Verification".

## Installation

It is recommended to install the dependencies of DimSum via [opam](https://opam.ocaml.org/doc/Install.html)
(version 2.0.0 or newer) into a new switch. This can be done via the
following commands.

```
opam switch create . ocaml-base-compiler.4.12.0 --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make builddep
eval $(opam env)
```

Afterwards, run the following command to build the development (replace 8 by a suitable number of parallel jobs to spawn):

```
make -j 8
```

You might need to run `eval $(opam env)` to update the environment of your shell.

## Linking the Coq development and the paper

Note the following differences between the paper and the Coq development:
- The language Rec is called Imp in the Coq development.
- "module" in the Coq development does not contain an initial state. A
  module as defined in the paper is "mod_state" in the Coq
  development. Combinators and languages in Coq are defined as Coq
  "module" and provide the initial state in a separate definition
  (usually called "initial_..._state").

Section 2:
- Verification of the running example including programs and specifications: theories/memmove.v
- Proof rules in Figure 5:
  - asm-link-syn-1: asm_link_refines_prod in theories/asm.v
  - asm-link-syn-2: asm_prod_refines_link in theories/asm.v
  - rec-link-syn-1: imp_link_refines_prod in theories/imp.v
  - rec-link-syn-2: imp_prod_refines_link in theories/imp.v
  - asm-link-horizontal: asm_prod_trefines in theories/asm.v
  - rec-link-horizontal: imp_prod_trefines in theories/imp.v
  - rec-wrapper-compat: imp_to_asm_trefines in theories/imp_to_asm.v
  - compiler-correct: compile_correct in theories/compiler/compiler.v
  - rec-to-asm-link: imp_to_asm_combine in theories/imp_to_asm.v
- Definition of the Rec to Asm wrapper: imp_to_asm in theories/imp_to_asm.v

Section 3.1:
- Definition of module: module, mod_state in theories/module.v
- Definition of the multi-step relation: lhas_trace in theories/lrefines.v
- Definition of refinement / simulation: sim in theories/proof_techniques.v / trefines in theories/trefines.v
  - The definition of the DimSum simulation is sim in theories/proof_techniques.v.
  - For historic reasons, the Coq development mostly uses an
    equivalent definition: trefines in theories/trefines.v
  - The two definitions are proven equivalent by sim_trefines in theories/proof_techniques.v.
- Lemma 3.1: trefines_preorder in theories/trefines.v
- Theorem 3.2: trefines_lrefines in theories/refines_meta.v

Section 3.2:
- Defintion of Spec: mod_itree in theories/itree.v
  - Note that Spec programs in the Coq development also have put and
    get constructors to access private state. This does not give
    additional expressive power but makes some spec programs easier to
    write.

Section 3.3:
- Product: mod_seq_product in theories/seq_product.v
- Filter: mod_seq_map in theories/seq_product.v
  - Note that the filter is defined using more primitive combinators
    not discussed in the paper.
- Linking: mod_link in theories/link.v
- (Kripke) wrappers: mod_prepost in theories/prepost.v
- Rules in Figure 10:
  - product-compat: mod_seq_product_trefines in theories/seq_product.v
  - filter-compat: mod_seq_map_trefines in theories/seq_product.v
  - link-compat: mod_link_trefines in theories/link.v
  - wrapper-compat: mod_prepost_trefines in theories/prepost.v

Section 4:
- Definition of Asm:
  - Syntax: deep_asm_instr in theories/asm.v
  - Module Semantics: asm_module, deep_to_asm_instrs in theories/asm.v
  - Syntactic Linking: asm_link in theories/asm.v
  - Semantic Linking: asm_prod in theories/asm.v
- Definition of Rec:
  - Syntax: expr in theories/imp.v
  - Module Semantics: imp_module in theories/imp.v
  - Syntactic Linking: imp_link in theories/imp.v
  - Semantic Linking: imp_prod in theories/imp.v
- Coroutine Library:
  - Definition of the linking operator: coro_prod in theories/coroutine.v
  - yield: yield_asm in theories/coroutine.v
  - coro-link: coro_spec in theories/coroutine.v
  - Verification of the example: theories/coroutine_example.v

Section 5:
- Compiler: theories/compiler/compiler.v
  - Compiler correctness: compiler_correct in theories/compiler/compiler.v
    - Note that the compiler_correct lemma only allows compiling
      single functions but they can be combined using
      imp_to_asm_combine in theories/imp_to_asm.v and the equivalence
      of syntactic and semantic linking.
  - SSA pass: theories/compiler/ssa.v
  - Linearize pass: theories/compiler/linearize.v
  - Mem2Reg pass: theories/compiler/mem2reg.v
  - Codegen pass: theories/compiler/codegen.v
- Rec-to-rec wrapper: imp_heap_bij in theories/imp_heap_bij_own.v
- rec-to-asm-vertical: i2a_bij_vertical in theories/i2a_bij_vertical.v
