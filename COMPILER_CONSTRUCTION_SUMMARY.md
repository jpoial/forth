# Compiler Construction Summary

## Scope

This repository mixes a small GForth learning area with a much larger historical PC/FORTH archive in `forth8332/`.
This summary concentrates on the compiler construction side of that archive.

The best way to read `forth8332/` is as a toolkit for building language processors inside Forth:

- grammar descriptions are written in screen files
- a constructor turns those descriptions into compact tables and helper files
- semantic actions are implemented as Forth words
- image builders assemble the required modules into runnable compiler images

Some comments and strings in the converted files contain mojibake from DOS-era encodings, but the architecture is still readable.

## What The Archive Contains

The compiler-related files fall into a few clear groups.

### 1. Image builders

These files load a set of modules and then save a runnable compiler image.

- `forth8332/M2LINK_CONVERTED.FS` - main Modula-2 compiler image
- `forth8332/CROSS_CONVERTED.FS` - Modula-2 cross-compiler image
- `forth8332/TESTLINK_CONVERTED.FS` - debug-oriented compiler image
- `forth8332/TGO_CONVERTED.FS` - debugging image variant

### 2. Grammar specifications

These files define the source language grammar plus embedded semantic hooks.

- `forth8332/MODULA_CONVERTED.FS`
- `forth8332/JPIGRAM_CONVERTED.FS`
- `forth8332/UUSMOD_CONVERTED.FS`
- `forth8332/REALGRAM_CONVERTED.FS`
- `forth8332/MOD2VI_CONVERTED.FS`

Typical productions look like:

```text
TypeIdent = ident '='  #PRE TYPE$# .
varid = [I]  #PRE TYPE-DUP VAR$# .
```

This means the grammar is syntax plus actions, not syntax alone.

### 3. Constructor / parser-generator infrastructure

These files are responsible for turning grammar descriptions into executable tables and supporting artifacts.

- `forth8332/CONSTR_CONVERTED.FS` - the constructor itself
- `forth8332/JMODANAL_CONVERTED.FS`
- `forth8332/RMODANAL_CONVERTED.FS`
- `forth8332/3LC_CONVERTED.FS`
- `forth8332/TURBOC_CONVERTED.FS`
- `forth8332/JARC_CONVERTED.FS`

The constructor side contains lexical analysis, grammar packing, semantic text handling, conflict analysis, and file emission.

### 4. Semantic and symbol-table machinery

These files define the compiler's internal model and code-generation behavior.

- `forth8332/TABEL_CONVERTED.FS` - table format and type predicates
- `forth8332/POHI_CONVERTED.FS` - object and type creation
- `forth8332/REC_CONVERTED.FS` - record and variant-record semantics
- `forth8332/TRANSEXP_CONVERTED.FS` - expression typing and code generation
- `forth8332/SEMANTIC_CONVERTED.FS` - runtime semantics for generated code
- `forth8332/SEMANTC_CONVERTED.FS` - cross-compiler variant of runtime semantics

### 5. Support modules

- `forth8332/BINLINK_CONVERTED.FS` and `forth8332/BINLINKC_CONVERTED.FS` - relocation and linking
- `forth8332/LINKPOHI_CONVERTED.FS` - shared link-layer support
- `forth8332/FLOAT_CONVERTED.FS` - floating-point bridge
- `forth8332/ASM8632_CONVERTED.FS` - assembler support
- `forth8332/MODLIB_CONVERTED.FS` - supplemental library helpers
- `forth8332/TRACE32_CONVERTED.FS` - tracer/debugger for colon definitions

## High-Level Construction Pipeline

The compiler construction algorithm in this archive is best understood as a staged, image-based pipeline.

### Stage 1. Define the language

The language grammar is written in files such as `MODULA_CONVERTED.FS`.
Productions contain embedded markers like `#PRE`, `#POST`, `#REG`, and `#PERM`.
Those markers connect grammar reductions to Forth semantic actions.

### Stage 2. Construct parsing artifacts

`CONSTR_CONVERTED.FS` acts as a constructor for the grammar machinery.
It contains:

- a metalexer and metaparser for reading grammar descriptions
- symbol and production table builders
- semantic text packing
- hash-based lookup structures
- conflict analysis for parser states
- output writers for generated artifacts

The constructor writes multiple derived files such as grammar, symbol, parameter, and hash-related outputs.
Examples visible in the code include extensions like `.GRA`, `.SYM`, `.PAR`, `.PRM`, `.HLX`, and `.HGR`.

### Stage 3. Build analyzer / parser runtime tables

Files such as `JMODANAL_CONVERTED.FS`, `RMODANAL_CONVERTED.FS`, `3LC_CONVERTED.FS`, and `TURBOC_CONVERTED.FS` show the next step.
They contain the scanner, parser, and generator runtime, along with arrays like `PRODSEM` and `TERMSEM`.

These modules appear to:

- load grammar-related files
- allocate production and terminal semantic arrays
- attach semantic text to productions and tokens
- execute the generated parsing algorithm over source text

### Stage 4. Build compiler-internal objects

When the parser reduces a rule, semantic hooks call Forth words in the compiler core.

Examples:

- `TYPE$`, `PTRTYPE$`, `IMPORT$`, `CREATE-OBJ` in `POHI_CONVERTED.FS`
- `EL$`, `CEL$`, `MRT`, `SELECTOR$`, `CASECHECK` in `REC_CONVERTED.FS`

This is where declarations turn into internal tables, types, record layouts, and symbol entries.

### Stage 5. Perform type analysis and emit code

`TRANSEXP_CONVERTED.FS` contains the rules for compatibility and assignment, plus code emission helpers for variables, expressions, and procedure calls.

This is where the compiler decides things like:

- whether two types are compatible
- how to build addresses for globals, locals, and record fields
- how to compile procedure calls and control structures

### Stage 6. Rely on runtime semantics

`SEMANTIC_CONVERTED.FS` defines runtime words used by emitted threaded code.
Examples include literals, procedure environment setup, local-memory allocation, and procedure-body execution.

The compiled output is therefore not just raw machine code.
It is closely tied to the Forth runtime model provided by the semantic module.

### Stage 7. Relocate, link, and save an image

Image builders such as `M2LINK_CONVERTED.FS` and `CROSS_CONVERTED.FS` load the required modules and save a runnable compiler image.

`BINLINK_CONVERTED.FS` and `BINLINKC_CONVERTED.FS` handle relocation, pass-table management, and binary linking.

## Why The Constructor Matters

`CONSTR_CONVERTED.FS` is the key file for understanding the "compiler compiler" aspect of the project.

It is not the Modula-2 compiler itself.
Instead, it is the machinery used to translate grammar descriptions and semantic annotations into the compact runtime data structures that later compiler images consume.

Important aspects visible in the constructor:

- meta-lexical analysis for grammar text
- meta-actions for `#PRE`, `#POST`, `#REG`, and `#PERM`
- grammar packing and symbol numbering
- hash-based storage for lexemes and rules
- conflict checking phases
- overlay-based staging to save memory

## Overlay-Based Staging

One especially important construction technique is the use of overlays in `CONSTR_CONVERTED.FS`.

The pattern is:

- mark the start of a temporary phase with `HERE CONSTANT OVERLAY`
- store intra-phase references as offsets relative to `OVERLAY`
- reconstruct absolute addresses with `OVERLAY +`
- reclaim memory for the whole phase with `OVERLAY forget`

This allows the constructor to run large multi-phase analyses in constrained DOS/Forth memory.
It also isolates phase-specific helper code that is only needed temporarily.

In practice, the constructor uses overlays for things like:

- temporary I/O hook installation
- metacompilation support
- conflict analysis phases
- later symbol-table extension passes

## How Grammar Hooks Connect To Compiler Semantics

A useful mental model is:

- grammar files describe when a construct is recognized
- `POHI`, `REC`, and related modules describe what object or type to create
- `TRANSEXP` describes how expressions and statements become executable code
- `SEMANTIC` describes what that generated code does at runtime

For example, a grammar production for a type declaration can invoke `TYPE$`.
That hook then creates or fills a compiler table entry representing the declared type.

This means syntax, semantic analysis, and code generation are tightly interleaved.
The system is strongly syntax-directed.

## M2LINK vs CROSS

Two key builder files show how the same compiler core can be packaged differently.

- `M2LINK_CONVERTED.FS` builds the main Modula-2 compiler image
- `CROSS_CONVERTED.FS` builds the cross-compiler image

The cross build uses cross-oriented variants of some modules, notably:

- `SEMANTC_CONVERTED.FS` instead of `SEMANTIC_CONVERTED.FS`
- `BINLINKC_CONVERTED.FS` instead of `BINLINK_CONVERTED.FS`

So the project supports multiple compiler configurations assembled from mostly shared pieces.

## Suggested Reading Order

If you want to understand the compiler construction story end to end, this reading order works well:

1. `forth8332/CONSTR_CONVERTED.FS`
2. `forth8332/MODULA_CONVERTED.FS`
3. `forth8332/TABEL_CONVERTED.FS`
4. `forth8332/POHI_CONVERTED.FS`
5. `forth8332/REC_CONVERTED.FS`
6. `forth8332/TRANSEXP_CONVERTED.FS`
7. `forth8332/SEMANTIC_CONVERTED.FS`
8. `forth8332/BINLINK_CONVERTED.FS`
9. `forth8332/M2LINK_CONVERTED.FS`
10. `forth8332/CROSS_CONVERTED.FS`

If you want to understand the generated analyzer side in more detail, add:

11. `forth8332/JMODANAL_CONVERTED.FS`
12. `forth8332/RMODANAL_CONVERTED.FS`

## Short Conclusion

The archive implements a full compiler-construction environment inside Forth.
It combines:

- grammar-driven parsing
- embedded semantic actions
- custom symbol and type tables
- syntax-directed code generation
- relocation and binary linking
- staged image construction under tight memory constraints

The most important file for the construction story is `CONSTR_CONVERTED.FS`, because it shows how grammar descriptions are converted into the packed artifacts and runtime tables used by the later compiler images.

## Thesis Crosswalk

The 1986 dissertation behind this archive is not reproduced here as a single frozen code snapshot.
Instead, the repository appears to preserve a later and larger evolution of the same ideas.

## Thesis Chapter-By-Chapter Summary

The dissertation is structured as an argument that Forth can support not only compact implementation, but also more formal and reliable compiler construction.

### Introduction

The introduction motivates the work from the constraints of microcomputers and personal computers of the period.
It argues that compiler-construction tools must be portable, compact, and economical in memory, which makes Forth attractive.
At the same time, it identifies a gap: existing Forth-oriented systems are flexible but weak in formal description methods and in early detection of semantic and stack-related errors.

### Chapter 1. Programming Systems Based On Forth

Chapter 1 surveys Forth and Forth-like implementation systems as a foundation for compiler construction.
It reviews the language's main strengths: compactness, extensibility, portability, interactivity, and suitability for building integrated tool environments.
It also highlights the language's weaknesses, especially the lack of static control over stack-passed parameters and the resulting difficulty of documenting and verifying programs.

The chapter then turns to Forth-oriented compiler-construction systems, with particular attention to the Tartu system.
It explains syntax-directed translation as the practical method used in these systems, shows how semantic procedures are tied to grammar structure, and discusses limitations of existing approaches.
The chapter's conclusion is that Forth is a strong implementation base, but reliability requires a more formal specification discipline.

### Chapter 2. Algebra Of Forth Specifications

Chapter 2 introduces the dissertation's main formal apparatus: an algebra of Forth-program specifications.
Specifications are modeled as relations between input and output stack words, and the chapter studies the algebraic properties of these specifications under composition.
This gives a mathematical language for talking about what a Forth word expects and produces.

The chapter then defines a partial order on specifications and studies upper and lower bounds in that order.
Those constructions are used to define notions of program correctness, compatibility, and closure.
The practical purpose of the chapter is to turn informal stack comments into a structure that can support reasoning and checking.

### Chapter 3. Applying Specification Algebra In Forth-Oriented Compiler Systems

Chapter 3 applies the specification algebra to syntax-directed translation systems whose semantic language is Forth.
It defines correctness for a translation scheme and proves a key closure theorem for object programs generated by such schemes.
In effect, the chapter argues that if the semantic pieces are specified correctly, the generated programs remain well-formed in the relevant sense.

The chapter then develops algorithms for checking translation correctness.
These algorithms are meant to catch errors in language descriptions and semantic actions earlier than normal debugging would.
The chapter ends with practical use of the method inside a Forth-oriented compiler-construction setting, connecting the theory back to real translator implementation.

### Conclusion

The conclusion summarizes the main contributions:

- a formal notion of Forth-word and Forth-program specification
- an algebra over those specifications
- a notion of correctness for Forth programs and syntax-directed descriptions
- checking methods that improve the reliability of Forth-oriented compiler systems

It also points to further work in automated language implementation and stronger static checking.

### Appendices

The appendices are implementation-oriented and are especially relevant to this repo:

- Appendix 1 presents the implementation of algebraic operations on Forth specifications
- Appendix 2 presents the implementation of static type and stack checking for linear Forth programs

These appendices are the clearest bridge between the thesis and files such as `SPEC32_CONVERTED.FS` and the `TCOMP` family.

## Main Theorem Explained

The dissertation's main mathematical result appears in Chapter 3 as Theorem 5.
Its purpose is to characterize when a syntax-directed translation scheme, whose semantic language is Forth, produces stack-correct object programs.

The setup is:

- each output-language terminal symbol is assigned a Forth stack specification
- a specification has the form `[input -- output]`
- specifications can be composed, which models sequencing Forth words
- for each nonterminal `A`, the grammar determines a language `L(A)` of output strings derivable from `A`
- each such output string `w` has a composed specification `s(w)`

The theorem then states that the following are equivalent:

1. All output sequences generated by the translation scheme are correct or closed in the required stack-discipline sense.
2. A system of inequalities `I(T, s)`, constructed from the grammar `T` and the terminal specifications `s`, has a solution.
3. For every nonterminal `A`, the set `{ s(w) | w in L(A) }` has an infimum, written as `m(A)`.

The third condition is the most informative one mathematically.
It says that all object programs derivable from a nonterminal share a common lower-bound specification.
That lower bound acts as the best guaranteed summary of the stack effect of everything derivable from `A`.

Why this matters:

- it turns translator correctness into a finite algebraic constraint problem
- it gives a constructive basis for the checking algorithms in Chapter 3.2
- it shows that syntax-directed translation correctness can be analyzed with order-theoretic tools rather than only by testing generated programs

An important nuance is that the theorem does not require all generated programs to have exactly the same specification.
Instead, it requires them to be compatible enough that their family has a well-defined greatest lower bound in the specification order.
That is the thesis's precise notion of semantic coherence for generated Forth object programs.

The most useful thesis-to-repo mapping is:

| Thesis topic | Best matching files in this repo | Notes |
| --- | --- | --- |
| Algebra of Forth specifications | `forth8332/SPEC32_CONVERTED.FS` | Closest match to the dissertation appendix on formal specifications of Forth words |
| Static stack/type checking for linear Forth programs | `forth8332/TCOMP06_CONVERTED.FS`, `forth8332/TCOMP16_CONVERTED.FS`, `forth8332/TCOMP26_CONVERTED.FS`, `forth8332/TCOMP36_CONVERTED.FS`, `forth8332/TCOMPCA_CONVERTED.FS` | Best match for the dissertation appendix on static control of stack-passed parameters |
| Describing source languages with embedded semantic hooks | `forth8332/MODULA_CONVERTED.FS`, `forth8332/MOD2VI_CONVERTED.FS`, `forth8332/JPIGRAM_CONVERTED.FS`, `forth8332/REALGRAM_CONVERTED.FS`, `forth8332/UUSMOD_CONVERTED.FS` | Grammar files interleave productions with `#PRE`, `#POST`, `#REG`, and `#PERM` actions |
| Constructor for turning grammar descriptions into runtime artifacts | `forth8332/CONSTR_CONVERTED.FS` | Core "compiler compiler" file in the archive |
| Analyzer/runtime built from generated grammar artifacts | `forth8332/JMODANAL_CONVERTED.FS`, `forth8332/RMODANAL_CONVERTED.FS` | Parser/analyzer side that consumes generated tables and semantic text |
| Semantic object construction and type handling | `forth8332/POHI_CONVERTED.FS`, `forth8332/REC_CONVERTED.FS`, `forth8332/TRANSEXP_CONVERTED.FS` | Compiler-internal objects, records, type compatibility, and expression translation |
| Runtime semantics for generated code | `forth8332/SEMANTIC_CONVERTED.FS` | Execution model used by emitted threaded code |
| Linking and final compiler images | `forth8332/BINLINK_CONVERTED.FS`, `forth8332/BINLINKC_CONVERTED.FS`, `forth8332/M2LINK_CONVERTED.FS`, `forth8332/CROSS_CONVERTED.FS` | Final relocation, linking, and image assembly |

If you want to read the repo as a dissertation companion, a good order is:

1. `forth8332/SPEC32_CONVERTED.FS`
2. `forth8332/CONSTR_CONVERTED.FS`
3. one grammar file such as `forth8332/MODULA_CONVERTED.FS`
4. `forth8332/POHI_CONVERTED.FS`
5. `forth8332/REC_CONVERTED.FS`
6. `forth8332/TRANSEXP_CONVERTED.FS`
7. `forth8332/SEMANTIC_CONVERTED.FS`
8. one `TCOMP` file
