# AGENTS.md

This file provides guidance to agents when working with code in this repository.

## Project Overview
- **Language**: Forth
- **Interpreter**: GForth (GNU Forth)
- **File Extension**: .fs (Forth source files)

## Running Forth Files
- **F5 Key**: Runs the currently open .fs file using GForth (configured via launch.json)
- **Terminal Command**: `gforth filename.fs`
- **VSCode Tasks**: "Run Forth File" task available in tasks.json

## Key Files
- [`proov.fs`](proov.fs): Example Forth program with tests and definitions
- [`gforth.fi`](gforth.fi): GForth documentation in Finnish

## Forth Environment
This project uses standard GForth syntax and conventions. The proov.fs file demonstrates:
- Basic word definitions
- Conditional structures
- Loops
- Memory manipulation
- Input/output operations

## Getting Started
1. Ensure GForth is installed (available via package managers like apt-get, brew, etc.)
2. Open any .fs file in VSCode
3. Press F5 to run the file in GForth
