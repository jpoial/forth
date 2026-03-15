# Forth Screen File (.scr) Editor Support for VSCode

## Overview

This project provides tools to convert Forth screen files (.scr) to human-readable text files and vice versa, making them editable in VSCode.

## What are Forth Screen Files?

Forth screen files are traditional Forth source files that follow a 16x64 character grid format. Each "screen" contains 1024 bytes (16 lines × 64 characters) without line terminators. This format makes them difficult to edit in standard text editors like VSCode.

## Tools Provided

### 1. `convert_scr.py`
Converts a .scr file to a human-readable text file with proper line breaks.

**Usage:**
```bash
python3 convert_scr.py input_file.scr
```

This will create `input_file_CONVERTED.FS` in the same directory.

### 2. `convert_back_scr.py`
Converts the edited text file back to .scr format.

**Usage:**
```bash
python3 convert_back_scr.py input_file_CONVERTED.FS
```

This will create `input_file.scr` in the same directory.

### 3. VSCode Tasks
You can also use VSCode tasks to perform conversions:
- `Convert SCR to Text`: Converts the currently open .scr file
- `Convert Text to SCR`: Converts the currently open CONVERTED.FS file back to .scr format

To run a task:
1. Press `Ctrl+Shift+P`
2. Type `Tasks: Run Task`
3. Select the desired task

## How to Edit .scr Files

1. Open the .scr file in VSCode
2. Run the `Convert SCR to Text` task (or use the Python script)
3. Edit the generated `_CONVERTED.FS` file
4. Run the `Convert Text to SCR` task to save your changes back to .scr format

## Configuration

The following VSCode configuration files are provided:

- `settings.json`: Associates .scr files with Forth language
- `language-configuration.json`: Forth language configuration
- `tasks.json`: Conversion and run tasks
- `launch.json`: Debug/run configurations

## Notes

- The converter assumes CP850 encoding for .scr files (common in DOS-based Forth systems)
- Each line is limited to 64 characters when converting back to .scr format
- Overflowing lines will be truncated

## Example

```bash
# Convert CONSTR.SCR to editable format
python3 convert_scr.py forth8332/CONSTR.SCR

# Edit the converted file
code forth8332/CONSTR_CONVERTED.FS

# Convert back to .scr format
python3 convert_back_scr.py forth8332/CONSTR_CONVERTED.FS
```
