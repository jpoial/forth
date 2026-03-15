import os
import sys

def convert_text_to_scr(input_path, output_path, width=64):
    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
        
        # Process each line to ensure correct length
        processed_lines = []
        for line in lines:
            # Strip newline characters
            line = line.rstrip('\n\r')
            # Truncate or pad to required width
            line = line[:width].ljust(width)
            processed_lines.append(line)
        
        # Join all lines and encode
        try:
            content = ''.join(processed_lines).encode('cp850')
        except:
            content = ''.join(processed_lines).encode('latin-1')
        
        # Write to output file
        with open(output_path, 'wb') as f:
            f.write(content)
        
        print(f"Converted {input_path} to {output_path}")
        print(f"Total lines: {len(processed_lines)}")
        print(f"File size: {len(content)} bytes")
        
    except Exception as e:
        print(f"Error converting file: {e}")

def main():
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        # Generate output file name
        if '_CONVERTED.FS' in input_file:
            output_file = input_file.replace('_CONVERTED.FS', '.SCR')
        else:
            name, ext = os.path.splitext(input_file)
            output_file = name + '.SCR'
        convert_text_to_scr(input_file, output_file, 64)
    else:
        # If no file specified, convert CONSTR_CONVERTED.FS as default
        input_file = 'forth8332/CONSTR_CONVERTED.FS'
        output_file = 'forth8332/CONSTR.SCR'
        convert_text_to_scr(input_file, output_file, 64)
    
    print("\n--- Conversion complete ---")

if __name__ == "__main__":
    main()
