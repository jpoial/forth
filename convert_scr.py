import os
import sys

def convert_scr_to_text(input_path, output_path, width=64):
    try:
        with open(input_path, 'rb') as f:
            content = f.read()
        
        # Convert to text with proper encoding (assuming CP850 or similar)
        try:
            text = content.decode('cp850')
        except:
            try:
                text = content.decode('latin-1')
            except:
                text = content.decode('utf-8', errors='ignore')
        
        # Split into lines of specified width
        lines = []
        for i in range(0, len(text), width):
            line = text[i:i+width]
            # Strip trailing whitespace if needed
            # line = line.rstrip()
            lines.append(line)
        
        # Write to output file
        with open(output_path, 'w', encoding='utf-8') as f:
            for line in lines:
                f.write(line + '\n')
        
        print(f"Converted {input_path} to {output_path}")
        print(f"Total lines: {len(lines)}")
        print(f"Line width: {width}")
        
    except Exception as e:
        print(f"Error converting file: {e}")

def main():
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        # Generate output file name
        name, ext = os.path.splitext(input_file)
        output_file = name + '_CONVERTED.FS'
        convert_scr_to_text(input_file, output_file, 64)
    else:
        # If no file specified, convert CONSTR.SCR as default
        input_file = 'forth8332/CONSTR.SCR'
        output_file = 'forth8332/CONSTR_CONVERTED.FS'
        convert_scr_to_text(input_file, output_file, 64)
    
    print("\n--- Conversion complete ---")

if __name__ == "__main__":
    main()
