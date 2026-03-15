import os

def analyze_scr_file(file_path):
    try:
        with open(file_path, 'rb') as f:
            content = f.read()
        
        print(f"File size: {len(content)} bytes")
        
        # Check for line terminators
        has_crlf = b'\r\n' in content
        has_lf = b'\n' in content
        has_cr = b'\r' in content
        
        print(f"CRLF line terminators: {has_crlf}")
        print(f"LF line terminators: {has_lf}")
        print(f"CR line terminators: {has_cr}")
        
        # Look for common Forth structures
        print("\nFirst 200 bytes of content (hex and ASCII):")
        for i in range(0, min(200, len(content)), 16):
            chunk = content[i:i+16]
            hex_str = ' '.join(f'{byte:02x}' for byte in chunk)
            ascii_str = ''.join(chr(byte) if 32 <= byte < 127 else '.' for byte in chunk)
            print(f"{i:04x}  {hex_str:<48}  {ascii_str}")
            
        print("\n\n--- End of analysis ---")
        
    except Exception as e:
        print(f"Error analyzing file: {e}")

# Run analysis
analyze_scr_file('forth8332/CONSTR.SCR')
