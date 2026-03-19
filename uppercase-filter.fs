\ A simple GForth filter that converts lowercase letters to uppercase.
\ Usage: gforth uppercase-filter.fs < input.txt

: uppercase-filter ( -- )
  begin
    stdin key-file
    dup #eof <>
  while
    toupper emit
  repeat
  drop ;

uppercase-filter
bye
