(*$V-*)
IMPLEMENTATION MODULE Terminal ;

(* Core library interface *)

IMPORT IO ;

VAR
  CharBuffered : BOOLEAN ;
  SaveChar     : CHAR ;

PROCEDURE Read ( VAR v : CHAR ) ;
BEGIN
  IF CharBuffered THEN
    v := SaveChar ;
    CharBuffered := FALSE ;
  ELSE
    SaveChar := IO.RdCharDirect() ;
    v := SaveChar ;
  END ;
END Read ;


PROCEDURE ReadAgain ;
BEGIN
  CharBuffered := TRUE ;
END ReadAgain ;


PROCEDURE Write    ( v : CHAR ) ;
BEGIN
  IO.WrChar(v) ;
END Write ;

PROCEDURE WriteLn ;
BEGIN
  IO.WrLn ;
END WriteLn ;

PROCEDURE WriteString ( s : ARRAY OF CHAR ) ;
BEGIN
  IO.WrStr(s) ;
END WriteString ;

BEGIN
  CharBuffered := FALSE ;
  SaveChar := CHR(0) ;
END Terminal.

