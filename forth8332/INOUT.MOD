(*$V-*)
IMPLEMENTATION MODULE InOut ;
IMPORT IO,Str,Terminal,ASCII ;
CONST
  RestoreDev = 'CON' ;


PROCEDURE AddExt ( VAR fn : ARRAY OF CHAR ; ext : ARRAY OF CHAR ) ;
VAR
  i,p : CARDINAL ;
BEGIN
  p := Str.Length(fn) ;
  i := 1 ;
  LOOP
    IF (i>p)OR(i=5)OR(fn[p-i] = '\') THEN
      Str.Append(fn,'.');
      Str.Append(fn,ext);
      RETURN ;
    END ;
    IF fn[p-i]='.' THEN RETURN END ;
    INC(i,1) ;
  END ;
END AddExt ;

PROCEDURE OpenInput   ( defext : ARRAY OF CHAR ) ;
VAR
  fn : ARRAY[0..79] OF CHAR ;
BEGIN
  ReadString(fn) ;
  AddExt(fn,defext) ;
  IO.RedirectInput(fn) ;
  Done := TRUE ;
END OpenInput ;

PROCEDURE OpenOutput  ( defext : ARRAY OF CHAR ) ;
VAR
  fn : ARRAY[0..79] OF CHAR ;
BEGIN
  ReadString(fn) ;
  AddExt(fn,defext) ;
  IO.RedirectOutput(fn) ;
  Done := TRUE ;
END OpenOutput ;

PROCEDURE CloseInput ;
BEGIN
  IO.RedirectInput(RestoreDev) ;
  Done := TRUE ;
END CloseInput ;

PROCEDURE CloseOutput ;
BEGIN
  IO.RedirectOutput(RestoreDev) ;
  Done := TRUE ;
END CloseOutput ;

PROCEDURE Read ( VAR v : CHAR ) ;
VAR
  b : BOOLEAN ;
BEGIN
  REPEAT
    Terminal.Read(v) ;
  UNTIL v<>ASCII.lf ; (* LF ignored *)
  IF v=ASCII.cr THEN
    v := EOL ;
  END ;
  Write(v) ;
  Done := TRUE ;
END Read ;

PROCEDURE ReadString  ( VAR v : ARRAY OF CHAR ) ;
VAR
  c : CHAR ;
  line : ARRAY[0..255] OF CHAR ;
  p : CARDINAL ;
BEGIN
  p := 0 ;
  REPEAT Read(c) UNTIL c<>' ' ;
  LOOP
     IF (c=ASCII.bs)OR(c=ASCII.del) THEN
       IF p>0 THEN
         DEC(p,1) ;
         IO.WrChar(' ');
         IO.WrChar(ASCII.bs);
       END ;
     ELSIF (c>' ') THEN
       IF p<SIZE(line) THEN
         line[p] := c ;
         INC(p,1) ;
       END ;
     ELSE EXIT ;
     END ;
     Read(c) ;
  END ;
  termCH := c ;
  IF p<SIZE(line) THEN line[p] := CHR(0) END ;
  Str.Copy(v,line) ;
  Done := TRUE ;
END ReadString ;

PROCEDURE ReadCard    ( VAR v : CARDINAL ) ;
VAR
  line : ARRAY[0..79] OF CHAR ;
BEGIN
  ReadString(line) ;
  v := Str.StrToCard(line,10,Done) ;
END ReadCard ;

PROCEDURE ReadInt     ( VAR v : INTEGER ) ;
VAR
  line : ARRAY[0..79] OF CHAR ;
BEGIN
  ReadString(line) ;
  v := Str.StrToInt(line,10,Done) ;
END ReadInt ;



PROCEDURE Write       ( v : CHAR ) ;
BEGIN
  IF v=EOL THEN IO.WrLn ;
           ELSE IO.WrChar(v) ;
  END ;
  Done := IO.OK ;
END Write ;

PROCEDURE WriteLn ;
BEGIN
  IO.WrLn ;
  Done := IO.OK ;
END WriteLn ;

PROCEDURE WriteString ( v : ARRAY OF CHAR ) ;
VAR
  buff : ARRAY[0..256] OF CHAR ;
  i,j  : CARDINAL ;
  c    : CHAR ;

  PROCEDURE OutBuff ;
  BEGIN
     buff[j] := CHR(0) ;
     IO.WrStr(buff) ;
     IF NOT IO.OK THEN Done := FALSE END ;
     j := 0 ;
  END OutBuff;

BEGIN
  i := 0 ; j := 0 ;
  Done := TRUE ;
  LOOP
    IF i>HIGH(v) THEN OutBuff ; RETURN END ;
    c := v[i] ; INC(i,1) ;
    IF c=CHR(0) THEN OutBuff ; RETURN END ;
    IF c=EOL THEN OutBuff ; WriteLn
    ELSE
      buff[j] := c ; INC(j,1) ;
      IF j=SIZE(buff)-1 THEN OutBuff END ;
    END ;
  END ;
END WriteString ;

PROCEDURE WriteCard   ( v : CARDINAL ;      w : CARDINAL ) ;
BEGIN
  IO.WrCard(v,INTEGER(w)) ;
  Done := IO.OK ;
END WriteCard ;

PROCEDURE WriteInt    ( v : INTEGER ;       w : CARDINAL ) ;
BEGIN
  IO.WrInt(v,INTEGER(w)) ;
  Done := IO.OK ;
END WriteInt ;

PROCEDURE WriteOct    ( v : CARDINAL ;      w : CARDINAL ) ;
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  Str.CardToStr( v,s,8,Done );
  IF Done THEN
    IO.WrStrAdj( s,INTEGER(w) );
    Done := IO.OK ;
  END;
END WriteOct ;

PROCEDURE WriteHex    ( v : CARDINAL ;      w : CARDINAL ) ;
BEGIN
  IO.WrHex(v,INTEGER(w)) ;
  Done := IO.OK ;
END WriteHex ;

BEGIN
  Done   := TRUE ;
  termCH := CHR(0) ;
END InOut.
