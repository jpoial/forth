(* Copyright (C) 1987 Jensen & Partners International *)

(*$S-,R-,I-*)
IMPLEMENTATION MODULE IO;

FROM Str    IMPORT Length,Compare,IntToStr,CardToStr,(* RealToStr, *) StrToInt,
                   StrToCard,(* StrToReal, *) InCharSet,InclChar,EmptyCharSet;

IMPORT Str;


CONST
  TrueStr = 'TRUE';


VAR
  LWW     : BOOLEAN;
  Buffer  : ARRAY[0..MaxRdLength-1] OF CHAR;
  s,e     : CARDINAL;


(*$V-*)

PROCEDURE KeyPressed (): BOOLEAN;
BEGIN
  FORTH
    /$ ?TERMINAL $/
  END  
END KeyPressed;

PROCEDURE MEXPECT(VAR Buffer: ARRAY OF CHAR; L: CARDINAL);
BEGIN
  FORTH
    /$ addr Buffer 2 - addr L @ expect $/
  END
END MEXPECT;
     
PROCEDURE TerminalRdStr(VAR string: ARRAY OF CHAR);
VAR
  H : CARDINAL;
  I : CARDINAL;
  L : CARDINAL;
  InputBuffer :RECORD 
                  LenBuf : CHAR;
                  Len    : CHAR;
                  Buf    : ARRAY[0..81] OF CHAR;
               END;
BEGIN
  IF Prompt AND NOT LWW THEN WrStr('?'); END;
  LWW := FALSE;
  H := HIGH(string);
  IF H > 80 THEN
    L := 82;
  ELSE
    L := H+2;
  END;
  MEXPECT(InputBuffer.Buf,L);
  I := ORD(InputBuffer.Len);
  IF I <= H  THEN
    string[I] := CHR(0);
  END;
  WHILE (I>0) DO
    DEC(I,1);
    string[I] := InputBuffer.Buf[I];
  END;
  WrLn;
END TerminalRdStr;


PROCEDURE WrStr(S: ARRAY OF CHAR);
BEGIN
  WrStrRedirect(S);
END WrStr;

PROCEDURE RdStr ( VAR S : ARRAY OF CHAR );
BEGIN
  RdStrRedirect(S);
END RdStr;


PROCEDURE RdBuff;
VAR
  p,h : CARDINAL;
BEGIN
  RdStrRedirect(Buffer);
  p := Length(Buffer);
  h := SIZE(Buffer)-1;
  IF p>h-1 THEN p := h-1; END;
  Buffer[p] := CHR(13); INC(p,1);
  Buffer[p] := CHR(10); INC(p,1);
  IF p<=h THEN Buffer[p] := CHR(0) END;
  e := p; s := 0;
END RdBuff;

PROCEDURE TerminalWrStr(string: ARRAY OF CHAR);
VAR L : CARDINAL;
BEGIN
  LWW := TRUE;
  L := Length(string);
  FORTH
    /$ addr string addr L @ TYPE $/
  END
END TerminalWrStr;

PROCEDURE RdCharDirect() : CHAR;
BEGIN
  FORTH
    /$ KEY $/
    END
END RdCharDirect;

(*$V+*)

PROCEDURE WrStrAdj( S : ARRAY OF CHAR; Length : INTEGER );
VAR
  L : CARDINAL;
  a : INTEGER;
BEGIN
  OK := TRUE;
  IF RdLnOnWr  THEN RdLn; END;
  L := Str.Length( S );
  a := ABS( Length ) - INTEGER( L );
  IF (a < 0) AND ChopOff THEN
    L := CARDINAL(ABS(Length));
    IF L<=HIGH(S) THEN S[L] := CHR(0); END;
    WHILE (L>0) DO DEC(L,1); S[L] := '?'; END;
    OK := FALSE;
    a  := 0;
  END;

  IF (Length > 0) AND (a > 0) THEN WrCharRep( ' ',a ); END;
  WrStr( S );
  IF (Length < 0) AND (a > 0) THEN WrCharRep( ' ',a ); END;
END WrStrAdj;

(*$V+*)

PROCEDURE WrChar( V: CHAR );
VAR X: ARRAY[1..1] OF CHAR;
BEGIN
  X[1]:=V;
  IF RdLnOnWr THEN RdLn; END;
  WrStr( X );
END WrChar;

PROCEDURE WrCharRep(V: CHAR; count: CARDINAL);
VAR
  s   : ARRAY[0..80] OF CHAR;
  i,j : CARDINAL;
BEGIN
  IF RdLnOnWr THEN RdLn; END;
  WHILE count>0 DO
    i := SIZE(s)-2;
    IF i>count THEN i := count END;
    DEC(count,i);
    j := 0;
    WHILE (j<i) DO s[j] := V; INC(j,1) END;
    s[j] := CHR(0);
    WrStr(s);
  END;
END WrCharRep;

PROCEDURE WrBool(V: BOOLEAN; Length: INTEGER);
BEGIN
  IF V THEN
    WrStrAdj(TrueStr,Length);
  ELSE
    WrStrAdj('FALSE',Length);
  END;
END WrBool;

PROCEDURE WrInt(V: INTEGER; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  IntToStr( V,s,10,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrInt;

(*
PROCEDURE WrShtCard(V: BYTE; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( VAL( CARDINAL,V ),s,10,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrShtCard;
*)

PROCEDURE WrCard(V: CARDINAL; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( V,s,10,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrCard;

(*
PROCEDURE WrShtHex(V: BYTE; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( VAL( CARDINAL,V ),s,16,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrShtHex;
*)

PROCEDURE WrHex(V: CARDINAL; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( V,s,16,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrHex;

(*
PROCEDURE WrReal(V: REAL; Precision: CARDINAL; Length: INTEGER);
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  RealToStr( V,Precision,Eng,s,OK );
  IF OK THEN WrStrAdj( s,Length ); END;
END WrReal;
*)

PROCEDURE WrLn;
TYPE
  a3 = ARRAY [0..1] OF CHAR;
VAR
  crlf : a3;
BEGIN
  IF RdLnOnWr THEN RdLn; END;
  crlf[0] := CHR(13);
  crlf[1] := CHR(10);
  WrStr( crlf );
  LWW := FALSE;
END WrLn;
  
PROCEDURE RdBool() : BOOLEAN;
VAR s : ARRAY[0..80] OF CHAR;
BEGIN
  RdItem( s );
  RETURN Compare( s,TrueStr )=0;
END RdBool;

PROCEDURE RdInt() : INTEGER;
VAR
  s : ARRAY[0..80] OF CHAR;
  i : INTEGER;
BEGIN
  RdItem( s );
  i  := StrToInt( s,10,OK );
  OK := OK AND (i >= -8000H) AND (i <= 7FFFH);
  RETURN INTEGER(i);
END RdInt;

(*
PROCEDURE RdShtCard() : BYTE;
VAR
  s : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( s );
  i  := StrToCard( s,10,OK );
  OK := OK AND (i < 0FFH);
  RETURN BYTE( i );
END RdShtCard;

PROCEDURE RdShtHex() : BYTE;
VAR
  s : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( s );
  i  := StrToCard( s,16,OK );
  OK := OK AND (i < 0FFH);
  RETURN BYTE( i );
END RdShtHex;
*)

PROCEDURE RdCard() : CARDINAL;
VAR
  s : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( s );
  i  := StrToCard( s,10,OK );
  OK := OK AND (i < 10000H);
  RETURN INTEGER( i );
END RdCard;

PROCEDURE RdHex() : CARDINAL;
VAR
  s : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( s );
  i  := StrToCard( s,16,OK );
  OK := OK AND (i < 10000H);
  RETURN INTEGER( i );
END RdHex;

(*
PROCEDURE RdReal() : REAL;
VAR
  s   : ARRAY[0..80] OF CHAR;
  r,a : REAL;
BEGIN
  RdItem( s );
  r := StrToReal( s,OK );
  a := ABS( r );
  OK := OK AND (a >= 1.2E-38 ) AND (a <= 3.4E38 );
  RETURN VAL( REAL,r );
END RdReal;
*)

PROCEDURE RdLn;
BEGIN
  s:=e;
END RdLn;

PROCEDURE EndOfRd(Skip: BOOLEAN) : BOOLEAN;
BEGIN
  IF Skip THEN
     WHILE (s < e) AND (InCharSet(Buffer[s],Separators)) DO INC(s,1) END;
  END;
  RETURN s = e;
END EndOfRd;

PROCEDURE RdItem(VAR V: ARRAY OF CHAR);
VAR L,i : CARDINAL;
BEGIN
  OK := TRUE;
  L := HIGH(V);
  REPEAT
    IF s=e THEN RdBuff; END;

    WHILE (s<e) AND ( InCharSet(Buffer[s],Separators) ) DO INC(s,1); END;
    i := 0;
    WHILE (s<e) AND (i<=L) AND NOT ( InCharSet(Buffer[s],Separators) )  DO
      V[i] := Buffer[s];
      INC(s,1);
      INC(i,1);
    END;
    IF i <= L THEN V[i] := CHR(0); END;
  UNTIL V[0] # CHR(0);
END RdItem;

PROCEDURE RdChar() : CHAR;
VAR
  c : CHAR;
  t : BOOLEAN;
BEGIN
  IF s >= e THEN RdBuff; END;
  INC (s,1);
  RETURN Buffer[s-1];
END RdChar;

PROCEDURE RedirectInput(FileName: ARRAY OF CHAR);
BEGIN
  FORTH
    /$ addr FileName 1 open $/
    /$ IF DUP 0 forcedup    $/
    /$    IF close DROP     $/
    /$    ELSE ( DOSERROR ) $/
    /$    THEN              $/
    /$ ELSE ( DOSERROR )    $/
    /$ THEN                 $/
  END  
END RedirectInput;

PROCEDURE RedirectOutput(FileName: ARRAY OF CHAR);
(* VAR c : CARDINAL;
    r : Registers; *)

BEGIN
  FORTH
    /$ addr FileName 0 make $/
    /$ IF DUP 1 forcedup    $/
    /$    IF close DROP     $/
    /$    ELSE ( DOSERROR ) $/
    /$    THEN              $/
    /$ ELSE ( DOSERROR )    $/
    /$ THEN                 $/
  END  
END RedirectOutput;


BEGIN
  Prompt        := TRUE;
  RdLnOnWr      := FALSE;
  WrStrRedirect := TerminalWrStr;
  RdStrRedirect := TerminalRdStr;
  s             := e;
  OK            := TRUE;
  ChopOff       := FALSE;
  EmptyCharSet(Separators);
  InclChar( CHR(9), Separators );
  InclChar( CHR(10), Separators );
  InclChar( CHR(13), Separators );
  InclChar( CHR(26), Separators );
  InclChar( ' ', Separators );
  Eng           := FALSE;
  LWW           := FALSE;
END IO.
