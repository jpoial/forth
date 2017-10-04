(* Copyright (C) 1987 Jensen & Partners International *)

(*$S-,R-,I-*)
IMPLEMENTATION MODULE FIO;

FROM Str    IMPORT CHARSET,Length,Compare,IntToStr,CardToStr,(*RealToStr,*)
                   InCharSet,StrToInt,StrToCard,(*StrToReal,*)Copy,
                   EmptyCharSet,InclChar;
(* FROM SYSTEM IMPORT Seg,Ofs,Registers,CarryFlag; *)

(* IMPORT AsmLib; *)


CONST
  TrueStr   = 'TRUE';
  MaxHandle = MaxOpenFiles+3;

(*$V-*)

TYPE
  FileInf   = POINTER TO BufRec;
VAR
  IOR    : CARDINAL; (* MSDOS result value *)

  BufInf : ARRAY[0..MaxHandle] OF FileInf;
  ErrMsg2,ErrMsg3,ErrMsg4,ErrMsg5,ErrMsg6,
  ErrMsg15,ErrMsg16,ErrMsg17,ErrMsgDiskFull : ARRAY [0..20] OF CHAR;

PROCEDURE ErrorCheckNamed ( str   : ARRAY OF CHAR;
                            name  : ARRAY OF CHAR);
TYPE A079OC = ARRAY[0..79] OF CHAR;
VAR
  s  : ARRAY[0..100] OF CHAR;
  ns : ARRAY[0..3] OF CHAR;
  sp : POINTER TO A079OC;
  
  PROCEDURE AddErr(es: ARRAY OF CHAR);
  BEGIN
    Str.Append(s,es);
  END AddErr;

BEGIN
  IF  IOR # 0  THEN
    IF IOcheck THEN
      s[0] := CHR(0);  
       
      Copy(s,str);
      AddErr(' : ');
      CASE IOR OF
        2 :  FORTH /$ addr ErrMsg2 addr sp ! $/ END |
        3 :  FORTH /$ addr ErrMsg3 addr sp ! $/ END | 
        4 :  FORTH /$ addr ErrMsg4 addr sp ! $/ END | 
        5 :  FORTH /$ addr ErrMsg5 addr sp ! $/ END | 
        6 :  FORTH /$ addr ErrMsg6 addr sp ! $/ END | 
        15 :  FORTH /$ addr ErrMsg15 addr sp ! $/ END | 
        16 :  FORTH /$ addr ErrMsg16 addr sp ! $/ END | 
        17 :  FORTH /$ addr ErrMsg17 addr sp ! $/ END | 
        DiskFull :  FORTH /$ addr ErrMsgDiskFull addr sp ! $/ END | 
        ELSE  AddErr('MSDOS error # ') ;
          ns[0] := CHR(IOR DIV 10+48);
          ns[1] := CHR(IOR MOD 10+48);
          ns[2] := CHR(0);
          FORTH /$ addr ns addr sp ! $/ END ; 
      END;
      AddErr(sp^);
      IF name[0] # CHR(0) THEN
        AddErr(' (');
        AddErr(name);
        AddErr(')');
      END;
      FORTH
	/$ ABORT $/
      END;
    END;
  ELSE
    IOR := 0;
  END;
END ErrorCheckNamed;

PROCEDURE ErrorCheck(str: ARRAY OF CHAR);
BEGIN
  IF IOR # 0  THEN
    ErrorCheckNamed(str,CHR(0));
  ELSE
    IOR := 0;
  END;
END ErrorCheck;

PROCEDURE IOresult () : CARDINAL;
BEGIN
  RETURN IOR;
END IOresult;



PROCEDURE Write(F: File; Buf: ARRAY OF CHAR; Count: CARDINAL);
BEGIN
  IF Count = 0 THEN RETURN END;
  FORTH
    /$ addr Buf addr Count @ addr F @ /W $/
    /$ IF addr Count @ =	              $/
    /$   IF 0                         $/
    /$   ELSE 240                     $/
    /$   THEN                         $/
    /$ THEN addr IOR !                 $/
  END;  
  ErrorCheck('Write');
END Write;

PROCEDURE Truncate(F: File);
BEGIN
  FORTH
    /$ 0 0 addr F @ /W   $/
    /$ DROP addr IOR !   $/
  END;
  ErrorCheck('Truncate');
END Truncate;

PROCEDURE Read(F: File; VAR Buf: ARRAY OF CHAR; Count: CARDINAL) : CARDINAL;
VAR ActCount : CARDINAL;
BEGIN
  FORTH
    /$ addr Buf addr Count @ addr F @ R/   $/
    /$ IF 0                             $/
    /$ ELSE 0 SWAP THEN                 $/
    /$ addr IOR ! addr ActCount !         $/
  END;
  ErrorCheck('Read');
  RETURN ActCount;
END Read;


PROCEDURE WrStr(F: File; Buf: ARRAY OF CHAR);
VAR i,Count : CARDINAL;
BEGIN
  OK := TRUE;
  i  := 0;
  Count := Str.Length( Buf );
  WrBin( F,Buf,Count );
END WrStr;

PROCEDURE WrLn(F: File);
VAR a : ARRAY [ 0..1 ] OF CHAR;
BEGIN
  a[0]:= CHR(13); a[1]:=CHR(10);
  WrStr( F, a );
END WrLn;



PROCEDURE RdChar(F: File ) : CHAR;
VAR c : ARRAY [0..0] OF CHAR;
BEGIN
  OK := TRUE;
  IF (F < MaxHandle) AND (BufInf[F] # NIL) THEN
      IF  BufInf[F]^.RWPos <  BufInf[F]^.EOB THEN
        c :=  BufInf[F]^.Buffer[  BufInf[F]^.RWPos ];
        BufInf[F]^.RWPos:=BufInf[F]^.RWPos+1;
        EOF := (c[0] = CHR(26));
        RETURN c[0];
      END;
  END;
  IF RdBin( F,c,1 ) = 0 THEN
    OK := FALSE;
    c  := CHR(26);
  END;
  EOF := (c[0] = CHR(26));
  RETURN c[0];
END RdChar;

PROCEDURE RdStr(F: File; VAR Buf: ARRAY OF CHAR);
VAR
  i,h : CARDINAL;
  c   : CHAR;
BEGIN
  i  := 0;
  h  := HIGH( Buf );
  OK := TRUE;
  LOOP
     IF i > h THEN RETURN END;
     c := RdChar( F );
     IF c = CHR( 26 ) THEN
       Buf[ i ] := CHR(0);
       EOF := (i = 0);
       RETURN;
     ELSIF c = CHR( 13 ) THEN
       Buf[ i ] := CHR(0);
       RETURN;
     ELSIF c # CHR( 10 ) THEN
       Buf[ i ] := c;
       INC( i, 1 );
     END;
  END;
END RdStr;


PROCEDURE RdItem( F : File; VAR S : ARRAY OF CHAR );
VAR c : CHAR; i,L : CARDINAL;
BEGIN
  i := 0;
  LOOP
    c := RdChar( F );
    IF NOT OK OR NOT InCharSet( c , Separators ) THEN EXIT; END;
  END;
  L := HIGH( S );
  LOOP
    IF NOT OK OR InCharSet( c , Separators ) THEN EXIT; END;
    S[i] := c;
    INC( i,1 );
    IF i > L THEN
      EXIT;
    ELSE
      c := RdChar( F );
      IF c = CHR(26) THEN OK := TRUE; EXIT; END;
    END;
  END;
  IF i <= L THEN S[i] := 0C; END;
END RdItem;


(*$V+*)

PROCEDURE WrStrAdj(F: File; S: ARRAY OF CHAR; Length: INTEGER);
VAR
  L : CARDINAL;
  a : INTEGER;
BEGIN
  OK := TRUE;
  L  := Str.Length( S );
  a  := ABS( Length ) - INTEGER( L );
  IF (a < 0) AND ChopOff THEN
    L := CARDINAL(ABS(Length));
    IF L>HIGH(S) THEN
      L := HIGH(S)+1;
    ELSE
      S[L] := CHR(0);
    END;
    WHILE (L>0) DO DEC(L,1) ; S[L] := '?'; END;
    OK := FALSE;
    a  := 0;
  END;
  IF (Length > 0) AND (a > 0) THEN WrCharRep( F,' ',a ); END;
  WrStr( F,S );
  IF (Length < 0) AND (a > 0) THEN WrCharRep( F,' ',a ); END;
END WrStrAdj;

(*$V-*)

PROCEDURE WrChar(F: File; V: CHAR);
BEGIN
  WrStr( F,V );
END WrChar;

PROCEDURE WrCharRep(F: File; V: CHAR ; Count: CARDINAL);
VAR
  S   : ARRAY[0..80] OF CHAR;
  i,j : CARDINAL;
BEGIN
  WHILE Count>0 DO
    i := SIZE(S)-2;
    IF i > Count THEN i := Count END;
    DEC(Count,i);
    j := 0;
    WHILE (j < i) DO S[j] := V; INC(j,1) END;
    S[j] := CHR(0);
    WrStr(F,S);
  END;
END WrCharRep;

PROCEDURE WrBool(F: File; V: BOOLEAN; Length: INTEGER);
BEGIN
  IF V THEN
    WrStrAdj( F,TrueStr,Length );
  ELSE
    WrStrAdj( F,'FALSE',Length );
  END;
END WrBool;

PROCEDURE WrInt(F: File; V: INTEGER; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  IntToStr( V,S,10,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrInt;

(*
PROCEDURE WrShtCard(F: File; V: BYTE; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( VAL( CARDINAL,V ),S,10,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrShtCard;
*)

PROCEDURE WrCard(F: File; V: CARDINAL; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( V,S,10,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrCard;

(*
PROCEDURE WrShtHex(F: File; V: BYTE; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( VAL( CARDINAL,V ),S,16,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrShtHex;
*)

PROCEDURE WrHex(F: File; V: CARDINAL; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  CardToStr( V,S,16,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrHex;

(*
PROCEDURE WrReal(F: File; V: REAL; Precision: CARDINAL; Length: INTEGER);
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  RealToStr( V,Precision,Eng,S,OK );
  IF OK THEN WrStrAdj( F,S,Length ); END;
END WrReal;
*)

PROCEDURE RdBool(F: File) : BOOLEAN;
VAR S : ARRAY[0..80] OF CHAR;
BEGIN
  RdItem( F,S );
  RETURN Compare(S,TrueStr) = 0;
END RdBool;

PROCEDURE RdInt(F: File) : INTEGER;
VAR
  S : ARRAY[0..80] OF CHAR;
  i : INTEGER;
BEGIN
  RdItem( F,S );
  i  := StrToInt( S,10,OK );
  RETURN INTEGER(i);
END RdInt;

(*
PROCEDURE RdShtCard(F: File) : BYTE;
VAR
  S : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( F,S );
  i  := StrToCard( S,10,OK );
  OK := OK AND (i < 0FFH);
  RETURN BYTE( i );
END RdShtCard;
*)

PROCEDURE RdCard(F: File) : CARDINAL;
VAR
  S : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( F,S );
  i  := StrToCard( S,10,OK );
  RETURN INTEGER( i );
END RdCard;

(*
PROCEDURE RdShtHex(F: File) : BYTE;
VAR
  S : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( F,S );
  i  := StrToCard( S,16,OK );
  OK := OK AND (i < 0FFH);
  RETURN BYTE( i );
END RdShtHex;
*)

PROCEDURE RdHex(F: File) : CARDINAL;
VAR
  S : ARRAY[0..80] OF CHAR;
  i : CARDINAL;
BEGIN
  RdItem( F,S );
  i  := StrToCard( S,16,OK );
  RETURN i;
END RdHex;

(*
PROCEDURE RdReal(F: File): REAL;
VAR
  S   : ARRAY[0..80] OF CHAR;
  r,a : REAL;
BEGIN
  RdItem( F,S );
  r  := StrToReal( S,OK );
  a  := ABS( r );
  RETURN r;
END RdReal;
*)

PROCEDURE WrBin(F: File; Buf: ARRAY OF CHAR; Count: CARDINAL);
VAR i : CARDINAL;
BEGIN
  OK := TRUE;
  i  := 0;
  IF (F > MaxHandle) OR (BufInf[F] = NIL) THEN
    Write( F,Buf,Count );
    OK := (IOR = 0);
  ELSE
      IF  BufInf[F]^.RWPos <=  BufInf[F]^.EOB THEN (* last was read *)
         BufInf[F]^.RWPos := 0;
         BufInf[F]^.EOB   := 0;
      END;
      i := 0;
      WHILE Count > i DO
        WHILE ( BufInf[F]^.RWPos <  BufInf[F]^.BufSize) AND ( Count > i ) DO
           BufInf[F]^.Buffer[  BufInf[F]^.RWPos ] := Buf[i];
          INC( i ,1);
          BufInf[F]^.RWPos := BufInf[F]^.RWPos+1;
        END;
        IF  BufInf[F]^.RWPos =  BufInf[F]^.BufSize THEN
          Write( F, BufInf[F]^.Buffer, BufInf[F]^.BufSize );
           BufInf[F]^.RWPos := 0;
        END;
      END;
  END;
END WrBin;

PROCEDURE Flush(F: File);
VAR x : FileInf;
BEGIN
  IF (F <= MaxHandle) THEN
    x := BufInf[F];
    IF (x # NIL) THEN
        IF x^.RWPos > x^.EOB THEN
          Write( F,x^.Buffer,x^.RWPos );
        END;
        x^.RWPos := 0;
        x^.EOB   := 0;
    END;
  END;
END Flush;



PROCEDURE RdBin(F: File; VAR Buf: ARRAY OF CHAR; Count: CARDINAL) : CARDINAL;
VAR i,h,j : CARDINAL;
BEGIN
  i   := 0;
  OK  := TRUE;
  EOF := FALSE;
  IF Count > 0 THEN
    IF (F > MaxHandle) OR (BufInf[F] = NIL) THEN
      i  := Read( F,Buf,Count );
      OK := (IOR=0);
    ELSE
        IF BufInf[F]^.RWPos > BufInf[F]^.EOB THEN (* Last was write *) Flush( F ); END;
        i := 0;
        LOOP
          IF Count = i THEN EXIT; END;
          IF BufInf[F]^.RWPos >= BufInf[F]^.EOB THEN
            BufInf[F]^.EOB   := Read( F,BufInf[F]^.Buffer,BufInf[F]^.BufSize );
            OK    := (IOR=0);
            BufInf[F]^.RWPos := 0;
            IF BufInf[F]^.EOB=0 THEN EXIT; END;
          END;
          WHILE (BufInf[F]^.RWPos < BufInf[F]^.EOB) AND (Count > i) DO
            Buf[i] := BufInf[F]^.Buffer[ BufInf[F]^.RWPos ];
            INC( i, 1 );
            BufInf[F]^.RWPos := BufInf[F]^.RWPos+1 ;
          END;
      END;
    END;
    IF (i = 0) THEN EOF := TRUE; END;
  END;
  RETURN i;
END RdBin;



PROCEDURE GetName(name: ARRAY OF CHAR; VAR fn: PathStr);
BEGIN
  Copy(fn,name);
  fn[SIZE(fn)-1] := CHR(0);
END GetName;


PROCEDURE Open(Name: ARRAY OF CHAR) : File;
VAR
  fn: PathStr;
  h: CARDINAL;
BEGIN
  GetName(Name,fn);
  FORTH
    /$ addr fn 2 open            $/
    /$ IF 0 addr IOR !           $/
    /$ ELSE DUP 5 =              $/
    /$   IF DROP addr fn 0 open  $/
    /$     IF 0 addr IOR !       $/
    /$     ELSE addr IOR ! -1    $/
    /$     THEN                  $/
    /$   ELSE addr IOR ! -1      $/
    /$   THEN                    $/
    /$ THEN addr h !             $/
  END;  
  ErrorCheckNamed('Open',fn);
  IF IOR = 0 THEN
    IF h <= MaxHandle THEN BufInf[h] := NIL; END;
      RETURN h;
    END ;
  RETURN MAX(CARDINAL);
END Open;

PROCEDURE Exists(Name: ARRAY OF CHAR) : BOOLEAN;
VAR d : DirEntry;
    DTAAddr : CARDINAL;
    b : BOOLEAN ;
BEGIN
  FORTH
    /$ [ HEX ] 2F00 [ DECIMAL ] $AX ! DOSINT            $/
    /$ $BX H@ addr DTAAddr H! $ES H@ addr DTAAddr 2+ H!   $/
  END;
  b := ReadFirstEntry(Name,FileAttr{},d);
  FORTH
    /$ addr DTAAddr DUP H@ $DX H! 2+ H@ $DS H!           $/
    /$ [ HEX ] 1A00 [ DECIMAL ] $AX H! DOSINT DROP      $/
  END;  
  RETURN b;
END Exists;

PROCEDURE Append(Name: ARRAY OF CHAR) : File;
VAR F : CARDINAL;
BEGIN
  F := Open( Name );
  Seek( F,Size( F ) );
  RETURN F;
END Append;

PROCEDURE Create(Name: ARRAY OF CHAR) : File;
VAR
  fn: PathStr;
  h : CARDINAL;
BEGIN
  GetName(Name,fn);
  FORTH
    /$ addr fn 0 make            $/
    /$ IF 0                     $/
    /$ ELSE -1 SWAP             $/
    /$ THEN addr IOR ! addr h !   $/
  END;  
  ErrorCheckNamed('Create',fn);
  IF IOR = 0 THEN
    IF h <= MaxHandle THEN BufInf[h] := NIL; END;
    RETURN h;
  END ;
  RETURN MAX(CARDINAL);
END Create;

PROCEDURE Close(F: File);
BEGIN
  Flush( F );
  BufInf[F] := NIL;
  FORTH
    /$ addr F @ close    $/
    /$ IF 0 THEN        $/
    /$ addr IOR !        $/
  END;  
  ErrorCheck('Close');
END Close;

PROCEDURE GetPos(F: File) : CARDINAL;
VAR
  x    : FileInf;
  conv : CARDINAL;
BEGIN
  FORTH
    /$ 0 1 addr F @ seek $/
    /$ IF addr conv ! 0  $/
    /$ THEN             $/
    /$ addr IOR !        $/
  END;  
  ErrorCheck('GetPos');
  IF (F <= MaxHandle) THEN
    x := BufInf[F];
    IF (x # NIL) THEN
        IF x^.RWPos > x^.EOB THEN
          conv := conv+x^.RWPos;
        ELSIF x^.RWPos < x^.EOB THEN
          conv := conv - (x^.EOB-x^.RWPos);
        END;
    END;
  END;
  RETURN conv;
END GetPos;

PROCEDURE Seek( F : File; pos : CARDINAL );
BEGIN
  Flush( F );
  FORTH
    /$ addr pos @ 0 addr F @ seek $/
    /$ IF DROP 0                $/
    /$ THEN addr IOR !           $/
  END;  
  ErrorCheck('Seek');
END Seek;

PROCEDURE Size(F: File) : CARDINAL;
VAR
  conv : CARDINAL ;
BEGIN
  Flush( F );
  FORTH
    /$ 0 1 addr F @ seek         $/
    /$ IF 0 2 addr F @ seek      $/
    /$   IF addr conv !          $/
    /$     0 addr F @ seek       $/
    /$     IF DROP 0            $/
    /$     THEN                 $/
    /$   THEN                   $/
    /$ THEN addr IOR !           $/
  END;   
  ErrorCheck('Size');
  RETURN conv;
END Size;


PROCEDURE Erase(Name:ARRAY OF CHAR);
VAR
  fn : PathStr;
BEGIN
  GetName(Name,fn);
  FORTH
    /$ addr fn delete    $/
    /$ IF 0             $/
    /$ THEN addr IOR !   $/
  END;
  IF IOR = 2 THEN
    IOR := 0;
  END;
  ErrorCheckNamed('Erase',fn);
END Erase;


PROCEDURE Rename(Name,newname: ARRAY OF CHAR);
VAR
  fn,fn2: PathStr;
BEGIN
  GetName(Name,fn);
  GetName(newname,fn2);
  FORTH
    /$ addr fn addr fn2 rename    $/
    /$ IF 0                     $/
    /$ THEN addr IOR !           $/
  END;
  ErrorCheckNamed('Rename',fn);
END Rename;


PROCEDURE ReadFirstEntry ( DirName : ARRAY OF CHAR;
                           Attr    : FileAttr;
                           VAR D   : DirEntry) : BOOLEAN;
VAR
  fn : PathStr;
BEGIN
  GetName(DirName,fn);
  FORTH
    /$ addr fn addr Attr @ find           $/
    /$ IF 0 THEN addr IOR !              $/
    /$ SCRATCH_BUFF addr D 44 CMOVE      $/
  END;
  IF IOR = 18 THEN
    IOR := 0;
    RETURN FALSE;
  END;
  ErrorCheckNamed('ReadFirstEntry',fn);
  RETURN TRUE;
END ReadFirstEntry;

PROCEDURE ReadNextEntry(VAR D: DirEntry) : BOOLEAN;
BEGIN
  FORTH
    /$ addr D SCRATCH_BUFF 44 CMOVE       $/
    /$ next                              $/
    /$ IF 0 THEN addr IOR !               $/
    /$ SCRATCH_BUFF addr D 44 CMOVE       $/
  END;
  IF IOR = 18 THEN
    IOR := 0;
    RETURN FALSE;
  END;
  ErrorCheck('ReadNextEntry');
  RETURN TRUE;
END ReadNextEntry;


PROCEDURE ChDir(Name: ARRAY OF CHAR);
VAR
  fn : PathStr;
  D : CHAR;
BEGIN
  GetName(Name,fn);
  IF fn[1] = ':' THEN
    D := CAP(fn[0]);
    FORTH
      /$ 14 addr D C@ ASCII A - FDOS $/
      /$ 2DROP                      $/
    END;
  END;
  FORTH
    /$ addr fn chdir         $/
    /$ IF 0 THEN addr IOR !  $/
  END;
  ErrorCheckNamed('ChDir',fn);
END ChDir;

PROCEDURE MkDir(Name: ARRAY OF CHAR);
VAR
  fn : PathStr;
BEGIN
  GetName(Name,fn);
  FORTH
    /$ addr fn mkdir        $/
    /$ IF 0 THEN addr IOR ! $/
  END;
  ErrorCheckNamed('MkDir',fn);
END MkDir;

PROCEDURE RmDir(Name: ARRAY OF CHAR);
VAR
  fn : PathStr;
BEGIN
  GetName(Name,fn);
  FORTH
    /$ addr fn rmdir        $/
    /$ IF 0 THEN addr IOR ! $/
  END;
  ErrorCheckNamed('RmDir',fn);
END RmDir;

PROCEDURE GetDir(drive: CARDINAL; VAR Name: ARRAY OF CHAR);
VAR
  fn : PathStr;
BEGIN
  FORTH
    /$ addr drive C@ getdir $/
    /$ IF 0 THEN addr IOR ! $/
  END;
  ErrorCheck('GetDir');
  Copy(Name,fn);
END GetDir;


PROCEDURE InitBufInf;
VAR i : CARDINAL;
BEGIN
  FOR i := 0 TO MaxHandle DO BufInf[i] := NIL; END;
END InitBufInf;

PROCEDURE AssignBuffer(F: File; VAR Buf: ARRAY OF CHAR);
VAR FP : FileInf;
BEGIN
  IF (F <= MaxHandle) AND ( HIGH(Buf) > SIZE(BufRec) ) THEN
    FORTH /$ addr Buf addr FP ! $/ END ; 
    BufInf[F] := FP;
      BufInf[F]^.RWPos   := 0;
      BufInf[F]^.EOB     := 0;
      BufInf[F]^.BufSize := HIGH(Buf)-SIZE(BufRec)+2;
  END;
END AssignBuffer;


BEGIN
  Eng     := FALSE;
  IOcheck := TRUE;
  OK      := TRUE;
  ChopOff := FALSE;
  EmptyCharSet(Separators);
  InclChar( CHR(9), Separators );
  InclChar( CHR(10), Separators );
  InclChar( CHR(13), Separators );
  InclChar( CHR(26), Separators );
  InclChar( ' ', Separators );
  InitBufInf;
  ErrMsg2  := 'file not found';
  ErrMsg3  := 'path not found';
  ErrMsg4  := 'too many open files';
  ErrMsg5  := 'access denied';
  ErrMsg6  := 'invalid handle';
  ErrMsg15 := 'invalid drive';
  ErrMsg16 := 'current directory';
  ErrMsg17 := 'different device';
  ErrMsgDiskFull := 'disk full';
END FIO.

