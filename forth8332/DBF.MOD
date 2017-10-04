IMPLEMENTATION MODULE DBF;

TYPE A0790C = ARRAY[0..79] OF CHAR;

VAR
s : ARRAY[0..100] OF CHAR;
ns: ARRAY[0..3] OF CHAR;
sp: POINTER TO A0790C;
tf: BOOLEAN;
LEGNAME: PathTail;

PROCEDURE InclChar( s: CHAR; VAR cset: CHARSET);
VAR SetPart : BITSET ;
BEGIN
  SetPart := cset[ORD(s) DIV MaxSet];
  FORTH
    /$ addr SetPart DUP @               $/
    /$ 1 addr s C@ 31 AND <-L OR SWAP ! $/
  END;  
(*  INCL( SetPart , ORD(s) MOD MaxSet ); *)
  cset[ORD(s) DIV MaxSet] := SetPart
END InclChar;
PROCEDURE EmptyCharSet( VAR cset : CHARSET );
VAR i : CARDINAL;
BEGIN
  FOR i:=0 TO CSWords DO
    cset[i] := BITSET{}
  END
END EmptyCharSet;
PROCEDURE Compare(S1,S2: ARRAY OF CHAR) : INTEGER;
VAR
  L1,L2,L,Index : CARDINAL;
BEGIN
  L1 := Length(S1);
  L2 := Length(S2);
  IF L1<L2 THEN L := L1 ELSE L := L2 END;
  FORTH
    /$ addr  S1 addr  S2 addr  L @ COMPS $/
    /$ addr  Index !                     $/
  END;  
(*  Index := Lib.Compare(ADR(S1),ADR(S2),L); *)
  IF (Index<L) THEN
    IF S1[Index] < S2[Index] THEN
      RETURN -1
    ELSE
      RETURN 1;
    END;
  ELSIF (L1=L2) THEN
    RETURN 0
  ELSIF (L1<L2) THEN
    RETURN -1
  ELSE
    RETURN 1;
  END;
END Compare;
PROCEDURE Length(S1: ARRAY OF CHAR) : CARDINAL;
VAR I : CARDINAL;
BEGIN
  I := HIGH(S1);
  FORTH
    /$ addr  S1 addr  I @ 1+ 0 SCANS      $/
  END  
(*  RETURN Lib.ScanR(ADR(S1),HIGH(S1)+1,0);  *)
END Length;
PROCEDURE Copy(VAR Ns: ARRAY OF CHAR; S: ARRAY OF CHAR);
VAR
  H,L : CARDINAL;
BEGIN
  H := HIGH(Ns)+1;
  L := Length(S);
  IF L > H THEN L := H END;
  FORTH
    /$ addr  S addr  Ns addr  L @ CMOVE $/
  END;
(*  Lib.Move(ADR(S),ADR(Ns),L);  *)
  IF L < H THEN Ns[L] := CHR(0) END;
END Copy;
PROCEDURE GetName(name: ARRAY OF CHAR; VAR fn: PathStr);
BEGIN Copy(fn,name);
fn[SIZE(fn)-1] := CHR(0);
END GetName;

PROCEDURE InitDBFs;
BEGIN 
FORTH
/$ INIT-DBFs  $/
END;
END InitDBFs;

PROCEDURE OpenDBF(Legend: PathTail;
                  FileName  : PathStr;
                  VAR FILE : WORD) : BOOLEAN;
VAR 
fan: PathStr;
t:   BOOLEAN;
FanLength: CARDINAL;
BEGIN
GetName(FileName,fan);
FanLength := Length(fan);
LEGNAME := Legend;
FORTH
/$ SET-PARA                  $/
/$ addr LEGNAME DEFNAME !    $/
/$ addr fan addr FanLength @ $/
/$ OpenDBFile                $/
/$ IF 1 ELSE 0 THEN          $/
/$ addr t !                  $/
/$ F+P @ addr FILE !         $/
/$ 1 ReWri !                 $/
END;
RETURN t;
END OpenDBF; 

PROCEDURE OpenByName(Legend : PathTail;
                     VAR FILE : WORD) : BOOLEAN;
VAR 
t:   BOOLEAN;
Leg: PathTail;
LegLength: CARDINAL;
BEGIN
Copy(Leg,Legend);
LegLength := Length(Leg);
FORTH
/$ SET-PARA                          $/
/$ CR ." Faili kirjeldus on "        $/
/$ addr Leg addr LegLength @ TYPE    $/
/$ addr Leg DEFNAME !                $/
/$ OpenBY-NAME                       $/
/$ IF 1 ELSE 0 THEN                  $/
/$ addr t !                          $/
/$ F+P @ addr FILE !                 $/
/$ 1 ReWri !                         $/
END;
RETURN t;
END OpenByName; 

PROCEDURE OpenDBFro(Legend: PathTail;
                    FileName  : PathStr;
                  VAR FILE : WORD) : BOOLEAN;
VAR 
fn: PathStr;
h:  BOOLEAN;
FnLength: CARDINAL;
BEGIN
GetName(FileName,fn);
FnLength := Length(fn);
LEGNAME := Legend;
FORTH
/$ SET-PARA                  $/
/$ addr LEGNAME DEFNAME !    $/
/$ addr fn addr FnLength @   $/
/$ OpenDBFile                $/
/$ IF 1 ELSE 0 THEN          $/
/$ addr h !                  $/
/$ F+P @ addr FILE !         $/
/$ 0 ReWri !                 $/
END;
RETURN h;
END OpenDBFro; 

PROCEDURE OpenByNameRO(Legend : PathTail;
                       VAR FILE : WORD) : BOOLEAN;
VAR 
t:   BOOLEAN;
Leg: PathTail;
LegLength: CARDINAL;
BEGIN
Copy(Leg,Legend);
LegLength := Length(Leg);
FORTH
/$ SET-PARA                          $/
/$ addr Leg DEFNAME !                $/
/$ CR ." Faili kirjeldus on "        $/
/$ addr Leg addr LegLength @ TYPE    $/
/$ OpenBY-NAME                       $/
/$ IF 1 ELSE 0 THEN                  $/
/$ addr t !                          $/
/$ F+P @ addr FILE !                 $/
/$ 0 ReWri !                         $/
END;
RETURN t;
END OpenByNameRO; 

PROCEDURE GetByKey( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !                            $/
/$ SET-IXP                                      $/
/$ addr Rec REC->BUF                            $/
/$ key-GET 0= IF 1 ELSE 0 THEN addr tf !        $/
/$ addr Rec BUF->REC                            $/
END;
RETURN tf;
END GetByKey;

PROCEDURE GetByIndex( VAR FILE : WORD;
                      VAR Rec: ARRAY OF WORD;I: CARDINAL) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P ! SET-IXP  $/
/$ addr I @ GET_RECORD        $/
/$ 0= IF 1 ELSE 0 THEN        $/
/$ addr tf !                  $/
/$ addr Rec BUF->REC          $/
END;
RETURN tf;
END GetByIndex;

PROCEDURE GetFirst( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P ! SET-IXP  $/
/$ F-rECORD                   $/
/$ 0= IF 1 ELSE 0 THEN        $/
/$ addr tf !                  $/
/$ addr Rec BUF->REC          $/
END;
RETURN tf;
END GetFirst;

PROCEDURE GetLast( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !          $/
/$ SET-IXP L-rECORD           $/
/$ 0= IF 1 ELSE 0 THEN        $/
/$ addr tf !                  $/
/$ addr Rec BUF->REC          $/
END;
RETURN tf;
END GetLast;

PROCEDURE GetPrev( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !        $/
/$ SET-IXP P-rECORD         $/
/$ 0= IF 1 ELSE 0 THEN      $/
/$ addr tf !                $/
/$ addr Rec BUF->REC        $/
END;
RETURN tf;
END GetPrev;

PROCEDURE GetNext( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !        $/
/$ SET-IXP N-rECORD         $/
/$ 0= IF 1 ELSE 0 THEN      $/
/$ addr tf !                $/
/$ addr Rec BUF->REC        $/
END;
RETURN tf;
END GetNext;

PROCEDURE PutRecord( VAR FILE : WORD;VAR Rec: ARRAY OF WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !       $/
/$ ReWri @ 1 =             $/
/$ IF                      $/
/$ addr Rec REC->BUF       $/
/$ SET-IXP WRITE-I-REC     $/
/$ 0= IF 1 ELSE 0 THEN     $/
/$ ELSE 0                  $/
/$ THEN                    $/
/$ addr tf !               $/
END;
RETURN tf;
END PutRecord;

PROCEDURE CloseDBF( VAR FILE : WORD) : BOOLEAN;
BEGIN
FORTH
/$ addr FILE @ F+P !        $/
/$ CLOSE_DBF                $/
/$ 0= IF 1 ELSE 0 THEN      $/
/$ addr tf !                $/
END;
RETURN tf;
END CloseDBF;

PROCEDURE SetKeySequence( VAR FILE : WORD; KeyIndex : CARDINAL );
BEGIN
FORTH
/$ addr FILE @ F+P !                   $/
/$ ReWri @ 0= IF CLOSE-INX THEN        $/
/$ addr KeyIndex @ ?KEYKOMPLEKT DROP   $/
/$ ReWri @ 0= IF OPEN-INX  THEN        $/
END;
END SetKeySequence;

PROCEDURE MoveRecord( VAR R1,R2 : ARRAY OF WORD );
BEGIN
FORTH
/$ addr R1 addr R2 PURELENGTH @ CMOVE  $/
END;
END MoveRecord;

PROCEDURE ClearRecord( VAR R : ARRAY OF WORD );
BEGIN
FORTH
/$ addr R PURELENGTH @ ERASE  $/
END;
END ClearRecord;

PROCEDURE MBase;
BEGIN
FORTH
/$ D2Base $/
END;
END MBase;

END DBF.