MODULE STRUKT7;
FROM IO IMPORT WrCard,WrStr,WrBool,WrLn;
TYPE Rec=RECORD
           A:CARDINAL;
           B:BOOLEAN;
           C:CHAR;
           D:RECORD
               E:CARDINAL;
               F:CARDINAL;
             END;
         END;
VAR X:Rec;
VAR S:ARRAY [0..3] OF CHAR;
BEGIN
  X:=Rec(3,TRUE,'N',(13,21));
  WrCard(X.A,4);
  WrBool(X.B,8);
  S:='   ';
  S[3]:=X.C;
  WrStr(S);
  WrLn;
  WrCard(X.D.F,3);WrCard(X.D.F,3)
END STRUKT7.