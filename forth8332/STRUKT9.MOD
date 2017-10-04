MODULE STRUKT9;
FROM IO IMPORT WrCard,WrStr,WrBool,WrLn;
TYPE Rec1=RECORD
               E:CARDINAL;
               F:CARDINAL;
             END;
TYPE Rec=RECORD
           A:CARDINAL;
           B:BOOLEAN;
           C:CHAR;
           D:Rec1;
         END;
VAR Y:CARDINAL;
VAR X:Rec;
VAR S:ARRAY [0..3] OF CHAR;
BEGIN
  Y:=32;
  X:=Rec(3,TRUE,'N',Rec1(Y,21));
  WrCard(X.A,4);  WrBool(X.B,8);
  S:='   ';       S[3]:=X.C;
  WrStr(S);       WrLn;
  WrCard(X.D.E,3);WrCard(X.D.F,3)
END STRUKT9.