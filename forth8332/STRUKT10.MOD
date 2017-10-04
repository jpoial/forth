MODULE Strukt10;
FROM IO IMPORT WrCard,WrBool,WrStr;
TYPE Dim1=ARRAY [1..3] OF CARDINAL;
TYPE Dim2=ARRAY [1..2] OF Dim1;
VAR A:Dim2;
VAR I,J:CARDINAL;
TYPE Rec=RECORD
           A:CARDINAL;
           B:BOOLEAN;
           C:CHAR;
         END;
VAR X:Rec;
VAR S:ARRAY [0..3] OF CHAR;
BEGIN
X:=Rec(Dim2(Dim1(1,2,3),Dim1(4,5,6)));
  WrCard(X.A,4);
  WrBool(X.B,8);
  S:='   ';
  S[3]:=X.C;
  WrStr(S)
END Strukt10.