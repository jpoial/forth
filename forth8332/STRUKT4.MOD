MODULE Strukt4;
FROM IO IMPORT RdCard,WrStr,WrCard,WrLn;
TYPE Dim1=ARRAY [1..3] OF CARDINAL;
TYPE Dim2=ARRAY [1..2] OF Dim1;
VAR A:Dim2;
VAR I,J,X:CARDINAL;
BEGIN
WrStr("X=");
X:=CARDINAL(RdCard);
A:=Dim2(Dim1(1,X+2,3),Dim1(4,5,6));
FOR I:=1 TO 2 DO
    FOR J:=1 TO 3 DO
        WrCard(A[I,J],2)
    END; WrLn
END
END Strukt4.