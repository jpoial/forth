MODULE Strukt11;
FROM IO IMPORT WrCard,WrLn;
TYPE Dim1=ARRAY [1..3] OF CARDINAL;
TYPE Dim2=ARRAY [1..2] OF Dim1;
CONST A=Dim2(Dim1(1,2,3),Dim1(4,5,));
VAR I,J:CARDINAL;
BEGIN
FOR I:=1 TO 2 DO
    FOR J:=1 TO 3 DO
        WrCard(A[I,J],2)
    END; WrLn
END
END Strukt11.