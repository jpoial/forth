MODULE Strukt20;

TYPE Dim1=ARRAY [1..3] OF CARDINAL;
TYPE Dim2=ARRAY [1..2] OF Dim1;
VAR X,I,J:CARDINAL;A:Dim2;
BEGIN
  A:=Dim2(Dim1(1,2+4,3),Dim1(4,5,6));
FOR I:=1 TO 2 DO
    FOR J:=1 TO 3 DO
        X:=A[I,J];
        FORTH /$ addr X @ . $/ END
    END; FORTH /$ CR $/ END;                        
END
END Strukt20.