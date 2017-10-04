MODULE MASSIIV;
TYPE Dim=ARRAY [1..3] OF CARDINAL;
VAR A:Dim;
    I,X:CARDINAL;
BEGIN
    A[1]:=4;
    X:=A[1];
    FORTH /$ addr X @ . $/ END
END MASSIIV. 