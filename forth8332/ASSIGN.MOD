MODULE ASSIGN;
TYPE MASS=ARRAY[1..3] OF CARDINAL;
VAR A:MASS;
   
PROCEDURE PRINT(C:ARRAY OF CARDINAL);
VAR B:MASS;
 X:CARDINAL;
BEGIN
   B:=C;
   X:=B[1];
   FORTH /$ addr X @ . CR $/ END;
   X:=B[2];
   FORTH /$ addr X @ . CR $/ END;
   X:=B[3];
   FORTH /$ addr X @ . CR $/ END;
END PRINT;

BEGIN
   A[1]:=1;
   A[2]:=2;
   A[3]:=3;
END ASSIGN.