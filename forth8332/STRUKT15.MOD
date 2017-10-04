MODULE STRUKT15;
TYPE Dim=ARRAY [1..3] OF CARDINAL;
VAR A:Dim;
VAR I,X:CARDINAL;
BEGIN A:=Dim(1,2,3);
      FOR I:=1 TO 3 DO
          X:=A[I];
	  FORTH /$ addr X @ . $/ END
      END
END STRUKT15.