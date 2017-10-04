MODULE ASSIGN1;
TYPE MASS=ARRAY[1..3] OF CARDINAL;
     KIRI=RECORD
             L:CARDINAL;
             M:CARDINAL;
             N:CARDINAL;
          END;
VAR A:MASS;
   
PROCEDURE PRINT(B:ARRAY OF WORD);
VAR  X:WORD;
BEGIN
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
   PRINT(KIRI(A)) 
END ASSIGN1.