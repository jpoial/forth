MODULE ARROFW2;
TYPE RR=RECORD
        A:CARDINAL;
        B:ARRAY [1..3] OF CARDINAL;
        END;
VAR X:RR;
PROCEDURE PRINT(P:ARRAY OF WORD);
   VAR U:CARDINAL;
   BEGIN
      U:=P[1];
      FORTH /$ addr U @ . CR $/ END;
      U:=P[2];
      FORTH /$ addr U @ . CR $/ END;
   END PRINT;     
   BEGIN
      X.A:=25;
      X.B[1]:=1;
      X.B[2]:=2;
      X.B[3]:=3;
      PRINT(X);
   END ARROFW2.
	
