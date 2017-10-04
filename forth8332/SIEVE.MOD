MODULE SIEVE;
VAR I,J,K,L,N: INTEGER;
FLAGS:ARRAY [0..90] OF INTEGER;
   BEGIN 
      FOR I:=0 TO 90 DO FLAGS[I]:=1 END; 
          N:=0;
          FOR I:=0 TO 90
	  DO IF FLAGS[I]=1
	     THEN K:=2*I+3; L:=K+I;
	         WHILE L<=90
	         DO FLAGS[L]:=0; L:=L+K 
                 END; N:=N+1
             END
          END; 
    END SIEVE .
