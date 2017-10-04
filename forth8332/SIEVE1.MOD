MODULE SIEVE1;
VAR I,L,N: INTEGER;
FLAGS:ARRAY [0..90] OF INTEGER;
   BEGIN 
      FOR I:=0 TO 90 DO FLAGS[I]:=1 END; 
          N:=0;
          FOR I:=2 TO 90
	  DO IF FLAGS[I]=1
	     THEN L:=I+I;
	         WHILE L<=90
	         DO FLAGS[L]:=0; L:=L+I 
                 END; N:=N+1
             END
          END; 
    END SIEVE1 .
