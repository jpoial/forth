MODULE TIMES10;
FROM IO IMPORT WrStr,WrCard;
VAR mitu,i : CARDINAL;
PROCEDURE SIEVE(VAR res:CARDINAL) ;
   VAR I,J,K,L,N: INTEGER;
   FLAGS:ARRAY [0..8190] OF INTEGER;
   BEGIN
      FOR I:=0 TO 8190 DO FLAGS[I]:=1 END;
          N:=0;
          FOR I:=0 TO 8190
	  DO IF FLAGS[I]=1
	     THEN K:=2*I+3; L:=K+I;
	         WHILE L<=8190
	         DO FLAGS[L]:=0; L:=L+K
                 END; N:=N+1
          END
       END; res:=N
    END SIEVE ;
BEGIN
   FOR i:=1 TO 10
   DO SIEVE(mitu);WrStr("n=");WrCard(mitu,5)
   END;
END TIMES10 .