MODULE T22;
   VAR A:INTEGER;
       X:CARDINAL;
BEGIN
   A:=3;
   X:=CARDINAL(A);
   FORTH /$ addr A @ . addr X @ . $/ END;
END T22.

