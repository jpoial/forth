MODULE PR1;

TYPE
  WrStrType   = PROCEDURE ( ARRAY OF CARDINAL );
  RdStrType   = PROCEDURE ( VAR ARRAY OF CHAR );
  Dim         = ARRAY [1..5] OF CARDINAL;
VAR WrStrRedirect : WrStrType;
VAR RdStrRedirect : RdStrType;

PROCEDURE WrStr(s: ARRAY OF CARDINAL);
VAR I,X:CARDINAL;
BEGIN
  FOR I:=0 TO HIGH(s) DO 
      X:=s[I];
      FORTH /$ addr X @ . $/ END
  END
END WrStr;

BEGIN
WrStrRedirect:=WrStr;
WrStrRedirect(Dim(1,2,3,4,5))
END PR1.