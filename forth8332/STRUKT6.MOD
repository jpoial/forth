MODULE STRUKT6;

TYPE Rec=RECORD
           A:CARDINAL;
           B:BOOLEAN;
           C:CHAR;
         END;
VAR X:Rec;
VAR Y:CARDINAL;Z:BOOLEAN;W:CHAR;
VAR S:ARRAY [0..3] OF CHAR;
BEGIN
  X:=Rec(3,TRUE,'N');
  Y:=X.A;Z:=X.B;W:=X.C;
  FORTH /$ addr Y @ . addr Z @ . $/
        /$ addr W 1 TYPE $/ END;
END STRUKT6.