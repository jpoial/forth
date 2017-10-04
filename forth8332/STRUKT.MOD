MODULE Strukt;
TYPE Dim2=ARRAY [1..2] OF ARRAY [1..3] OF CARDINAL;
VAR A:Dim2;
BEGIN
A:=Dim2((1,2,3),(4,5,6),(7,8,9));
END Strukt.