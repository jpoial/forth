MODULE FFF;
(* FROM KKK IMPORT PPP; *)
FROM III IMPORT A,RTYYP,RVAR;
FROM JJJ IMPORT B; 
VAR C: INTEGER;
BEGIN
    C:= B-A+4;
    FORTH /$ CR addr C @ . CR $/ END;
    C:= RVAR.V1;
    FORTH /$ CR addr C @ . CR $/ END;
    (* PPP; *)
END FFF.
