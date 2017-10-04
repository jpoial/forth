IMPLEMENTATION MODULE KKK;
PROCEDURE PPP;
VAR A:INTEGER;
BEGIN
    A := 1990;
    FORTH /$ ." Veel yks tekst." CR addr A @ . CR $/ END;
END PPP;
BEGIN
    FORTH /$ CR ." Initializing KKK" CR $/ END;
END KKK.

