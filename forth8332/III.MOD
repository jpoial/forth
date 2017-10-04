IMPLEMENTATION MODULE III;
BEGIN
    FORTH /$ CR ." Initialize III" CR $/ END;
    WITH RVAR DO
        V1 := 13 ;
        TAG := TRUE;
        CASE TAG OF
            TRUE : V3 := 30 ;
        END;
    END;
    FORTH /$ CR addr RVAR DUP HEX . 40 DUMP DECIMAL CR $/ END;
END III.
