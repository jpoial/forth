
IMPLEMENTATION MODULE APR;
VAR T1: TEXT;
    T2: TEXT;
    KIRJELDUS: TEXT;

BEGIN
T1 := 'Ohvitseride korpuse isikuandmed';
T2 := 'Komand”r:';
KIRJELDUS := 'APR';
FORTH
/$ ['] File EXECUTE 12 + @ KIRJETYYP !       $/
/$ 1 #KOMPLEKT !                             $/
/$ ['] KEY1 KEY.ARRAY @ !                    $/
/$ 2 #VABA !                                 $/
/$ addr T1 TEXT.ARRAY @ !                    $/
/$ addr T2 TEXT.ARRAY @ 4 + !                $/
/$ addr KIRJELDUS DEFNAME !                  $/
END

END APR .
