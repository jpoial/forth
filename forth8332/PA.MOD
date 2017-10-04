
IMPLEMENTATION MODULE PA;
VAR KIRJELDUS: ARRAY [1..8] OF CHAR;

BEGIN
KIRJELDUS := 'PA';
FORTH
/$ ['] KLIENT EXECUTE 12 + @ KIRJETYYP !    $/
/$ 2 #KOMPLEKT !                            $/
/$ ['] PartneriNrJargi KEY.ARRAY @ !        $/
/$ ['] PartArveNrJargi KEY.ARRAY @  4 + !   $/
/$ 0 #VABA !                                $/
/$ addr KIRJELDUS DEFNAME !                 $/
END

END PA.
