
IMPLEMENTATION MODULE KUNDE;
VAR KIRJELDUS: ARRAY[1..10] OF CHAR;

BEGIN
KIRJELDUS := 'KUNDE';
FORTH
/$ ['] KLIENT EXECUTE 12 + @ KIRJETYYP !         $/
/$ 1 #KOMPLEKT !                                 $/
/$ ['] KEY1TYYP EXECUTE 12 + @ KEY.ARRAY @ !     $/
/$ 0 #VABA !                                     $/
/$ addr KIRJELDUS DEFNAME !                      $/
END

END KUNDE .
