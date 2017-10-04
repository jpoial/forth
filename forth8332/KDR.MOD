IMPLEMENTATION MODULE KDR;

VAR KIRJELDUS: ARRAY[1..256] OF CHAR;

BEGIN 
   KIRJELDUS := 'KDR';
   FORTH
      /$ ['] Inimene EXECUTE 12 + @ KIRJETYYP !      $/
      /$ 2 #KOMPLEKT !                               $/
      /$ ['] KEY1 EXECUTE 12 + @ KEY.ARRAY @ !       $/
      /$ ['] KEY2 EXECUTE 12 + @ KEY.ARRAY @ 4 + !   $/
      /$ addr KIRJELDUS DEFNAME !                    $/
   END
END KDR.
