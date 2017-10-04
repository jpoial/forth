IMPLEMENTATION MODULE MKOR;
  PROCEDURE INITS;
  VAR T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T10A,
      T11,T12,T13,T14,T15,T16,T17,T18,T19,T20,
      T21,T22,T23,T24,T25,T25A,T26,T27,T28,T29,T30,
      T31,T32,T33,T34,T35,T36,T37,T38,T39,T40,
      T41,T42,T43,T44,T45,T46,T47,T48,T49,T50,
      T51,T52: ARRAY [1..80] OF CHAR;
      KIRJELDUS: ARRAY [1..32] OF CHAR;
  BEGIN
T1 :=  'зддддддддддд©';
T2 :=  'Maksekorraldus Nr.Ё';
T3 :=  'Ё      0401002';
T4 :=  'юддддддддддды';
T5 :=  '.';
T6 :=  '.a.';
T7 :=  '    Maksja';
T8 :=  'DEEBET      Summa';
T9 :=  '   здддддддддддд©                                      здддддддддддбдддддддддд©';
T10 := '   ЁKood';
T10A := 'Ё';
T11 := 'Ё';
T12 := 'Ё          Ё';
T13 := '   юддддддддддддаддддддддддддддддддддддддддбдддддддддддеддддддддддд╢          Ё';
T14 := 'Ё';
T15 := 'Ё';
T16 := 'Ё';
T17 := '.';
T18 := 'Ё';
T19 := 'Ё           Ё           Ё          Ё';
T20 := '    Maksja pank                   Linn     Ё Kood      ЁArve Nr.   Ё          Ё';
T21 := '   ддддддддддддддддддддддддддддддддддддддддадддддддддддадддддддддддадддддддддды';
T22 := '    Saaja';
T23 := 'KREEDIT';
T24 := '   здддддддддддд©                                      здддддддддддбдддддддддд©';
T25 := '   ЁKood';
T25A := 'Ё';
T26 := 'Ё';
T27 := 'Ё          Ё';
T28 := '   юддддддддддддаддддддддддддддддддддддддддбдддддддддддедддддддддддедддддддддд╢';
T29 := 'Ё';
T30 := 'Ё';
T31 := 'Ё          Ё';
T32 := 'Ё           Ё           Ё          Ё';
T33 := '    Saaja pank                    Linn     Ё Kood      ЁArve Nr.   Ё          Ё';
T34 := '   ддддддддддддддддддддддддддддддддддддддддадддддддддддадддддддддддедддддддддд╢';
T35 := 'Postiga - telegraafiga                      ЁViivis    Ё';
T36 := 'цдддддддддд╢';
T37 := 'ЁKokku     Ё';
T38 := '    Summa sonadega                                                 Ё          Ё';
T39 := '   ддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддеддддбддддд╢';
T40 := '    Kauba/teenuse saamise kuupaev                                  ЁOperЁ     Ё';
T41 := '   ддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддддеддддеддддд╢';
T42 := '    Makse eesmark                                                  Ё    Ё     Ё';
T43 := 'цддддеддддд╢';
T44 := 'Ё    Ё     Ё';
T45 := 'цддддеддддд╢';
T46 := 'Ё    Ё     Ё';
T47 := 'цддддеддддд╢';
T48 := 'Ё    Ё     Ё';
T49 := 'юддддаддддды';
T50 := '   здддддддддд©                                      Ё';
T51 := '   Ё   P.K.   Ё            Kliendi allkirjad         Ё    Panga allkirjad';
T52 := '   юдддддддддды                                      Ё';
    KIRJELDUS := 'MKOR';
    FORTH
      /$ ['] MKORTYYP EXECUTE 12 + @ KIRJETYYP !      $/
      /$ addr KIRJELDUS DEFNAME !                     $/
      /$ 7 #KOMPLEKT ! $/
      /$ ['] KEY1TYYP EXECUTE 12 + @ KEY.ARRAY @ !      $/
      /$ ['] KEY2TYYP EXECUTE 12 + @ KEY.ARRAY @  4 + ! $/
      /$ ['] KEY3TYYP EXECUTE 12 + @ KEY.ARRAY @  8 + ! $/
      /$ ['] KEY4TYYP EXECUTE 12 + @ KEY.ARRAY @ 12 + ! $/
      /$ ['] KEY5TYYP EXECUTE 12 + @ KEY.ARRAY @ 16 + ! $/
      /$ ['] KEY6TYYP EXECUTE 12 + @ KEY.ARRAY @ 20 + ! $/
      /$ ['] KEY7TYYP EXECUTE 12 + @ KEY.ARRAY @ 24 + ! $/
      /$ 54 #VABA !  $/
      /$ addr T1  TEXT.ARRAY @ !  $/
      /$ addr T2  TEXT.ARRAY @  4 + ! $/
      /$ addr T3  TEXT.ARRAY @  8 + ! $/
      /$ addr T4  TEXT.ARRAY @ 12 + ! $/
      /$ addr T5  TEXT.ARRAY @ 16 + ! $/
      /$ addr T6  TEXT.ARRAY @ 20 + ! $/
      /$ addr T7  TEXT.ARRAY @ 24 + ! $/
      /$ addr T8  TEXT.ARRAY @ 28 + ! $/
      /$ addr T9  TEXT.ARRAY @ 32 + ! $/
      /$ addr T10 TEXT.ARRAY @ 36 + ! $/
      /$ addr T10A TEXT.ARRAY @  40 + ! $/
      /$ addr T11  TEXT.ARRAY @  44 + ! $/
      /$ addr T12  TEXT.ARRAY @  48 + ! $/
      /$ addr T13  TEXT.ARRAY @  52 + ! $/
      /$ addr T14  TEXT.ARRAY @  56 + ! $/
      /$ addr T15  TEXT.ARRAY @  60 + ! $/
      /$ addr T16  TEXT.ARRAY @  64 + ! $/
      /$ addr T17  TEXT.ARRAY @  68 + ! $/
      /$ addr T18  TEXT.ARRAY @  72 + ! $/
      /$ addr T19  TEXT.ARRAY @  76 + ! $/
      /$ addr T20  TEXT.ARRAY @  80 + ! $/
      /$ addr T21  TEXT.ARRAY @  84 + ! $/
      /$ addr T22  TEXT.ARRAY @  88 + ! $/
      /$ addr T23  TEXT.ARRAY @  92 + ! $/
      /$ addr T24  TEXT.ARRAY @  96 + ! $/
      /$ addr T25  TEXT.ARRAY @ 100 + ! $/
      /$ addr T25A TEXT.ARRAY @ 104 + ! $/
      /$ addr T26  TEXT.ARRAY @ 108 + ! $/
      /$ addr T27  TEXT.ARRAY @ 112 + ! $/
      /$ addr T28  TEXT.ARRAY @ 116 + ! $/
      /$ addr T29  TEXT.ARRAY @ 120 + ! $/
      /$ addr T30  TEXT.ARRAY @ 124 + ! $/
      /$ addr T31  TEXT.ARRAY @ 128 + ! $/
      /$ addr T32  TEXT.ARRAY @ 132 + ! $/
      /$ addr T33  TEXT.ARRAY @ 136 + ! $/
      /$ addr T34  TEXT.ARRAY @ 140 + ! $/
      /$ addr T35  TEXT.ARRAY @ 144 + ! $/
      /$ addr T36  TEXT.ARRAY @ 148 + ! $/
      /$ addr T37  TEXT.ARRAY @ 152 + ! $/
      /$ addr T38  TEXT.ARRAY @ 156 + ! $/
      /$ addr T39  TEXT.ARRAY @ 160 + ! $/
      /$ addr T40  TEXT.ARRAY @ 164 + ! $/
      /$ addr T41  TEXT.ARRAY @ 168 + ! $/
      /$ addr T42  TEXT.ARRAY @ 172 + ! $/
      /$ addr T43  TEXT.ARRAY @ 176 + ! $/
      /$ addr T44  TEXT.ARRAY @ 180 + ! $/
      /$ addr T45  TEXT.ARRAY @ 184 + ! $/
      /$ addr T46  TEXT.ARRAY @ 188 + ! $/
      /$ addr T47  TEXT.ARRAY @ 192 + ! $/
      /$ addr T48  TEXT.ARRAY @ 196 + ! $/
      /$ addr T49  TEXT.ARRAY @ 200 + ! $/
      /$ addr T50  TEXT.ARRAY @ 204 + ! $/
      /$ addr T51  TEXT.ARRAY @ 208 + ! $/
      /$ addr T52  TEXT.ARRAY @ 212 + ! $/
    END;
  END INITS;
BEGIN 
    INITS;
END MKOR.
