IMPLEMENTATION MODULE MK;

FROM DBF IMPORT GetByKey,ClearRecord;
IMPORT PA;

VAR klient : PA.KLIENT;
    maks :   MKORTYYP;
    KFail : WORD;

PROCEDURE TuuaMaksjaAndmed;
BEGIN
   FORTH
       /$ DIA-PARA @ F+P ! addr maks BUF->REC $/
   END;
   klient.PartneriNr := maks.MaksjaNr;
   FORTH
       /$ CO-FILE @ addr KFail !  $/
   END;
   IF GetByKey(KFail,klient) 
   THEN ClearRecord(maks);
        maks.MaksjaNimetus:=klient.PartnNimetus;
        maks.MNimetuseJatk:=klient.NimetuseJatk; 
        maks.MaksjaKood:=klient.Kood;
        maks.MaksjaPKorArveNr := klient.PKorArveNr; 
        maks.MaksjaPangaNimi:=klient.PangaNimi;
        maks.MaksjaPangaLinn:=klient.PangaLinn;
        maks.MaksjaPKood:=klient.PKood;
        maks.MaksjaArveNr:=klient.ArveNr;
        maks.MVahendPangaNimi:=klient.VahendPangaNimi;
        maks.MVahendPangaLinn:=klient.VahendPangaLinn;
        FORTH
            /$ DIA-PARA @ F+P !       $/
            /$ addr maks KIRJE @ MEST $/
        END;
   END; 
   FORTH
       /$ DIA-PARA @ F+P ! $/
   END;
END TuuaMaksjaAndmed;

PROCEDURE TuuaSaajaAndmed;
BEGIN
   FORTH
       /$ DIA-PARA @ F+P ! addr maks BUF->REC $/
   END;
   klient.PartneriNr := maks.SaajaNr;
   FORTH
       /$ CO-FILE @ addr KFail !  $/
   END;
   IF GetByKey(KFail,klient) 
   THEN ClearRecord(maks);
        maks.SaajaNimetus:=klient.PartnNimetus;
        maks.SNimetusJatk:=klient.NimetuseJatk; 
        maks.SaajaKood:=klient.Kood;
        maks.SaajaPKorArveNr:=klient.PKorArveNr;
        maks.SaajaPangaNimi:=klient.PangaNimi;
        maks.SaajaPangaLinn:=klient.PangaLinn;
        maks.SaajaPKood:=klient.PKood;
        maks.SaajaArveNr:=klient.ArveNr;
        maks.SVahendPangaNimi:=klient.VahendPangaNimi;
        maks.SVahendPangaLinn:=klient.VahendPangaLinn;
        FORTH
            /$ DIA-PARA @ F+P !       $/
            /$ addr maks KIRJE @ MEST $/
        END;
   END; 
   FORTH
       /$ DIA-PARA @ F+P ! $/
   END;
END TuuaSaajaAndmed;

PROCEDURE TaitaSummaSonades;
   BEGIN
   ClearRecord(maks);
   maks.SummaSonades:='      rubla ja    kopikat';
   FORTH
       /$ addr maks KIRJE @ MEST $/
   END;
   END TaitaSummaSonades;

PROCEDURE INITS;
  VAR T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T10A,
      T11,T12,T13,T14,T15,T16,T17,T18,T19,T20,
      T21,T22,T23,T24,T25,T25A,T26,T27,T28,T29,T30,
      T31,T32,T33,T34,T35,T36,T37,T38,T39,T40,
      T41,T42,T43,T44,T45,T46,T47,T48,T49,T50,
      T51,T52: ARRAY [1..80] OF CHAR;
      KIRJELDUS: ARRAY [1..8] OF CHAR;
BEGIN
T1 :=  'ÚÄÄÄÄÄÄÄÄÄÄÄ¿';
T2 :=  'Maksekorraldus Nr.³';
T3 :=  '³      0401002';
T4 :=  'ÀÄÄÄÄÄÄÄÄÄÄÄÙ';
T5 :=  '.';
T6 :=  '.a.';
T7 :=  '    Maksja';
T8 :=  'DEEBET      Summa';
T9 :=  '   ÚÄÄÄÄÄÄÄÄÄÄÄÄ¿                                      ÚÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄ¿';
T10 := '   ³Kood';
T10A := '³';
T11 := '³';
T12 := '³          ³';
T13 := '   ÀÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄÄ´          ³';
T14 := '³';
T15 := '³';
T16 := '³';
T17 := '.';
T18 := '³';
T19 := '³           ³           ³          ³';
T20 := '    Maksja pank               Linn         ³ Kood      ³Arve Nr.   ³          ³';
T21 := '   ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÙ';
T22 := '    Saaja';
T23 := 'KREEDIT';
T24 := '   ÚÄÄÄÄÄÄÄÄÄÄÄÄ¿                                      ÚÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄ¿';
T25 := '   ³Kood';
T25A := '³';
T26 := '³';
T27 := '³          ³';
T28 := '   ÀÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÂÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄ´';
T29 := '³';
T30 := '³';
T31 := '³          ³';
T32 := '³           ³           ³          ³';
T33 := '    Saaja pank                Linn         ³ Kood      ³Arve Nr.   ³          ³';
T34 := '   ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÁÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÄÄÄÄÄÄ´';
T35 := 'Postiga - telegraafiga                      ³Viivis    ³';
T36 := 'ÃÄÄÄÄÄÄÄÄÄÄ´';
T37 := '³Kokku     ³';
T38 := '    Summa sonadega                                                 ³          ³';
T39 := '   ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÂÄÄÄÄÄ´';
T40 := '    Kauba/teenuse saamise kuupaev                                  ³Oper³     ³';
T41 := '   ÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÄÅÄÄÄÄÅÄÄÄÄÄ´';
T42 := '    Makse eesmark                                                  ³    ³     ³';
T43 := 'ÃÄÄÄÄÅÄÄÄÄÄ´';
T44 := '³    ³     ³';
T45 := 'ÃÄÄÄÄÅÄÄÄÄÄ´';
T46 := '³    ³     ³';
T47 := 'ÃÄÄÄÄÅÄÄÄÄÄ´';
T48 := '³    ³     ³';
T49 := 'ÀÄÄÄÄÁÄÄÄÄÄÙ';
T50 := '   ÚÄÄÄÄÄÄÄÄÄÄ¿                                      ³';
T51 := '   ³   P.K.   ³            Kliendi allkirjad         ³    Panga allkirjad';
T52 := '   ÀÄÄÄÄÄÄÄÄÄÄÙ                                      ³';
  KIRJELDUS := 'MK';
    FORTH
      /$ 0 GET-FP $/ 
      /$ ['] MKORTYYP EXECUTE 12 + @ KIRJETYYP !      $/
      /$ addr KIRJELDUS DEFNAME !                     $/
      /$ 6 #KOMPLEKT ! $/ 
      /$ ['] MKorrNrJargi      KEY.ARRAY @      ! $/ 
      /$ ['] SaajaNrJargi      KEY.ARRAY @  4 + ! $/ 
      /$ ['] KuupaevaJargi     KEY.ARRAY @  8 + ! $/ 
      /$ ['] RahasummaJargi    KEY.ARRAY @ 12 + ! $/ 
      /$ ['] MaksjaArveNrJargi KEY.ARRAY @ 16 + ! $/ 
      /$ ['] SaajaArveNrJargi  KEY.ARRAY @ 20 + ! $/ 
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
      /$ 3 #PROTS ! $/
      /$ ['] TuuaMaksjaAndmed  PROCED.ARRAY @ !     $/
      /$ ['] TuuaSaajaAndmed   PROCED.ARRAY @ 4 + ! $/ 
      /$ ['] TaitaSummaSonades PROCED.ARRAY @ 8 + ! $/
    END;
END INITS;

BEGIN
 INITS;
END MK.
