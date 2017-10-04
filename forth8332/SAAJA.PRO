PROCEDURE Saaja;
BEGIN
        FORTH
        /$ F+P @ i-ATOM ! $/
        END;
   Klient.KUNDENUMBER := maks.SAAJANUMBER;
   IF GetByKey(kFail,Klient) 
   THEN
        FORTH     
        /$ addr i-ATOM @ F+P ! $/
        /$ KIRJE @ addr maks ! $/
        END; 
        maks.SAAJANIMETUS:=Klient.NIMETUS;
        maks.SKOOD:=KLlient.KOOD;
        maks.SPANGANIMI:=Klient.PANGANIMI;
        maks.SPANGALINN:=Klient.PANGALINN;
        maks.SARVEKOOD:=Klient.ARVEKOOD;
        maks.SARVENR:=Klient.ARVENR;
   END;
END Saaja;