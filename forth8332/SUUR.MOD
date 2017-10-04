MODULE SUUR;
TYPE DATE=RECORD DAY:[1..31]; MONTH: [1..12];
                 YEAR:CARDINAL ; END ;
TYPE Inime=RECORD
  Eesnimi,Nimi: ARRAY[1..10] OF CHAR;
  CASE Mees: BOOLEAN OF
          TRUE:Aukraad: ARRAY[1..12] OF CHAR |
          FALSE: Neiuna: ARRAY[1..10] OF CHAR; END;           
       Ident:CARDINAL;
       Synd: DATE;                                    
  CASE Seis:BOOLEAN OF                                               
          FALSE: |
          TRUE: Abikaasa: ARRAY[1..20] OF CHAR;
                Lapsi: CARDINAL;
                Pulm: DATE;      
END; END;
VAR X: Inime; BEGIN WITH X DO
  Eesnimi:='MATI'; Nimi:='TOMBAK';                         
  Mees:=TRUE; CASE Mees OF 
        TRUE: Aukraad:='REAMEES' |
        FALSE: Neiuna:='EIMRE';  END;
  Ident:=1501;
  WITH Synd DO
       DAY:=25; MONTH:=1; YEAR:=1942;
            END;                        
  Seis:=TRUE; CASE Seis OF
        TRUE:
        Abikaasa:='TIIU EIMRE'; Ident:=777;
         Pulm.DAY:=2; Lapsi:=0; Pulm.MONTH:=7; Lapsi:=2; END;
  Ident:=1000;  END;          
END SUUR .
