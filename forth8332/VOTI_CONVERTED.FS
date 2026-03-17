Modula2DataBase                                                 
Key support.                                                    
                     ╔═════════════════════════╗                
MASTER_RECORD+32:══>0║ >makett    keykompl. 1  ║                
MASTER_RECORD+36:N  4║ komplekt1 passi SA      ║                
                     ╠═════════════════════════╣                
                            .   .   .   .                       
                     ╠═════════════════════════╣                
                     ║ >makett    keykompl. N  ║                
     ┌───────────────Â komplektN passi SA      ║                
     │               ╚═════════════════════════╝                
   ┌─┴──────────┬────────┬─────┬──────┬─ ─┬──┬────┐             
   │ 0: L(konka)│2: #keys│4: l1│6: SA1│...│ln│SAn │             
   └────────────┴────────┴─────┴──────┴─ ─┴──┴────┘             
                                                                
                                                                
\ #1 Fill KEY-TAB, KEYSHOW                           10/08/90 ) 
( komplektikirjete tyybid )                                     
VARIABLE KEY-INDEX   ( komponentide koguarvu loendaja )         
VARIABLE #KOMPLEKT                                              
                                                                
: >TABEL ( i --- A )                                            
8 * MASTER_RECORD DUP 32 + H@ + + ;                             
                                                                
: KEYSHOW ( --- )                                               
>vPUHVER >STOREHOUSE KEYDEPOT @ DUP JUURIK ! AIT !              
CURSOR-ON PILTETTE DB-EDIT CURSOR-OFF STOREHOUSE>               
<vPUHVER ;                                                      
                                                                
: KEY.PASS ( cfa --- pass )                                     
EXECUTE 12 + @ ;                                                
-->                                                             
\ #2 Put length & shift of a key                     04/25/91 ) 
VARIABLE NIMEPLATS 40 DECL NIMEPLATS !                          
VARIABLE PEARETS  ( originaal-kirjetüüp )                       
VARIABLE CONTX ( hoiul ) VARIABLE CONTrec                       
VARIABLE AI    ( MASTER_RECORDi järje absaadress )              
: GET-K-NAME ( >pass --- >pass >nfa )                           
DUP 4 - BODY> >NAME ;                                           
: KEILA ( >pass --- >pass )                                     
DUP ?TYPE ?TSIZE AI @ H! 2 AI +!  ( pikkus )                    
4 + @  AI @ H! 2 AI +!            ( nihe ) ;                    
: KEY.ERROR ( >pass --- >pass )                                 
H-WINDOW W-CLEAR 1 1 H-WINDOW W-GOTOXY                          
." Invalid keytype:  " GET-K-NAME .NAME KEY DROP ABORT ;        
: >KOMPLEKT ( I --- )                                           
>TABEL 4 + AI @ MASTER_RECORD - SWAP ! ;                        
-->                                                             
\ #3 Get originalfields chain                        04/25/91 ) 
( otsib vôtmepassi nime abil kirjevälja passi. )                
: VINT ( >nfa.key  --- >pass.originaal )                        
NIMEPLATS @ >R DUP C@ 31 AND                                    
R@ SWAP 1+ CMOVE R@ C@ 31 AND R@ C!                             
R@ DUP C@ + DUP C@ 128 - SWAP C!                                
CONTrec @ CONTEXT !                                             
R> FIND 0= IF H-WINDOW W-CLEAR 1 1 H-WINDOW W-GOTOXY            
              ." Valevôti!  " NIMEPLATS @ DUP C@ SWAP 1+ SWAP   
              TYPE KEY DROP CONTX @ CONTEXT ! ABORT             
           ELSE 4 + >BODY CONTX @ CONTEXT !                     
           THEN ;                                               
: LjaSA ( >pass --- >pass )                                     
GET-K-NAME VINT KEILA ;                                         
-->                                                             
                                                                
\ #4 Make keysequence                                04/25/91 ) 
( tsykkel yle vôtmekirje, otsib nime järgi kirjeväljad ja teeb  
vôtmekomplekti passi. AI on järje abs-aadress MASTER_RECORDis ) 
: WEKTOR ( --- )                                                
KIRJETYYP @ DUP 8 + @ 1+ AI @ H! 2 AI +!  ( konka pikkus )      
DUP 12 + @ AI @ H! 2 AI +!                ( vôtmete arv  )      
24 + @                                    ( esimene pass )      
BEGIN DUP ?T                                                    
 CASE 1 OF LjaSA                 ENDOF                          
      2 OF KEY.ERROR             ENDOF                          
      3 OF LjaSA                 ENDOF                          
 ENDCASE                                                        
   16 + @ DUP 0 = IF DROP EXIT THEN ( next )                    
AGAIN ;                                                         
-->                                                             
                                                                
\ #5 Make keysequences structure                     04/25/91 ) 
: Key-SUPPORT ( --- )                                           
>STOREHOUSE 0 JUURIK ! 0 KUVAR ! 0 AIT !                        
0 NihE ! 0 TREPP ! KIRJETYYP @ MakeDISPLAY DROP                 
JUURIK @ KEYDEPOT ! STOREHOUSE> ;                               
: KEY-INST ( A.keytabel --- )                                   
#KOMPLEKT @ 0 >                                                 
IF #KOMPLEKT @ 8 * + AI !                                       
   KIRJETYYP @ DUP PEARETS ! 20 + @ CONTrec !                   
   CONTEXT @ CONTX ! #KOMPLEKT @ 0                              
   DO I >KOMPLEKT I 4 * KEY.ARRAY @ + @ KEY.PASS KIRJETYYP !    
      WEKTOR Key-SUPPORT KEYDEPOT @ I >TABEL !                  
   LOOP PEARETS @ KIRJETYYP !                                   
THEN ;                                                          
-->                                                             
                                                                
\ #6 KEY-SUPPORT: initialisation keyscreen           04/26/91 ) 
: KEY-SUPPORT ( --- )                                           
KIRJETYYP @ PEARETS !                                           
MASTER_RECORD 34 + H@ ?DUP                                      
  IF 0 DO I 4 * KEY.ARRAY @ + @ KEY.PASS KIRJETYYP !            
          Key-SUPPORT KEYDEPOT @ I >TABEL !                     
       LOOP                                                     
     PEARETS @ KIRJETYYP !                                      
     1 MASTER_RECORD 6 + H! ACT-INX                             
  THEN ;                                                        
: KEYNUMBER ( --- | vôtmete koguarv > KEY-INDEX )               
0 KEY-INDEX ! #KOMPLEKT @ 0                                     
 DO I 4 * KEY.ARRAY @ + @ KEY.PASS 12 + @ KEY-INDEX +! LOOP ;   
;S                                                              
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
                                                                
