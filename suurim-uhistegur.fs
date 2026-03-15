\
\ Suurima Ühisteguri Leidmine (GCD) - GForth rakendus
\ Kasutab Eukleidese algoritmi

\ Funktsioon: GCD
\ Sisend: kaks täisarvu (a b)
\ Väljund: nende suurim ühistegur
: GCD ( a b -- gcd )
  BEGIN
    DUP 0= IF               \ Kui teine arv on null, tagasta esimene arv
      DROP EXIT
    THEN
    OVER DUP > IF           \ Kui a > b, arvuta a mod b ja vaheta
      OVER MOD SWAP
    ELSE
      SWAP OVER MOD         \ Kui b >= a, arvuta b mod a ja vaheta
    THEN
  AGAIN
;

\ Funktsioon: TEST-GCD
\ Testib GCD funktsiooni ja kuvab tulemuse
: TEST-GCD ( a b -- )
  2DUP ." GCD(" . ." , " . ." ) = "  \ Kuvame sisendväärtused
  GCD . CR                           \ Arvutame ja kuvame ühisteguri
;

\ Põhiprogramm
: MAIN
  CR ." Suurima Ühisteguri Kalkulaator (GCD)" CR
  ." =======================================" CR CR
  
  \ Testandmed
  ." Testandmed:" CR
  12 8 TEST-GCD
  100 25 TEST-GCD
  42 18 TEST-GCD
  7 3 TEST-GCD
  144 60 TEST-GCD
  50 30 TEST-GCD
  105 45 TEST-GCD
  
  CR ." =======================================" CR
;

\ Käivita programm
MAIN
BYE
