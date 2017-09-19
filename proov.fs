[IFDEF] forget
    forget
[ENDIF]

MARKER forget

: test ( flag --- )
    DUP . ." is "
    IF ." true"
    ELSE ." false"
    THEN 
    CR ;

-1 test

: myConst CREATE , DOES> @ ;

7 myConst x
x . CR

: myVar CREATE , DOES> ;

6 myVar y
y DUP . ." contains " @ . CR

: myArray CREATE CELLS ALLOT
          DOES> SWAP CELLS + ;

10 myArray z
66 4 z !
4 z @ .

' z >BODY 4 CELLS + @ .

