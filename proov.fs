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
4 z @ . CR

' z >BODY 4 CELLS + @ .

: wait-space ( --- )
  BEGIN
    CR ." Press space bar "
    KEY DUP EMIT 32 = 0=
  WHILE
    CR ." Try again "
  REPEAT
  CR ." That's ok " ;

: fact ( n --- n! )
 DUP 1 > 
 IF 
    DUP 1 
       DO 
          I * 
       LOOP 
 ELSE 
    DROP 1 
 THEN ;

