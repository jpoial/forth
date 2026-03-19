\ A simple number guessing game for GForth.
\ Run with: gforth guessing-game.fs

: secret-number ( -- n )
  utime drop 100 mod 1+ ;

: read-guess ( -- n )
  pad 32 erase
  ." Enter your guess (1-100): "
  pad 32 accept
  pad swap evaluate ;

: play-round ( -- )
  secret-number
  0
  begin
    read-guess >r
    1+
    over r@ =
    if
      cr ." Correct! You needed " . ." guesses." cr
      rdrop drop
      true
    else
      over r@ >
      if
        cr ." Too low. Try again." cr
      else
        cr ." Too high. Try again." cr
      then
      r> drop
      false
    then
  until ;

: play-again? ( -- flag )
  cr ." Play again? (y/n): "
  key dup emit cr
  dup [char] y = swap [char] Y = or ;

: guessing-game ( -- )
  cr ." Welcome to the guessing game!" cr
  ." I am thinking of a number between 1 and 100." cr
  begin
    play-round
    play-again?
  while
    cr ." Starting a new round..." cr
  repeat
  cr ." Thanks for playing!" cr ;

guessing-game
bye
