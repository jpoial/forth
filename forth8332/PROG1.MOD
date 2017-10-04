MODULE prog1;
(* This program writes 'hello' on the screen *)
FROM IO IMPORT WrStr,WrCard;
BEGIN
  WrStr(' hello');
  WrCard(345,3)
END prog1.
