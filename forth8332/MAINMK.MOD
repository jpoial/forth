MODULE MAINMK;
IMPORT MK;
FROM BASE IMPORT MBase;
FROM DBF IMPORT InitDBFs,OpenDBFro;
VAR CoFile: WORD;
BEGIN
 IF OpenDBFro('PA','PAFAIL.MDB',CoFile) THEN END;
  FORTH
      /$ 0 GET-FP  $/
      /$ addr CoFile @ CO-FILE ! $/ 
  END;
  MBase;
END MAINMK.
