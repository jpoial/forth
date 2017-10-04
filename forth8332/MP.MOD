MODULE MKORPOHI;
IMPORT MKOR;
FROM DBF IMPORT OpenDBFro,CloseDBF,MBase;

VAR KFail:  WORD;
    MFail:  WORD;
    tf: BOOLEAN;

BEGIN
 FORTH
 /$  F+P @ addr MFail ! $/
 END;
  tf := OpenDBFro('KUNDE','KUNDED.MDB',KFail);
 FORTH
 /$  addr MFail @ F+P ! $/
 END;
  MBase;
  tf := CloseDBF(KFail);
END MKORPOHI.