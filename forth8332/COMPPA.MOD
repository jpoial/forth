MODULE COMPPA;
BEGIN
FORTH
/$ ENV!                                                 $/
/$ LIT" BASE.DEF"     DUP SET_WFILE SET_MFILE M2COMPILE $/
/$ LIT" PA.DEF"       DUP SET_WFILE SET_MFILE M2COMPILE $/
/$ LIT" BASE.MOD"     DUP SET_WFILE SET_MFILE M2COMPILE $/
/$ LIT" PA.MOD"       DUP SET_WFILE SET_MFILE M2COMPILE $/
/$ LIT" MAINPA.MOD"   DUP SET_WFILE SET_MFILE M2COMPILE $/
END;
END COMPPA.
