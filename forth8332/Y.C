/* 
typedef
   struct
   {
      char ll[2];
      char np;
   }
   LINETYPE;

int vElines[] =
   {
      { "\0\0", '\0' },
      { "ID", '\xFF'},
      { "AC", '\xFF'},
      { "DT", '\xFF'},
      { "DE", '\xFF'},
      { "KW", '\xFF'},
      { "OS", '\xFF'},
      { "OC", '\xFF'},
      { "RN", '\xFF'},
      { "RA", '\xFF'},
      { "RT", '\xFF'},
      { "RL", '\xFF'},
      { "FH", '\xF0'},
      { "FT", '\xFF'},
      { "SQ", '\xFF'},
      { "  ", '\xFF'},
      { "CC", '\xFF'},
      { "XX", '\xF0'},
      { "//", '\xFF'},
      { "OG", '\x0F'},
      { "DR", '\x0F'}
   };
*/
int sElinecode (line)
char *line;


{
/*
   int i;
   for ( i = 1 ; i <= MAXLINECODE; i++)
*/
      if ( line[0] == vElines[i].ll [0] &&
	   line[1] == vElines[i].ll [1] )
	 return(i);
   return(0);
};
