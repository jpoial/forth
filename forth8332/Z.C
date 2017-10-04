void cCopenin (int * * );
void cCopenout (int * * );
void emb23to15 (int *, int *);
void indfile (int *, char *, char *);
int sElinecode (char *);


void main ()

{
   int *inf,*outf;

   printf ("\nConvert EMBL nucleotide data Release 23 to Release 15\n");
   cCopenin (&inf);
   cCopenout (&outf);

   emb23to15 (inf, outf);

   fclose (inf);
   fclose (outf);
}

void cCopenin (file)
int **file;

{
   char fname[66] = "";
   char line[256];

   for ( *file = NULL; *file == NULL ; )
   {
      printf ("\nInput file name (Enter to exit): ");
      gets (line);
      sscanf (line, "%s", fname);
      if ( fname[0] == '\0' )
	 exit(0);

      *file = fopen (fname, "r");

      if ( *file == NULL )
	 printf ("\nUnable to open file %s. (Error code %d)", fname, errno);
   }
}

void cCopenout (file)
int **file;

{
   char fname[66] = "";
   char line[256];

   for ( *file = NULL; *file == NULL ; )
   {
      printf ("\nOutput file name (Enter to exit): ");
      gets (line);
      sscanf (line, "%s", fname);
      if ( fname[0] == '\0' )
	 exit(0);

      *file = fopen (fname, "w");

      if ( *file == NULL )
	 printf ("\nUnable to create file %s. (Error code %d)",
		 fname, errno);
   }
}

void emb23to15 (inf, outf)
int *inf;
int *outf;

{
   char line[82];
   char name[12], class[13], moltype[5], division[5], size[11], unit[4];
   long int numsize;
   char *ptr;
   int i;
   int code;

   while ( fgets (line, 81, inf) != NULL )
   {
      code = sElinecode(line);
      switch (code)
      {
	 case ID:
	    sscanf (line+5, "%s %s %s %s %s %s",
			 name, class, moltype, division, size, unit);

	    for ( i  =  strlen(name); i < 9 ; name[i++] = ' ' );
	    name[9] = '\0';

	    printf (name);

	    strlwr (moltype);
	    if ( !strcmp (moltype, "xxx;") )
	       strcpy (moltype, "DNA;");
	    sprintf (line, "ID   %s %s %s %s %s \n",
			name, class, moltype, size, unit);
	    numsize = strtol (size, &ptr, 10);
	    if ( numsize > 25000 )
	    {
	       indfile (inf, name, line);
	       continue;
	    }
	    break;
	 case bl:
	    break;
	 case XX:
	    continue;
	 case sh:
	    break;
	 case KW:
	    if ( !strcmp (line+5, ".\n") )
	       continue;
	 default:
	    if ( strlen (line) <= 6 )
	       continue;
      }
      strupr (line);
      if ( fputs (line, outf) == EOF )
      {
	 printf ("Error writing output file");
	 exit (8);
      }
   }
}


void indfile (inf, name, first)
int *inf;
char *name;
char *first;

{
   char line[82];
   char iname[13];
   int *outf;
   int code;

   iname[0] = 'N';
   iname[1] = '\0';
   strncat (iname, name, 7);
   if ( strlen (name) > 7 )
   {
      iname[8] = '.';
      iname [9] = '\0';
      strcat (iname, name + 7);
   }
   else
      iname[8] = '\0';
   printf ("\nCreating individual file %s\n", iname);

   outf = fopen (iname, "w");

   if (outf == NULL )
      printf ("\nUnable to create file %s. (Error code %d)",
		 iname, errno);

   strupr (first);
   if ( fputs (first, outf) == EOF )
   {
      printf ("Error writing individual file %s", iname);
      exit (8);
   }

   line[0] = '\0';
   while ( fgets (line, 81, inf) != NULL )
   {
      code = sElinecode (line);
      switch (code)
      {
	 case bl:
	    strupr (line);
	    break;
	 case XX:
	    continue;
	 case sh:
	    break;
	 case KW:
	    if ( !strcmp (line+5, ".\n") )
	       continue;
	 default:
	    if ( strlen (line) <= 6 )
	       continue;
      }
      strupr (line);
      if ( fputs (line, outf) == EOF )
      {
	 printf ("Error writing individual file %s", iname);
	 exit (8);
      }
      if ( code == sh )
	 break;
   }
   fclose (outf);
}
