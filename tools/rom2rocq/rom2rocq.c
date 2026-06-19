#include <assert.h>
#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static const char *definition = "rom";
static int tabsize = 2;
static unsigned char *data = NULL;
static size_t datasize = -1;
static FILE *out = NULL;

static const char *usage = "rom2rocq [-h] [-i INDENT] [-n NAME] [-o FILE] file";

static void
help()
{
    printf("%s\n\n", usage);
    printf("    -n NAME     The name of the Rocq definition (default: \"rom\")\n");
    printf("    -i INDENT   The number of spaces to indent (default: 2)\n");
    printf("    -o FILE     The output file (default: -)\n");
    printf("    -h          Print this message\n");
}

static void*
emalloc(size_t sz)
{
    void *p = malloc(sz);
    if (p == NULL)
        errx(1, "out of memory");
    return p;
}

static char*
estrdup(char *s)
{
    char *r = emalloc(strlen(s) + 1);
    return strcpy(r, s);
}

static void
loadfile(const char *path)
{
    FILE *f;
    struct stat st;

    if (stat(path, &st) != 0)
        err(1, "%s", path);
    datasize = st.st_size;
    if ((f = fopen(path, "rb")) == NULL)
        err(1, "%s", path);
    data = emalloc(st.st_size);
    if (fread(data, 1, datasize, f) != datasize)
        err(1, "%s", path);  /* TODO: short read. */
}

static void
indent(int depth)
{
    for (int i = 0; i < depth * tabsize; i++)
        fputc(' ', out);
}

/*
  Definition example : pmap N :=
    (Branch (Some 1)                        (*    1 *)
      (Branch (Some 2)                      (*   10 *)
        (Branch (Some 4)                    (*  100 *)
          (Branch (Some 8) Empty Empty)     (* 1000 *)
          (Branch (Some 12) Empty Empty))   (* 1100 *)
        (Branch (Some 6)                    (*  110 *)
          (Branch (Some 10) Empty Empty)    (* 1010 *)
          (Branch (Some 14) Empty Empty)))  (* 1110 *)
      ...
*/

static void
printtree(size_t i, int d)
{
    if (i >= datasize) {
        indent(d+2), fprintf(out, "Empty\n");
    } else {
        indent(d+2), fprintf(out, "(Branch (Some 0x%02x) (* 0x%08zx *) \n", data[i], i);
        printtree(i&~(3<<d)|(2<<d), d+1);
        printtree(i&~(3<<d)|(3<<d), d+1);
        indent(d+2), fprintf(out, ")\n");
    }
}

static void
printfile()
{
    fprintf(out, "Require Import ExtLib.Data.Map.FMapPositive.\n");
    fprintf(out, "From GameBoy Require Import Data.Map.FMapNat.\n");
    fprintf(out, "From GameBoy Require Import Stdint.\n");
    fprintf(out, "Open Scope u8_scope.\n");
    fprintf(out, "\n");

    if (datasize == 0) {
        fprintf(out, "Definition %s : nmap u8 := nmap_empty u8.\n", definition);
    } else {
        fprintf(out, "Definition %s : nmap u8 :=\n", definition);
        indent(1), fprintf(out, "NMap (Some 0x%02x) (* 0x%08x *)\n", data[0], 0);
        printtree(1, 0);
        indent(1), fprintf(out, ".\n");
    }
}

int
main(int argc, char *argv[])
{
    int c;
    out = stdout;
    while ((c = getopt(argc, argv, "n:ho:w:")) != -1) {
        switch (c) {
        case 'n':
            definition = estrdup(optarg);
            break;
        case 'i':
            tabsize = atoi(optarg);
            break;
        case 'o':
            if (!strcmp(optarg, "-"))
                break;
            if ((out = fopen(optarg, "w")) == NULL)
                err(1, "%s", optarg);
            break;
        case 'h':
            help();    
            exit(0);
        default:
            errx(1, "usage: %s", usage);
        }
    }
    argc -= optind;
    argv += optind;
    if (argc != 1)
        errx(1, "usage: %s", usage);
    loadfile(argv[0]);
    printfile();
    return 0;
}