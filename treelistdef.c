#include<stdlib.h>

struct sll {int key; struct sll *next;};
typedef struct sll **sllbox;

struct tree {int key; int value; struct tree *left, *right;};
typedef struct tree **treebox;

void dummylist()
{
   struct sll *sllDummy = (struct sll *) malloc (sizeof *sllDummy);
   free(sllDummy);
}

void dummyTree()
{
    struct tree *treeDummy = (struct tree *) malloc (sizeof *treeDummy);
    free(treeDummy);
}