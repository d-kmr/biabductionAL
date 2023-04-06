#include <stdio.h>

int result;

struct List { struct List *next; } a[10], *x;

struct List *Last(struct List *p) {
  while (p -> next != NULL) p = p -> next;
  return p;
}

void main() {
  a[0].next = a + 1;
  a[1].next = a + 2;
  a[2].next = a + 3;
  a[3].next = NULL;
  x = Last(a);
  if (x == a+3) result = 2; else result = 1; /* 2 */
}
