#include <stdio.h>
#include <stdlib.h>

struct node {
    int data;
    struct node* next;
};

struct node* array_to_linked_list(int arr[], int len) {
    struct node* head = (struct node*)malloc(sizeof(struct node));

    head->data = arr[0];
    head->next = NULL;

    struct node* curr = head;

	struct node* new_node;
	int i = 0;
	while (i < len) {
	  new_node = (struct node*)malloc(sizeof(struct node));
	  new_node->data = arr[i];
	  new_node->next = NULL;
	  curr->next = new_node;
	  curr = new_node;
	  i++;
	}
    return head;
}

int main() {
  int len = 100;
  int arr[len];
  int i = 0;
  while(i<len) { arr[i] = i; i++; }
  
  struct node* curr = array_to_linked_list(arr, len);
  struct node* temp;
  while (curr != NULL) {
	temp = curr;
	curr = curr->next;
	free(temp);
  }

  return 0;
}
