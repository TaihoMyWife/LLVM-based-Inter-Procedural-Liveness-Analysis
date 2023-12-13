#include <stdio.h>
#include <stdlib.h>

// Function declaration: This function takes a double pointer (pointer to pointer)
// as an argument and modifies the memory it points to
void modifyArray(int **arr, int size) {
    // Allocate memory for the array
    *arr = (int *)malloc(size * sizeof(int));
    
    // Populate the array
    for (int i = 0; i < size; i++) {
        (*arr)[i] = i * i; // Square of the index
    }
}

int main() {
    int *array = NULL; // Pointer to an integer array
    int size = 5;      // Size of the array

    // Call the function with the address of the pointer variable
    modifyArray(&array, size);

    // Print the modified array
    printf("Modified array: ");
    for (int i = 0; i < size; i++) {
        printf("%d ", array[i]);
    }
    printf("\n");

    // Free the allocated memory
    free(array);

    return 0;
}

