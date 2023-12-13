#include <stdio.h>
#include <string.h>

// Function to swap values of two integers using pointers
void swap(int *a, int *b) {
    int temp = *a;
    temp = *b;
    /*
    int shihao =3;
    shihao += temp;
    *a = *b;
    //a++;
    *b = temp;
    */
    //printf("Swapped x and y: %d, %d\n", a, b);
}
// Function to calculate the sum of an array using pointers
int arraySum(int *arr, int size) {
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += *(arr + i);
    }
    return sum;
}

// Function to reverse a string in place
void reverseString(char *str) {
    int n = strlen(str);
    for (int i = 0; i < n / 2; i++) {
        char temp = str[i];
        str[i] = str[n - i - 1];
        str[n - i - 1] = temp;
    }
}

// Function to print an integer array
void printArray(int *arr, int size) {
    for (int i = 0; i < size; i++) {
        printf("%d ", arr[i]);
    }
    printf("\n");
}

int main() {
    int x = 10;
    int y = 20;
    swap(&x, &y);
    printf("Swapped x and y: %d, %d\n", x, y);
    swap(&x, &y);
    int numbers[] = {1, 2, 3, 4, 5};
    swap(&x, &y);
    int size = sizeof(numbers) / sizeof(numbers[0]);
    printf("Original array: ");
    printArray(numbers, size);
    printf("Sum of array elements: %d\n", arraySum(numbers, size));

    char str[] = "Hello, world!";
    printf("Original string: %s\n", str);
    reverseString(str);
    printf("Reversed string: %s\n", str);

    return 0;
}
