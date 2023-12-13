#include <stdio.h>

void increment(int *value) {
    (*value)++;
}

void doubleValue(int *value) {
    *value = *value * 2;
}

void swap(int *a, int *b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}

int main() {
    int x = 10;
    int y = 20;
    int *f = &y;

    increment(f);
    printf("Original x: %d\n", x);
    printf("Original y: %d\n", y);

    // Call increment function
    increment(&x);
    printf("x after increment: %d\n", x);

    // Call doubleValue function
    doubleValue(&x);
    printf("x after doubling: %d\n", x);

    // Call swap function
    swap(&x, &y);
    printf("x after swap: %d\n", x);
    printf("y after swap: %d\n", y);

    return 0;
}

