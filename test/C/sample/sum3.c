#include <stdio.h>

int main()
{
    int n, i, sum;
    void A(int *x, int *y);

    printf("Enter a positive number: ");
    scanf("%d", &n);

    sum = 0;
    i = 1;
    while (i <= n)
    {
     A(&sum,&i);
    }

    printf ("sum = %d\n", sum);
    printf ("i = %d\n", i);
    return 0;
}

void A(int *x, int *y)
{
    void add(int *a, int *b);
    void inc(int *z);
    add(x,y);
    inc(y);
}

void add(int *a, int *b)
{
    *a = *a + *b;
//    return(a);
}

void inc(int *z)
{
//    int add(int a, int b);
    int tmp = 1;
    add(z,&tmp);
}


