/*Corresponds to sepcification: {x |-> a * y |-> b}void swapadd(int* x, int* y){ x |-> (b + 1) * y |-> (a + 2)}*/
void swapadd(int *x, int *y)
{
    int a2 = *x;
    int b2 = *y;
    *x = b2 + 1;
    *y = a2 + 2;
}