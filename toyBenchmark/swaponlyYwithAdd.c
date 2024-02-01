/*Corresponds to sepcification: {x |-> a * y |-> b}void swaponlyYwithAdd(int* x, int* y){ x |-> a * y |-> (a + 3)}*/
void swaponlyYwithAdd(int *x, int *y)
{
    *y = *x + 3;
}