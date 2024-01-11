void swapskip(int* x, int* y)
{
}
void swap(int* x, int* y)
{
    /*int a2 = *x;
    int b2 = *y;
    *y = a2;
    *x = b2; */
}
void swapmath(int *x, int *y)
{
    int a2 = *x;
    int b2 = *y;
    *y = a2 + 1;
}
void swapif(int *x, int *y)
{
    int a2 = *x;
    int b2 = *y;
    if (a2 < b2)
    {
        *y = a2;
        *x = b2; 
    }
    else
    {
        *x = b2;
    }
}