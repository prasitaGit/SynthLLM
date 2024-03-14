//returns the index
//i,jstarts with 0,1
//-1 if no repeated nums exist
int findFirstRepeatedNum(int a[], unsigned i, unsigned j, unsigned length)
{
    if(i == length - 1)
    {
        return -1;
    }
    else if(j == length)
    {
        return findFirstRepeatedNum(a, i + 1, i + 2, length);
    }
    else if(a[i] == a[j])
    {
        return i;
    }
    else
    {
        return findFirstRepeatedNum(a, i, j + 1, length);
    }
    
}