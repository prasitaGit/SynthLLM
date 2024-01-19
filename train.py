from openai import OpenAI
from subprocess import call
client = OpenAI()

completion = client.chat.completions.create(
  model="gpt-3.5-turbo",
  messages=[
    {"role": "system", "content": "Translate Gallina program to C program. Only include the C program in the content. No need to include a main function in the translated C program, and other English description"},
    {"role": "user", "content": "Convert Definition swapnum (a b : Z) := (b, a) to C with a and b as pointers. Output the C program only, and not any English with it"}
  ]
)
#print(completion)
cprog = completion.choices[0].message.content
#cprog = "void swapnum(int* a, int* b) {  int temp = *a; *a = *b; *b = temp;}"
fcprog = open("swapprog.c","w")
fcprog.write(cprog)
fcprog.close()
#call clightgen
call(["clightgen", "-normalize","swapprog.c"])
