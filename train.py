from openai import OpenAI
from subprocess import call
client = OpenAI()
messages=[
   {"role": "system", "content": "Translate separation logic specification to C program. Only include the C program in the content. No need to include a main function in the translated C program, and other English description"},
    {"role": "user", "content": "{x |-> a * y |-> b}void swapnum(int* x, int* y){ x |-> b * y |-> a }"},
    {"role": "assistant", "content": "void swapnum(int* x, int* y) {  int temp = *x; *x = *y; *y = temp;}"}
  ]

while True:
    uinp = input("Please enter your specification in separation logic format: (Pre-condition)function name(Post-condition), otherwise Quit: ")
    if uinp == 'Quit':
      break
    messages.append({"role":"user","content":uinp})
    #one-shot experience - just give the prog. doesnt work
    completion = client.chat.completions.create(
      model="gpt-3.5-turbo",
      seed=1235,
      messages=messages
    )

    cprog = completion.choices[0].message.content
    #print(cprog)
    fcprog = open("proggen.c","w")
    fcprog.write(cprog)
    fcprog.close()
    #call clightgen
    #call(["clightgen", "-normalize","swapprog.c"])
