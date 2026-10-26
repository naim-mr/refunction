int main(void) {
  int x, y, z;
  z = input("car");
  y = input("car");
  x = input("car", 0, 1);          // coup contrôlé par A
  if (3*x-y>=0) {
    if (z -  3*x >= 0) { /* gagne : termine */ }
    else { while (1) {} }
  } else { while (1) {} }
}
