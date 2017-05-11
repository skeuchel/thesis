interface ArithExp {
  int eval();
  String print();
}
class Lit implements ArithExp {
  public int lit;
  public int eval() { return lit; }
  public String print() { return String.valueOf(lit); }
}
class Add implements ArithExp {
  public ArithExp e1, e2;
  public int eval() { return e1.eval() + e2.eval(); }
  public String print() {
    return e1.print().concat("+").concat(e2.print());
  }
}
class Mul implements ArithExp {
  public ArithExp e1, e2;
  public int eval() { return e1.eval() + e2.eval(); }
  public String print() {
    return e1.print().concat("*").concat(e2.print());
  }
}
