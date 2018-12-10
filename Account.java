public class Account {
  private /*@ spec_public @*/ int bal;
  //@ public invariant bal >= 0;
  /*@ requires amt >= 0;
    @ assignable bal;
    @ ensures bal == amt; @*/
  public Account(int amt) {
    bal = amt;
  }
  /*@ ensures bal == acc.bal; @*/
  public Account(Account acc) {
    bal = acc.balance();
  }

  public void transfer(int amt, Account acc) {
    acc.withdraw(amt);
    deposit(amt);
  }


  public void withdraw(int amt) {
    bal -= amt;
  }


  public void deposit(int amt) {
    bal += amt;
  }
  //@ ensures \result == bal;
  public /*@ pure @*/ int balance() {
    return bal;
  }
    public static void main(String[] args) {
        Account acc = new Account(100);
        acc.withdraw(200);
        System.out.println("Balance after withdrawal: " + acc.balance());
    }
}
