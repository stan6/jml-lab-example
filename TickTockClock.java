
public class TickTockClock {

protected int hour; 
protected int minute; 
protected int second; 

 //@ assignable this.*;
 //@ ensures getHour() == 12 && getMinute() == 0 && getSecond() == 0;
 public /*  @ pure @*/ TickTockClock() {
 hour = 12; minute = 0; second = 0;
 }

 
 public /*@ pure @*/ int getHour() { return hour; }

 public /*@ pure @*/ int getMinute() { return minute; }

 public /*@ pure @*/ int getSecond() { return second; }


 public void tick() {
 second++;
 if (second == 60) { second = 0; minute++; }
 if (minute == 60) { minute = 0; hour++; }
 if (hour == 24) { hour = 0; }
 }
}
