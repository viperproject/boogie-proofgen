procedure procedure_1() {
    var y: int;

    y := 1;
    
    y := y+1;
    goto l1;

    l1:
    y := y+2;
    goto l2, l7;

    l2:
    y := y+3;
    goto l3,l4;

    l3:
      assert y >= 0;
      goto l4, l5;
    
    l4:
      assert y >= 0;
      goto l5;

    l5:
      y:= y+5;
      goto l6;

    l6: 
      assume false;
      goto l7;

    l7:
      y := y + 7;
      assume false;
      goto l8;

    l8:
      y := y + 8;
}