procedure procedure_1() {
    var y: int;
    var i: int;

    i := 0;
    y := 0;

    goto l1, l2;

    l1:
    i := i + 5;
    goto l3;

    l3:
    i := i + 1;
    y := y + i;
    goto l4;

    l4:
    y := y + 1;
    goto l2;


    l2:
    if (i>y){
      y := i;
      goto l5;

      l5:
      assume false;
    }
    assume false;
    i := i + 1;
    y := i + 1;
    
}