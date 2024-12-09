procedure procedure_test() {
    var y: int;
    var i: int;

    l1:
    i := 0;
    y := 0;
    goto l2;
    

    l2:
    i := i+1;


    l3:
    while ( i <= 10 ){
      i := i + 1;
      goto l4, l2;

      l4:
      y := y + i;
    }

    assert true;


    l5:
    i := i + 10;
    goto l6;


    l6: 
    i := i + 10;
    assume false;
    goto l7;

    l7:
    i := i + 1;
}