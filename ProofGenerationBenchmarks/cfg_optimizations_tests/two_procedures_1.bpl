procedure p() {
    var y: int;

    y := 1;
    
    y := y+1;
    goto l1;

    l1:
    y := y+2;
    goto l2;

    l2:
    y := y+3;
    goto l3,l4;

    l3:
      assert y >= 0;
    
    l4:
      assert y >= 0;
}

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