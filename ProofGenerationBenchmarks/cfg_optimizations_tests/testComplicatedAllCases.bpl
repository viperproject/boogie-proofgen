procedure p() {
    var y: int;
    var i: int;

    l1:
    i := 0;
    y := 0;
    goto l3, l5;
    

    l2:
    i := i+1;


    l3:
    while ( i <= 10 ){
      goto l2,l4, l6, l3;
      l4:
      i := i + 1;
      y := y + i;
    }

    assert y >= 0;


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