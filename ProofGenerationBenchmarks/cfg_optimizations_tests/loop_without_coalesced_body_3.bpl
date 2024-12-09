procedure p() {
    var y: int;
    var i: int;

    l1:
    i := 0;
    y := 0;
    

    l2:
    i := i+1;


    l3:
    while ( i <= 10 ){
      goto l2,l4;
      l4:
      i := i + 1;
      y := y + i;
    }

    assert true;
}