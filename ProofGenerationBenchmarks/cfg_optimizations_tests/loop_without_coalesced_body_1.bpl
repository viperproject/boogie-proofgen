procedure p() {
    var y: int;
    var i: int;
    i := 0;
    goto l1;

    l1:
    y := 0;
    goto l2;


    l2:
    while ( i <= 10 ){
      y := y + i;
      i := i + 1;
    }


    i := i + 1;
    assume true;

}