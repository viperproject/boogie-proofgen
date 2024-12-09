procedure p() {
    var y: int;
    var i: int;
    i := 0;
    y := 0;
    l10:

    while ( i <= 10 ){
      y := y + i;
      goto l1;
      
      l1:
      i := i + 1;
    }

    i := i + 1;
    if (y <= 1000){
      goto l10;
    }
    else{
      goto l2;
    }

    l2:
    i := i + 1;
    goto l3;

    l3:
    i := i + 1;
    goto l4;

    l4:
    assume false;
    goto l5;

    l5:
    i := i + 1;


}