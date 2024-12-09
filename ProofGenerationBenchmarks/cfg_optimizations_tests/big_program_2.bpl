procedure p() {
    var x: int;
    var y: int;
    var i: int;
    var z: int;
    var a: int;
    var b: int;
    var c: int;
    x := 0;
    z := 0;

    b1:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto l1;
      
        l1:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b1;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;

    b2:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto l2;
      
        l2:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b2;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;

    b3:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto l3;
      
        l3:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b3;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;



    i := 0;
    y := 0;
    b4:

    while ( i <= 10 ){
      y := y + i;
      goto b5;
      
      b5:
      i := i + 1;
    }

    i := i + 1;
    if (y <= 1000){
      goto b4;
    }
    else{
      goto b6;
    }

    b6:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b7;

    b7:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b8;

    b8:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b9;

    b9:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;

    b10:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto b11;
      
        b11:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b10;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;

    b12:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto b13;
      
        b13:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b12;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;

    b14:
    x := x + 1;
    z := z + 1;
    i := 0;
    y := 0;
    while (y<=1000){
      i := 0;
      while ( i <= 10 ){
        x := x + 1;
        z := z + 1;
        y := y + i;
        goto b15;
      
        b15:
        x := x + 1;
        z := z + 1;
        i := i + 1;
      }
    }
    i := i + 1;
    if (y <= 1000){
      goto b14;
    }

    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;



    i := 0;
    y := 0;
    b16:

    while ( i <= 10 ){
      y := y + i;
      goto b17;
      
      b17:
      i := i + 1;
    }

    i := i + 1;
    if (y <= 1000){
      goto b16;
    }
    else{
      goto b18;
    }

    b18:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b19;

    b19:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b20;

    b20:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;
    goto b21;

    b21:
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    x := x + 1;
    z := z + 1;
    i := i + 1;


    
    
    

    




}