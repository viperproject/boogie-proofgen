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