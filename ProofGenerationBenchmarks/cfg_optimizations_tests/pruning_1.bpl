procedure p() {
    var y: int;
    var i: int;

    l1:
    i := 0;
    y := 0;
    goto l2,l5;
    

    l2:
    i := i+1;
    goto l3;

    l3:
    assume false;
    goto l4;

    l4:
    i := i + 1;
    goto l6;

    l5:
    assume false;
    goto l6;


    l6:
    assert true;
}