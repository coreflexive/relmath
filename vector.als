open ops

-- Domain and codomain
fun dom(X,Y: set univ, R: X->Y) : X->Y {
  R.(full[Y,Y])
}

fun cod(X,Y: set univ, R: X->Y) : Y->X {
  ~R.(full[X,X])
}


-- Uni/multivalent Part
fun upa(X,Y: set univ, R: X->Y) : X->Y {
  R & co[X,Y,R.(di[Y])]
}

fun mup(X,Y: set univ, R: X->Y) : X->Y {
  R & R.(di[Y])
}


-- Uni/mutlivalent Zone
fun uvz(X,Y: set univ, R: X->Y) : X->Y {
  dom[X,Y,upa[X,Y,R]]
}

fun mvz(X,Y: set univ, R: X->Y) : X->Y {
  dom[X,Y,mup[X,Y,R]]
}
