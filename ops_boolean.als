fun co(X,Y: set univ, R: X->Y) : X->Y {
	X->Y - R
}

fun null(X,Y: set univ) : X->Y {
  none->none
}

fun full(X,Y: set univ) : X->Y {
	X->Y
}

fun id(X: set univ) : X->X {
	iden:>X
}

fun sup(I,X,Y: set univ, F: I->X->Y) : X->Y {
  { x:X, y:Y | some i: I | x->y in F[i] }
}

fun inf(I,X,Y: set univ, F: I->X->Y) : X->Y {
  { x:X, y:Y | all i: I | x->y in F[i] }
}
