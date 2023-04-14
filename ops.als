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

fun di(X: set univ) : X->X {
	full[X,X] - id[X]
}

fun sup(I,X,Y: set univ, F: I->X->Y) : X->Y {
  { x:X, y:Y | some i: I | x->y in F[i] }
}

fun inf(I,X,Y: set univ, F: I->X->Y) : X->Y {
  { x:X, y:Y | all i: I | x->y in F[i] }
}

fun dual(X,Y: set univ, R: X->Y) : Y->X {
	~(co[X,Y,R])
}

-- Residuals
fun ResL(X,Y,Z: set univ, R: X->Y, S: X->Z) : Y->Z {
	co[Y,Z,(~R).(co[X,Z,S])]
}

fun ResR(X,Y,Z: set univ, R: X->Z, S: Y->Z) : X-> Y {
	co[X,Y,(co[X,Z,R]).(~S)]
}

-- Symmetric Quotient
fun syq(X,Y,Z: set univ, R: X->Y, S: X->Z) : Y->Z {
  co[Y,Z,(~R).(co[X,Z,S])]
	&
	co[Y,Z,(dual[X,Y,R]).S]
}
