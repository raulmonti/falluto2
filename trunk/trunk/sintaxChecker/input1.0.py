MODULE M0 ()
MODULE M1(v1,v2)
MODULE M2(v1,v2;a1,a2)
MODULE M3() VAR FAULT INIT TRANS
MODULE M4(v1;a1)
	VAR
	TRANS
MODULE M5(v1;a1)
	VAR
		a:bool
		b:10..25
		c:{a,b,c,123,44,_ff}
	FAULT
		f1:TRUE:next(a)=FALSE
		f2:a:next(b)=0
		f2:b<20:next(c)=a
	INIT
		a=TRUE & b=10 & c={a,b}
	TRANS
		[t1]:a=FALSE:next(a)=TRUE&next(b)={a,g}

MODULE M6 (v1)
	VAR v:0..1
	FAULT f::next(r)=TRUE
	INIT v=0
	TRANS []:TRUE:next(v)={a,v} <BIZ (x,z)>
