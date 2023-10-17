sig Row {}
one sig Table {
	var data : set Row
}

pred insert[ t: Table, r : Row] {
	r not in t.data
	t.data'  = t.data + r
}

pred delete[t: Table, r : Row]{
	r in t.data
	t.data' = t.data - r
}

pred update[t: Table, r1 : Row, r2 : Row]{
	r1 in t.data
	r2 not in t.data
	t.data' = t.data - r1 + r2
}

fact "init" {
	no data
}

run {
	always {{some t: Table, r : Row { insert[t, r] or delete[t, r]  }} 
			or 
		 	{some t: Table, r1, r2 : Row { update[t,r1,r2] }}}
	eventually some t: Table, r1, r2 : Row { update[t,r1,r2] }
} 
