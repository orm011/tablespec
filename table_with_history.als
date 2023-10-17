sig Row {}

sig Snapshot {
	data : set Row
}

one sig Table {
	var data : set Row,
	var history : seq Snapshot
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

pred stutter[t:Table]{
	t.data' = t.data
	t.history' = t.history
}

pred init[t : Table] {
	no t.data
	t.history.isEmpty
}


pred update_history[t : Table ]{
	some s : Snapshot {
		 	s.data = t.data
			t.history' = t.history.add[s]
	}
}

pred step[t : Table] {
	some r : Row  {
		( (insert[t, r] or delete[t,r]) and update_history[t] )
	}
}


fact "init" {
	all t : Table { init[t] }
}

example1 : run {
		always some t : Table  {step[t] or stutter[t]}
		eventually some t : Table {#t.data > 3}
		eventually some t : Table, r : Row  { delete[t,r] }
}
for 5 
