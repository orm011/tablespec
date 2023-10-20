sig Row {}

// sig Snapshot {
// 	data : set Row
// }

// sig Table {
// 	var data : set Row,
// 	var history : seq Snapshot
// }

// pred insert[ t: Table, r : Row] {
// 	r not in t.data
// 	t.data'  = t.data + r
// }

// pred delete[t: Table, r : Row] {
// 	r in t.data
// 	t.data' = t.data - r
// }

// pred update[t: Table, r1 : Row, r2 : Row] {
// 	r1 in t.data
// 	r2 not in t.data
// 	t.data' = t.data - r1 + r2
// }

// pred noop[t : Table] {
// 	t.data' = t.data
// 	t.history' = t.history
// }

// pred init[t : Table] {
// 	no t.data
// 	t.history.isEmpty
// }

// fun query [t : Table ] : Snapshot {
// 	{ s : Snapshot |  s.data = t.data}
// }

// pred update_history[t : Table ] 
// {
// 	some s : Snapshot {
// 		 s.data = t.data 
// 		 t.history' = t.history.add[s]
// 	}
// }

// pred step[t : Table] {
// 	some r : Row  {
// 		( (insert[t, r] or delete[t,r]) and update_history[t] )
// 	}
// }

// fact "init" {
// 	all t : Table { init[t] }
// }

// fact {
// 	#Table = 1
// }

// example1 : run {
// 		always some t : Table { step[t] or noop[t] }
// 		eventually some t : Table { #t.data > 3 }
// 		eventually some t : Table, r : Row  { delete[t,r] }
// }
// for 5 


// vmin vmax implementation.
// will check that it behaves similar to simply keeping snapshot around

sig VersionedRow {
	data : Row,
	vmin : Int,
	vmax : lone Int, // it can be null if latest version.
}

enum Oper { Insert, Delete}
sig LogEntry {
	// insert, delete, update
	oper : Oper,
	row : Row
}

one sig VersionedTable {
	var entries : set VersionedRow,
	var version : one Int,
	var log : seq LogEntry
}

pred init[t : VersionedTable] {
	no t.entries
	t.version = 0
	t.log.isEmpty
}

fact "extensionality" { 
	all disj vr1, vr2 : VersionedRow | not (vr1.data = vr2.data and vr1.vmin = vr2.vmin and vr1.vmax = vr2.vmax)
}

pred insert[t : VersionedTable, r : Row] {
	r not in { r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
	//r not in { r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
	t.entries' = t.entries + { vr : VersionedRow | vr.data = r and vr.vmin = t.version' and no vr.vmax }
	t.version' = add[t.version,1]
	t.log' = t.log.add[{ le : LogEntry | le.row = r and le.oper = Insert }]
}

pred delete[t: VersionedTable, r : Row] {
	r in { r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
	t.entries' = t.entries - { vr : VersionedRow | vr.data = r and no vr.vmax }
					+ { vr : VersionedRow | vr.data = r and vr.vmax = t.version' }
	t.version' = add[t.version,1]
	t.log' = t.log.add[{ le : LogEntry | le.row = r and le.oper = Delete }]
}

pred noop[t : VersionedTable] {
	t.entries' = t.entries
	t.version' = t.version
	t.log' = t.log
}

pred step[t : VersionedTable] {
	one r : Row  { 
		insert[t,r] or delete[t,r]
	}
}

fact "init2" {
	all t : VersionedTable { init[t] }
	always all t : VersionedTable { step[t] or noop[t] }
}

example2 : run {
		eventually some t : VersionedTable { #t.entries > 2 }
		eventually some t : VersionedTable, r : Row { delete[t, r] }
}


// why are multiple things inserted at the same time?

// pred update[t: Table, r1 : Row, r2 : Row] {
// 	r1 in t.data
// 	r2 not in t.data
// 	t.data' = t.data - r1 + r2
// }

// pred noop[t : Table] {
// 	t.data' = t.data
// 	t.history' = t.history
// }



