sig Row {}

 sig Snapshot {
 	data : set Row
 }
//
one sig Table {
 	var data : set Row,
 	var history : seq Snapshot
 }

 pred update_history[t : Table ] 
 {
 	one s : Snapshot {
 		 s.data = query[t]
 		 t.history' = t.history.add[s]
 	}
 }
//
 pred insert[ t: Table, r : Row] {
 	r not in t.data
 	t.data'  = t.data + r
	update_history[t] 
 }
//
 pred delete[t: Table, r : Row] {
 	r in t.data
 	t.data' = t.data - r
	update_history[t]
 }

pred insert_correct[t : Table] {
	always all  r : Row { insert[t, r] => after (r in query[t]) }
}

pred delete_correct[t : Table] {
	always all  r : Row { delete[t, r] => after (r not in query[t]) }
}

//
 pred update[t: Table, r1 : Row, r2 : Row] {
 	r1 in t.data
 	r2 not in t.data
 	t.data' = t.data - r1 + r2
 }
//
 pred noop[t : Table] {
 	t.data' = t.data
 	t.history' = t.history
 }
//
 pred init[t : Table] {
 	no t.data
 	t.history.isEmpty
 }

 fun query [t : Table ] : set Row {
 	t.data
 }

fun query_at[t : Table, v : Int ] : set Row {
	t.history[v].data
}
 pred step[t : Table, r : Row] {
 	(insert[t, r] or delete[t,r])
 }


 fact "init" {
 	all t : Table { init[t] }
 }


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

//fact "extensionality" { 
//	all disj vr1, vr2 : VersionedRow | not (vr1.data = vr2.data and vr1.vmin = vr2.vmin and vr1.vmax = vr2.vmax)
//}

fun query[t: VersionedTable]: set Row {
	{ r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
}

fun query_at[vt : VersionedTable, v : Int]: set Row {
	{ r : Row | some vr : vt.entries { vr.data = r and vr.vmin <= v and v < vr.vmax }}
}

pred insert[t : VersionedTable, r : Row] {
	r not in { r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
	one vr : VersionedRow {
		vr.data = r
		vr.vmin = t.version'
		no vr.vmax
		t.entries' = t.entries + vr
	}

	t.version' = add[t.version,1]

	one le : LogEntry {
		le.row = r
		le.oper = Insert 
		t.log' = t.log.add[le]
	}
}

pred delete[t: VersionedTable, r : Row] {
	r in { r : Row | some vr : t.entries { vr.data = r and vr.vmax = none } }
	
	one vrold : t.entries, vrnew : VersionedRow {
		vrold.data = r
		no vrold.vmax

		vrnew.vmin = vrold.vmin
		vrnew.vmax = t.version'
		vrnew.data = r

		t.entries' = t.entries - vrold + vrnew
	}
	t.version' = add[t.version,1]

	one le : LogEntry {
		le.row = r
		le.oper = Delete 
		t.log' = t.log.add[le]
	}
}

pred noop[t : VersionedTable] {
	t.entries' = t.entries
	t.version' = t.version
	t.log' = t.log
}

pred step[vt : VersionedTable, t : Table] {
	(one r : Row  { 
		(insert[vt, r] and insert[t, r]  )
		or 	(delete[vt, r] and delete[t,r])
	})
	or (noop[vt] and noop[t])
}

fact "init2" {
	all t : VersionedTable { init[t] }
}

fact lockstep {
	always all vt : VersionedTable, t: Table { step[vt, t] }
}

assert consistent_table {
	always all vt : VersionedTable, t : Table { query[vt] = query[t] }
//	always all vt : VersionedTable, v : Int {
//		v+1 <= vt.version => query_at[vt,v] = query_at[vt, v+1] 
//	}
}

assert vconsistent {
	always all vr : VersionedRow 
		{ (some vt : VersionedTable | vr in vt.entries ) => (no vr.vmax or vr.vmin < vr.vmax) }
}

pred insert_correct[vt : VersionedTable] {
	always all  r : Row { insert[vt, r] => after (r in query[vt]) }
}

pred delete_correct[t : VersionedTable] {
	always all  r : Row { delete[t, r] => after (r not in query[t]) }
}

//check consistent for 5
//check {all vt : VersionedTable | delete_correct[vt]} for 4
//check {all vt : VersionedTable | delete_correct[vt] }

check_consistent_impl: check consistent_table

//example2 : run {
//		eventually some vt : VersionedTable { #query[vt] >1 }
//}



// tricky mistakes
// 1. no noop => no examples, 
// 2. insert/delete predicate inadvertently too weak:
	// there are instances of things outside the relation
	// a set of things can be empty, seem to need to have the predicate outside.