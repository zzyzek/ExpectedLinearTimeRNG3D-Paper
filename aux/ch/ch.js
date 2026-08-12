

var njs = require("./numeric.js");

var CH = require("convex-hull");

var _EPS = (1.0 / (1024.0*1024.0));

function gp_pprint(P) {
  for (let i=0; i<P.length; i++) {
    console.log(P[i][0], P[i][1], P[i][2], "\n\n");
  }
}

function jsonf_pprint(P, name) {

  console.log("  \"" + name + "\":[");

  for (let i=0; i<P.length; i++) {
    console.log("    [", P[i][0], ",", P[i][1], ",", P[i][2], "]", (i < (P.length-1)) ? "," : "" );
  }

  console.log("  ]");
}

var p = [0,0,0];

let Qn = 40;
let Q = [];
for (let i=0; i<Qn; i++) {
  Q.push( [ (Math.random() - 0.5), (Math.random() - 0.5), (Math.random() - 0.5) ] );
}

console.log("{");
console.log("  \"n\":", Qn, ",");

console.log("  \"p\": [", p[0], ",", p[1], ",", p[2], "],");
//gp_pprint(Q);
jsonf_pprint(Q, "Q");
console.log(",");

let Dq = [];
let Nq = [];
for (let i=0; i<Q.length; i++) {
  let q = Q[i];

  let nqp = njs.sub( q, p );

  Dq.push( nqp);
  Nq.push( njs.mul( 1/njs.norm2(nqp), nqp ) );

  //console.log(p[0], p[1], p[2]);
  //console.log(nqp[0], nqp[1], nqp[2], "\n\n");
}

let candidate_pnt = [];
for (let i=0; i<Q.length; i++) {
  for (let j=0; j<Q.length; j++) {
    if (i==j) { continue; }
    for (let k=0; k<Q.length; k++) {
      if (j==k) { continue; }
      if (i==k) { continue; }

      let d_u = njs.norm2( Dq[i] );
      let d_v = njs.norm2( Dq[j] );
      let d_w = njs.norm2( Dq[k] );

      let s = njs.solve( [ Nq[i], Nq[j], Nq[k] ], [ d_u, d_v, d_w ] );

      candidate_pnt.push(s);
    }
  }
}

let ch_pnt = [];

// plane equation:
//
// P(u) = (u - p0) . (Np)

let a_plane_idx = [];

for (let i=0; i<candidate_pnt.length; i++) {

  let u = candidate_pnt[i];
  let accept = true;

  let min_idx = -1;

  for (let j=0; j<Nq.length; j++) {
    let s = njs.dot( Nq[j], njs.sub( u, Q[j] ) );
    if (s > _EPS) { accept = false; break; }

    if (s > -_EPS) { min_idx = j; }
  }

  if (accept) {
    ch_pnt.push(u);
    a_plane_idx.push(min_idx);
  }
}

a_plane_idx.sort( function(a,b) { return (a<b) ? -1 : ( (a>b) ? 1 : 0 ) ; } );


let q_plane_idx = [ a_plane_idx[0] ];
for (let i=1; i<a_plane_idx.length; i++) {
  if (a_plane_idx[i] != a_plane_idx[i-1]) { q_plane_idx.push( a_plane_idx[i] ); }
  //console.log("## [", i, "]:", a_plane_idx[i]);
}

console.log("  \"Q_ch_idx\":[", q_plane_idx.join(","), "],");


console.log("  \"Q_ch_v\":[")
for (let i=0; i<q_plane_idx.length; i++) {
  let idx = q_plane_idx[i];
  console.log("    [ [", p[0], ",", p[1], ",", p[2], "], [", Q[idx][0], ",", Q[idx][1], ",", Q[idx][2], "] ]", (i<(q_plane_idx.length-1)) ? "," : "" );
  //console.log(p[0], p[1], p[2]);
  //console.log(Q[idx][0], Q[idx][1], Q[idx][2], "\n\n");
}
console.log("  ],");

var ok = CH( ch_pnt );

console.log("  \"ch_idx\":[");
for (let i=0; i<ok.length; i++) {
  console.log("    [", ok[i][0], ",", ok[i][1], ",", ok[i][2], "]", ( i < (ok.length-1) ) ? "," : "" );
}
console.log("  ],");

console.log("  \"ch_p\":[");
for (let i=0; i<ok.length; i++) {
  console.log( "    [[", ch_pnt[ok[i][0]][0], ",", ch_pnt[ok[i][0]][1], ",", ch_pnt[ok[i][0]][2], "]," );
  console.log( "     [", ch_pnt[ok[i][1]][0], ",", ch_pnt[ok[i][1]][1], ",", ch_pnt[ok[i][1]][2], "]," );
  console.log( "     [", ch_pnt[ok[i][2]][0], ",", ch_pnt[ok[i][2]][1], ",", ch_pnt[ok[i][2]][2], "]]", (i<(ok.length-1)) ? "," : ""  );
}
console.log("  ]");

console.log("}");

//for (let i=0; i<ch_pnt.length; i++) { console.log("#", ch_pnt[i][0], ch_pnt[i][1], ch_pnt[i][2], "\n#\n#"); }
