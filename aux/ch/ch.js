

var njs = require("./numeric.js");

function gp_pprint(P) {
  for (let i=0; i<P.length; i++) {
    console.log(P[i][0], P[i][1], P[i][2], "\n\n");
  }
}

var p = [0,0,0];

let Qn = 20;
let Q = [];
for (let i=0; i<Qn; i++) {
  Q.push( [ (Math.random() - 0.5), (Math.random() - 0.5), (Math.random() - 0.5) ] );
}

console.log(p[0], p[1], p[2], "\n\n");
gp_pprint(Q);

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
for (let i=0; i<candidate_pnt.length; i++) {

  for (let j=0; j<Nq.length; j++) {


  }

}
