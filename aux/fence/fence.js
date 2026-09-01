
var njs = require("./numeric.js");

var S = 0.5;

function cutplane(P, _mf) {
  _mf = ((typeof _mf === "undefined") ? 1.25 : _mf);
  let Pe = [];

  let p_com = [0,0,0];

  for (let i=0; i<P.length; i++) {
    let cur = i;
    let nxt = (i+1)%P.length;
    console.log(P[cur][0], P[cur][1], P[cur][2]);
    console.log(P[nxt][0], P[nxt][1], P[nxt][2]);
    console.log("\n\n");

    njs.addeq(p_com, P[i]);
  }

  p_com[0] /= P.length;
  p_com[1] /= P.length;
  p_com[2] /= P.length;


  for (let i=0; i<P.length; i++) {
    Pe.push( njs.add( njs.mul(_mf, njs.sub( P[i], p_com )), p_com ) );
  }
  
  for (let i=0; i<Pe.length; i++) {
    let cur = i;
    let nxt = (i+1)%Pe.length;
    console.log(Pe[cur][0], Pe[cur][1], Pe[cur][2]);
    console.log(Pe[nxt][0], Pe[nxt][1], Pe[nxt][2]);
    console.log("\n\n");
  }


}

function fe() {

  let idir_Tv = [
    [ [ 0, 1, 0], [ 0, 0, 1] ],
    [ [ 0,-1, 0], [ 0, 0,-1] ],

    [ [ 1, 0, 0], [ 0, 0, 1] ],
    [ [-1, 0, 0], [ 0, 0,-1] ],

    [ [ 1, 0, 0], [ 0, 1, 0] ],
    [ [-1, 0, 0], [ 0,-1, 0] ],
  ];

  let idir_v = [ [1,0,0], [-1,0,0], [0,1,0], [0,-1,0], [0,0,1], [0,0,-1] ];

  // idir
  //
  let face_edge = [
    [ [ 1, -1, -1], [ 1,  1, -1], [ 1,  1,  1], [ 1, -1,  1] ],
    [ [-1, -1,  1], [-1,  1,  1], [-1,  1, -1], [-1, -1, -1] ],

    [ [ 1,  1, -1], [-1,  1, -1], [-1,  1,  1], [ 1,  1,  1] ],
    [ [ 1, -1,  1], [-1, -1,  1], [-1, -1, -1], [ 1, -1, -1] ],

    [ [-1, -1,  1], [-1,  1,  1], [ 1,  1,  1], [ 1, -1,  1] ],
    [ [ 1, -1, -1], [ 1,  1, -1], [-1,  1, -1], [-1, -1, -1] ]
  ];

  let face_patch = [];

  for (let idir=0; idir<face_edge.length; idir++) {
    for (let i=0; i<face_edge[idir].length; i++) {
      for (let j=0; j<face_edge[idir][i].length; j++) {
        face_edge[idir][i][j] *= S;
      }
    }
  }

  let fudge = 1/50;
  fudge = 0;

  for (let idir=0; idir<face_edge.length; idir++) {
    let du = idir_Tv[idir][0];
    let dv = idir_Tv[idir][1];

    let _fe = [];
    for (let i=0; i<face_edge[idir].length; i++) {
      _fe.push( njs.sub( face_edge[idir][i], njs.mul(S, idir_v[idir]) ) );
    }

    for (let iu=-1; iu<1; iu++) {
      for (let iv=-1; iv<1; iv++) {

        let a = njs.mul( (iu+0.5)/2, idir_Tv[idir][0] );
        let b = njs.mul( (iv+0.5)/2, idir_Tv[idir][1] );

        let _n = face_edge[idir].length;
        for (let i=0; i<=_n; i++) {
          let w = njs.add( njs.mul( 1/2, _fe[i%_n] ), a, b, njs.mul(S, idir_v[idir]) );

          console.log(w[0] + fudge, w[1] + fudge, w[2] + fudge);
        }
        console.log("\n\n");
      }
    }
  }

  for (let idir=0; idir<face_edge.length; idir++) {
    for (let i=0; i<face_edge[idir].length; i++) {
      let nxt = (i+1)%(face_edge[idir].length);
      console.log( face_edge[idir][i][0], face_edge[idir][i][1], face_edge[idir][i][2] );
      console.log( face_edge[idir][nxt][0], face_edge[idir][nxt][1], face_edge[idir][nxt][2] );
      console.log("\n\n");
      
    }
  }

  let p0 = [ 0.25, -0.5, 0.5 ];
  let p1 = [ -0.5, 0.15, 0.5 ];
  let p2 = [ -0.5, -0.45, -0.5 ];
  let p3 = [ -0.15, -0.5, -0.5 ];
  cutplane([p0, p1, p2, p3],1.25);

  let q0 = [ -.12, 0.5 , 0.5 ];
  let q1 = [ 0.5, 0.5 , 0.25 ];
  let q2 = [ 0.5, -.15, 0.5 ];
  cutplane([q0,q1,q2], 1.6);

  /*
  let Pe = [];

  let p_com = [0,0,0];

  for (let i=0; i<P.length; i++) {
    let cur = i;
    let nxt = (i+1)%P.length;
    console.log(P[cur][0], P[cur][1], P[cur][2]);
    console.log(P[nxt][0], P[nxt][1], P[nxt][2]);
    console.log("\n\n");

    njs.addeq(p_com, P[i]);
  }

  p_com[0] /= P.length;
  p_com[1] /= P.length;
  p_com[2] /= P.length;


  for (let i=0; i<P.length; i++) {
    Pe.push( njs.add( njs.mul(1.25, njs.sub( P[i], p_com )), p_com ) );
  }
  
  for (let i=0; i<Pe.length; i++) {
    let cur = i;
    let nxt = (i+1)%Pe.length;
    console.log(Pe[cur][0], Pe[cur][1], Pe[cur][2]);
    console.log(Pe[nxt][0], Pe[nxt][1], Pe[nxt][2]);
    console.log("\n\n");
  }
  */


}

fe();


function ok() {
  var fence = [
    [ [ -1, -1, -1 ], [  1, -1, -1 ] ],
    [ [ -1, -1, -1 ], [ -1,  1, -1 ] ],
    [ [ -1, -1, -1 ], [ -1, -1,  1 ] ],

    [ [  1,  1,  1 ], [ -1,  1,  1 ] ],
    [ [  1,  1,  1 ], [  1, -1,  1 ] ],
    [ [  1,  1,  1 ], [  1,  1, -1 ] ]
  ];

  for (let i=0; i<fence.length; i++) {
    for (let j=0; j<fence[i].length; j++) {
      for (let k=0; k<3; k++) {
        fence[i][j][k] *= S;
      }
    }
  }


  let p0 = [ 0.25, 0.5, -0.5 ];
  let p1 = [ -0.5, 0.5, 0.25 ];
  let p2 = [ 0.35, -0.5, -0.5 ];


  for (let i=0; i<fence.length; i++) {
    let a = fence[i][0];
    let b = fence[i][1];
    console.log(a[0], a[1], a[2]);
    console.log(b[0], b[1], b[2]);
    console.log("\n\n");
  }

  console.log(p0[0], p0[1], p0[2]);
  console.log(p1[0], p1[1], p1[2]);
  console.log("\n\n");

  console.log(p1[0], p1[1], p1[2]);
  console.log(p2[0], p2[1], p2[2]);
  console.log("\n\n");


  console.log(p0[0], p0[1], p0[2]);
  console.log(p2[0], p2[1], p2[2]);
  console.log("\n\n");


}
