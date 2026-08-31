
var S = 0.5;


function fe() {

  // idir
  //
  let face_edge = [
    [ [ 1, -1, -1], [ 1,  1, -1], [ 1,  1,  1], [ 1, -1,  1] ],
    [ [-1, -1,  1], [-1,  1,  1], [-1,  1, -1], [-1, -1, -1] ],

    [ [ 1,  1, -1], [-1,  1, -1], [-1,  1,  1], [ 1,  1,  1] ],
    [ [ 1, -1,  1], [-1, -1,  1], [-1, -1, -1], [ 1, -1, -1] ],

    [ [-1, -1,  1], [-1,  1,  1], [ 1,  1,  1], [ 1, -1,  1] ],
    [ [ 1, -1, -1], [ 1,  1, -1], [-1,  1, -1], [-1, -1, -1] ]
  ]

  for (let idir=0; idir<face_edge.length; idir++) {
    for (let i=0; i<face_edge[idir].length; i++) {
      for (let j=0; j<face_edge[idir][i].length; j++) {
        face_edge[idir][i][j] *= S;
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

}


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
