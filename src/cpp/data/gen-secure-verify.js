
var fs = require("fs");
var njs = require("./numeric.js");

var grid_n = 3;
var grid_cell_size = [ 1/grid_n, 1/grid_n ];
var win_center = [0.5,0.5];

var ds = njs.mul( 1/(8*grid_n), grid_cell_size );

var p0 = njs.sub(
          njs.add( win_center,
                   njs.mul( 0.5, grid_cell_size ) ),
          ds );

var Q = [];
Q.push( njs.sub( p0, [ 4.4*ds[0], 3.1*ds[1]/2 ] ) );
//Q.push( njs.add( p0, [-0.5*ds[0], 1.5*ds[1] ] ) );
Q.push( njs.add( p0, [-4.1*ds[0], 0.3*ds[1] ] ) );
Q.push( njs.add( p0, [ ds[0]/256, ds[1]/32] ) );

let dt = (1/(4*grid_n));

//let fudge = 0.0051;

let dv = [-dt,dt/8];
p0 = njs.add( p0, [dv[0], dv[1] ]);
Q[0] = njs.add( Q[0], [dv[0], dv[1] ] );
Q[1] = njs.add( Q[1], [dv[0], dv[1] ] );
Q[2] = njs.add( Q[2], [dv[0], dv[1] ] );


var _c = grid_cell_size;

Q.push( njs.add( win_center, [ -_c[0] - ds[0], _c[1] - ds[1] ] ) );
Q.push( njs.add( win_center, [ -_c[0] - ds[0],    0  - ds[1] ] ) );
Q.push( njs.add( win_center, [ -_c[0] - ds[0], _c[1] + ds[1] ] ) );

Q.push( njs.add( win_center, [  _c[0] - ds[0], _c[1] - ds[1] ] ) );
Q.push( njs.add( win_center, [  _c[0] + ds[0],    0  - ds[1] ] ) );
Q.push( njs.add( win_center, [  _c[0] - ds[0], _c[1] + ds[1] ] ) );

Q.push( njs.add( win_center, [     0  + ds[0], -_c[1] - ds[1] ] ) );



//----
//----
//----

let lines_lines = [];

let dq2 = njs.sub( Q[2], p0 );
dq2 = njs.mul( 1/njs.norm2(dq2), dq2 );
let dq2T = [ -dq2[1], dq2[0] ];

for (let dt = -1.0; dt <= 1.0; dt += (1/32)) {
  let v = njs.add(Q[2], njs.mul( dt, dq2T ));
  lines_lines.push( v[0].toString() + " " + v[1].toString() );
}
lines_lines.push("\n\n");

let dq0 = njs.sub( Q[0], p0 );
dq0 = njs.mul( 1/njs.norm2(dq0), dq0 );
let dq0T = [ -dq0[1], dq0[0] ];

for (let dt = -1.0; dt <= 1.0; dt += (1/32)) {
  let v = njs.add(Q[0], njs.mul( dt, dq0T ));
  lines_lines.push( v[0].toString() + " " + v[1].toString() );
}
lines_lines.push("\n\n");

fs.writeFileSync( "lines.gp", lines_lines.join("\n"));



//----
//----
//----

let circle_lines = [];

let r_p0q0 = njs.norm2( njs.sub(p0, Q[0]) );
let r_p0q1 = njs.norm2( njs.sub(p0, Q[1]) );
let r_p0q2 = njs.norm2( njs.sub(p0, Q[2]) );

let r_p0qi = [
 njs.norm2( njs.sub(p0, Q[0]) ),
 njs.norm2( njs.sub(p0, Q[1]) ),
 njs.norm2( njs.sub(p0, Q[2]) )
];

let cseg = 1024;

for (let iq=0; iq<3; iq++) {

  for (let i=0; i<=cseg; i++) {
    let theta = 2*Math.PI*i/cseg;
    let v = njs.add( p0, njs.mul( r_p0qi[iq], [ Math.cos(theta), Math.sin(theta) ] ) )
    circle_lines.push( v[0].toString() + " " + v[1].toString() );
  }
  circle_lines.push("\n\n\n");

  for (let i=0; i<=cseg; i++) {
    let theta = 2*Math.PI*i/cseg;
    let v = njs.add( Q[iq], njs.mul( r_p0qi[iq], [ Math.cos(theta), Math.sin(theta) ] ) )
    circle_lines.push( v[0].toString() + " " + v[1].toString() );
  }
  circle_lines.push("\n\n\n");
}

/*
for (let i=0; i<=32; i++) {
  let theta = 2*Math.PI*i/32;
  let v = njs.add( p0, njs.mul( r_p0q1, [ Math.cos(theta), Math.sin(theta) ] ) )
  circle_lines.push( v[0].toString() + " " + v[1].toString() );
}
circle_lines.push("\n\n\n");

for (let i=0; i<=32; i++) {
  let theta = 2*Math.PI*i/32;
  let v = njs.add( Q[1], njs.mul( r_p0q1, [ Math.cos(theta), Math.sin(theta) ] ) )
  circle_lines.push( v[0].toString() + " " + v[1].toString() );
}
circle_lines.push("\n\n\n");
*/

fs.writeFileSync("circles.gp", circle_lines.join("\n"));

//----
//----
//----

let grid_lines = [];
for (let i=0; i<=grid_n; i++) {

  for (let j=0; j<grid_n; j++) {
    grid_lines.push( (i/grid_n).toString() + " " + (j/grid_n).toString() );
    grid_lines.push( (i/grid_n).toString() + " " + ((j+1)/grid_n).toString() );
    grid_lines.push("\n\n");
  }
  console.log("##", i/grid_n, 0);
  console.log("##", i/grid_n, 1);
  console.log("##\n#\n");
}

for (let i=0; i<=grid_n; i++) {
  for (let j=0; j<grid_n; j++) {
    grid_lines.push( (j/grid_n).toString() + " " + (i/grid_n).toString() );
    grid_lines.push( ((j+1)/grid_n).toString() + " " + (i/grid_n).toString() );
    grid_lines.push("\n\n");
  }
  console.log("##", 0, i/grid_n);
  console.log("##", 1, i/grid_n);
  console.log("##\n#\n");
}

fs.writeFileSync("grid.gp", grid_lines.join("\n"));


//---
//---
//---

let fp_lines = [];
for (let i=0; i<=(2*grid_n); i++) {
  for (let j=0; j<=(2*grid_n); j++) {
    console.log("###", i/(2*grid_n), j/(2*grid_n), "\n###\n###\n");
    fp_lines.push( (i/(2*grid_n)).toString() + " " + (j/(2*grid_n)).toString() + "\n\n\n");
  }
}

fs.writeFileSync("fp.gp", fp_lines.join("\n"));

//----
//----
//----


console.log(p0[0], p0[1], "\n\n");

for (let i=0; i<Q.length; i++) {
  console.log(Q[i][0],  Q[i][1], "\n\n");
}


