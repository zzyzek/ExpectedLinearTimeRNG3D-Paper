
var njs = require("./numeric.js");

var grid_n = 3;
var grid_cell_size = [ 1/grid_n, 1/grid_n ];
var win_center = [0.5,0.5];

var ds = njs.mul( 1/(2*grid_n), grid_cell_size );

var p0 = njs.sub(
          njs.add( win_center,
                   njs.mul( 0.5, grid_cell_size ) ),
          ds );
var Q = [];
Q.push( njs.sub( p0, [ ds[0], ds[1]/2 ] ) );
Q.push( njs.add( p0, [ 0, 3*ds[1] ] ) );

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

for (let i=0; i<=grid_n; i++) {
  console.log("##", i/grid_n, 0);
  console.log("##", i/grid_n, 1);
  console.log("##\n#\n");
}

for (let i=0; i<=grid_n; i++) {
  console.log("##", 0, i/grid_n);
  console.log("##", 1, i/grid_n);
  console.log("##\n#\n");
}


//----
//----
//----


console.log(p0[0], p0[1], "\n\n");

for (let i=0; i<Q.length; i++) {
  console.log(Q[i][0],  Q[i][1], "\n\n");
}


