// LICENSE: CC0
//

// inkscape doesn't respect rgba in fill or stroke,
// which is the main method of two.js to do it.
// As a hacky way to make sure it's inkscape compatible,
// the _dl() function will do a post processing step
// of going through each element and converting fill, stroke
// and linearGradient stop components with an rgba value
// to an rgb value with the appropriate 'opacity' portion
// set.
//

// Note on Libertine font,
// Chrome displays it, Inkscape displays it (using 'Linux Libertine O')
// but Firefox shits the bed for some reason.
// It looks like all font-family in `text` elements that have a space don't work.
// I'm tired of fighting with Firefox so I'm moving on as Inkscape works just fine.
//

var njs = numeric;

var g_fig_ctx = {
  "html_id":"fig",
  "two": new Two({fitted:true})
};


//--------------------
//--------------------
//--------------------
//--------------------
// auxiliary functions

// 3d cross product.
//
function cross3(p,q) {
  let c0 = ((p[1]*q[2]) - (p[2]*q[1])),
      c1 = ((p[2]*q[0]) - (p[0]*q[2])),
      c2 = ((p[0]*q[1]) - (p[1]*q[0]));

  return [c0,c1,c2];
}


// euler rotation or olinde rodrigues
// https://en.wikipedia.org/wiki/Rodrigues%27_rotation_formula
//
function rodrigues(v0, _vr, theta) {
  let c = Math.cos(theta);
  let s = Math.sin(theta);
  let v_r = njs.mul( 1 / njs.norm2(_vr), _vr );
  return njs.add(
    njs.mul(c, v0),
    njs.add(
      njs.mul( s, cross3(v_r,v0)),
      njs.mul( (1-c) * njs.dot(v_r, v0), v_r )
    )
  );
}

function toRGBAa(rgba) {
  let va = rgba.split(")")[0].split("(")[1].split(",");
  if (rgba.match( /^rgba\(/ )) { return va; }
  va.push(1);
  return va;
}

function _dl() {
  var ele = document.getElementById("ui_canvas");
  let svg_txt = ele.innerHTML;
  var b = new Blob([ svg_txt ]);
  saveAs(b, "fig.svg");
}

function makeTwoVector(_pnt) {
  let pnt = [];
  for (let ii=0; ii<_pnt.length; ii++) {
    pnt.push( new Two.Vector(_pnt[ii][0], _pnt[ii][1]) );
  }
  return pnt;
}

function makeTwoAnchor(_pnt) {
  let pnt = [];
  for (let ii=0; ii<_pnt.length; ii++) {
    pnt.push( new Two.Anchor(_pnt[ii][0], _pnt[ii][1]) );
  }
  return pnt;
}

// so very hacky
// somehow we managed to shoehorn
// mathjax notation into svg so that it
// can be used by two.js.
// We need to contort ourselves to get the mask
// right so that it gets all the element
//
function mathjax2twojs(_id,x,y,s,s_sub) {
  s = ((typeof s === "undefined") ? 0.02 : s);
  s_sub = ((typeof s_sub === "undefined") ? 0.7 : s_sub);

  let two = g_fig_ctx.two;

  let ele = document.querySelector("#" + _id + " svg");
  let ser = new XMLSerializer();
  let str = ser.serializeToString(ele);

  let parser = new DOMParser();
  let sge = parser.parseFromString(str, "image/svg+xml").documentElement;

  let sgr = two.interpret(sge);

  sgr.position.x = x;
  sgr.position.y = y;
  sgr.scale.x =  s;
  sgr.scale.y = -s;

  debug.push(sgr);

  // rescale subscript HACK
  //
  if (_id.slice(0,2) == "m_") {

    if (true) {

    if (sgr.children.length > 0) {
    if (sgr.children[0].children.length > 0) {
    if (sgr.children[0].children[0].children.length > 1) {
    if (sgr.children[0].children[0].children[1].children.length > 1) {
        sgr.children[0].children[0].children[1].children[1].scale.x = s_sub;
        sgr.children[0].children[0].children[1].children[1].scale.y = s_sub;
    }
    }
    }
    }

    }
  }
  else {

    if (sgr.children.length > 0) {
    if (sgr.children[0].children.length > 0) {
    if (sgr.children[0].children[0].children.length > 0) {
    if (sgr.children[0].children[0].children[0].children.length > 1) {
        sgr.children[0].children[0].children[0].children[1].scale.x = s_sub;
        sgr.children[0].children[0].children[0].children[1].scale.y = s_sub;
    }
    }
    }
    }

  }

  //yep, needed, so we can then get the make element
  //
  two.update();

  let mask = document.getElementById(sgr.mask.id);
  //mask.firstChild.setAttribute("d", "M -10000 -10000 L 10000 -10000 L 10000 10000 L -10000 10000 Z");
  mask.firstChild.setAttribute("d", "M -4000 -4000 L 4000 -4000 L 4000 4000 L -4000 4000 Z");

  two.update();
}

function mklune(p,q, co) {
  let two = g_fig_ctx.two;

  let nseg = 32;

  let dpq = njs.sub(q,p);
  let lpq = njs.norm2(dpq);

  let theta = Math.atan2(dpq[1], dpq[0]);

  let top_pnt = [];

  let pnt = [];
  let rpnt = [];
  for (let i=0; i<nseg; i++) {
    let t = (i/nseg);
    let a = ((theta - (Math.PI/4))*t) + ((1-t)*(theta + (Math.PI/4)));

    a = (-t*Math.PI/3) + ((1-t)*Math.PI/3);

    let c = Math.cos(a);
    let s = Math.sin(a);

    let v = [ (c*dpq[0]) - (s*dpq[1]), (s*dpq[0]) + (c*dpq[1]) ]
    pnt.push( njs.add(p, v) );

    top_pnt.push( pnt[i] );

    let u = [ (-c*dpq[0]) + (s*dpq[1]), (-s*dpq[0]) - (c*dpq[1]) ]
    rpnt.push( njs.add(q, u) );
  }

  for (let i=0; i<rpnt.length; i++) { pnt.push( rpnt[i] ); }

  let aa = makeTwoAnchor(pnt);
  let _path = two.makePath( aa );

  _path.noStroke();

  _path.stroke = "rgb(20,20,20)";
  _path.fill = "#fff1f1"
  _path.opacity = 0.5;

  if (typeof co !== "undefined") {
    _path.fill = co;
  }

}

//--------------------
//--------------------
//--------------------
//--------------------

// There are a few things to keep intact:
//
// * q must not be in the lune of (p,w)
// * cutting plane H _ {p,q} must secure a fence side
// * w must be within the fence
// * u must be outside the fence
//

// todo:
// * hatching for cut plane
// * highlight secured fence face
// * color p as anchor point
// * rescale?
//
function fig_sabotage() {
  let two = g_fig_ctx.two;

  let _f = 20000;

  let ds = (1/100)*_f;
  ds = (1/160)*_f;

  let z = njs.mul(_f, [.655,-.815]);
  let P = njs.mul(_f, [0.659538,-0.811543]);
  let Q = njs.mul(_f, [0.661445,-0.807216]);
  let W = njs.mul(_f, [0.638765,-0.800436]);
  let U = njs.mul(_f, [0.655036,-0.789833]);

  Q[0] -= 10;

  W[0] += 110;
  W[1] -= 170;

  U[0] -= 50;
  U[1] -= 180;

  let com = njs.mul( 1/4, njs.add( njs.add(P,Q), njs.add(W,U) ) );
  com = njs.mul(1/5, njs.add(z, njs.add(P, njs.add(Q, njs.add(U, W)))));
  com = njs.add(com, [-500,-450]);
  P = njs.sub(P, com);
  Q = njs.sub(Q, com);
  W = njs.sub(W, com);
  U = njs.sub(U, com);
  z = njs.sub(z, com);



  //two.makeRectangle( z[0], z[1], 4*ds, 4*ds);
  two.makeRectangle( z[0], z[1], 5*ds, 5*ds);
  two.makeRectangle( z[0], z[1], 3*ds, 3*ds);
  two.makeRectangle( z[0], z[1], ds, ds);

  let _pq = njs.sub(Q,P);
  let _lpq = two.makeLine(P[0], P[1], Q[0], Q[1]);
  _lpq.dashes = [8,8];

  let _pqt = [-_pq[1], _pq[0]];
  let _Npqt = njs.mul( 1/njs.norm2(_pqt), _pqt );
  let _Lpqt = njs.mul( 1000, _Npqt );
  two.makeLine( Q[0], Q[1], Q[0]+_Lpqt[0], Q[1]+_Lpqt[1] );
  two.makeLine( Q[0], Q[1], Q[0]-_Lpqt[0], Q[1]-_Lpqt[1] );


  mklune(P,W);


  two.makeCircle( z[0], z[1], 1 );
  two.makeCircle( P[0], P[1], 4 );
  two.makeCircle( Q[0], Q[1], 4 );
  two.makeCircle( W[0], W[1], 4 );
  two.makeCircle( U[0], U[1], 4 );


  let style = {
    "size": 15, //20,
    "weight": "normal",
    "family": "Libertine, Linux Libertine O"
  };


  two.makeText("p", P[0]-10, P[1]-10, style);
  two.makeText("q", Q[0]+10, Q[1]+10, style);
  two.makeText("u", U[0]+10, U[1]+10, style);
  two.makeText("w", W[0]-10, W[1]-10, style);


}

function show_frame() {
  let two = g_fig_ctx.two;

  let rect = two.makeRectangle( two.width/2, two.height/2, two.width, two.height )
  rect.lineWidth = 2;
}


function init() {
  let two = g_fig_ctx.two;

  //let vr = [0,0,1];
  //let theta = -Math.PI/16 + Math.PI/2;

  var ele = document.getElementById("ui_canvas");
  two.appendTo(ele);

  show_frame();

  fig_sabotage();

  two.update();

}
