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

//--------------------
//--------------------
//--------------------
//--------------------

function show_frame() {
  let two = g_fig_ctx.two;

  let rect = two.makeRectangle( two.width/2, two.height/2, two.width, two.height )
  rect.lineWidth = 2;
}

function fig_lune() {
  let two = g_fig_ctx.two;

  let style = {
    "size": 20,
    //"weight": "bold",
    "weight": "normal",
    "family": "Libertine, Linux Libertine O"
  };

  let _co_faded = "rgb(150,150,150)";
  _co_faded = "rgb(180,180,180)";

  let _co_grey = "rgb(80,80,80)";
  let _co_solid = "rgb(20,20,20)";
  let _co_highlight = "rgb(235,64,52)";
  _co_highlight = "rgb(201,62,52)";
  _co_highlight = '#FFB74D';
  _co_highlight = '#AD1457';


  let _r = 6;

  let P = [100, 300];
  let Q = [200,200];
  //let W = [330,170];
  let W = [320,210];

  P = [260, 260];
  Q = [360,160];
  W = [480,170];



  let dpw = njs.sub( W, P );
  let lpw = njs.norm2( dpw );

  let _cpw = two.makeCircle( P[0], P[1], lpw );
  _cpw.noFill();
  _cpw.stroke = _co_faded;
  _cpw.linewidth = 2;
  _cpw.opacity = 0.75;
  _cpw.dashes = [5,5];

  /*
  let theta_pw = Math.atan2( dpw[1], dpw[0] );
  let _s2 = two.makeArcSegment( P[0], P[1], lpw-0, lpw+0, theta_pw + Math.PI/3, theta_pw - Math.PI/3 );
  //_s2.fill = "rgb(220,220,220)";
  _s2.linewidth = 1;
  _s2.stroke = _co_faded;
  _s2.opacity = 0.75;
  _s2.dashes = [5,5];
  */


  let theta_wp = Math.atan2( -dpw[1], -dpw[0] );
  let _s3 = two.makeArcSegment( W[0], W[1], lpw-0, lpw+0, theta_wp + Math.PI/3, theta_wp - Math.PI/3 );
  //_s3.fill = "rgb(220,220,220)";
  _s3.linewidth = 1;
  _s3.stroke = _co_faded;
  _s3.opacity = 0.75;
  _s3.dashes = [5,5];



  let dpq = njs.sub( Q, P );
  let lpq = njs.norm2( dpq );

  let _pB = two.makeCircle( P[0], P[1], lpq );
  _pB.noFill();
  _pB.stroke = _co_faded;
  _pB.linewidth = 2;
  _pB.opacity = 0.75;
  _pB.dashes = [5,5];

  /*
  let _qB = two.makeCircle( Q[0], Q[1], lpq );
  _qB.noFill();
  _qB.stroke = "rgb(230,230,230)";
  _qB.linewidth = 2;
  _qB.opacity = 0.75;
  */


  let _p_txt = two.makeText( "p", P[0]-14, P[1]+10, style );
  let _q_txt = two.makeText( "q", Q[0]-20, Q[1]-1, style );
  let _w_txt = two.makeText( "w", W[0]+10, W[1]-10, style );

  let _lpq = two.makeLine( P[0], P[1], Q[0], Q[1] );
  _lpq.cap = 'round';
  _lpq.linewidth = 3;
  _lpq.fill = "rgb(20,20,20)";
  _lpq.dashes = [3,8];
  _lpq.dashes = [4,8];

  let theta0 = Math.atan2( dpq[1], dpq[0] );
  let _s0 = two.makeArcSegment( P[0], P[1], lpq-1, lpq+1, theta0 + Math.PI/3, theta0 - Math.PI/3 );
  _s0.fill = "rgb(20,20,20)";
  _s0.linewidth = 1;
  _s0.stroke = "rgb(20,20,20)";
  _s0.opacity = 0.75;

  let theta1 = Math.atan2( -dpq[1], -dpq[0] );
  let _s1 = two.makeArcSegment( Q[0], Q[1], lpq-1, lpq+1, theta1 + Math.PI/3, theta1 - Math.PI/3 );
  _s1.fill = "rgb(20,20,20)";
  _s1.linewidth = 1;
  _s1.stroke = "rgb(20,20,20)";
  _s1.opacity = 0.75;


  /*

  let ortho = [ -dpq[1], dpq[0] ];
  ortho[0] *= 1.5;
  ortho[1] *= 1.5;

  let _l0 = two.makeLine( Q[0] - ortho[0], Q[1] - ortho[1],
                          Q[0] + ortho[0], Q[1] + ortho[1] );

  _l0.fill = "rgb(20,20,20)";
  _l0.stroke = "rgb(20,20,20)";
  _l0.linewidth = 2;
  _l0.opacity = 0.75;
  //_l0.dashes = [ 5,5,1,5];
*/

  let _p = two.makeCircle( P[0], P[1], _r );
  _p.fill = _co_solid;
  _p.linewidth = 1.2;
  _p.stroke = _co_highlight;
  _p.fill = _co_highlight;

  let _q = two.makeCircle( Q[0], Q[1], _r );
  _q.fill = _co_solid;
  _q.linewidth = 1.2;
  _q.stroke = _co_solid;
  //_q.fill = _co_grey;

  let _w = two.makeCircle( W[0], W[1], _r );
  _w.fill = _co_solid;
  _w.linewidth = 1.2;
  _w.stroke = _co_solid;
  //_w.fill = _co_grey;


}

function init() {
  let two = g_fig_ctx.two;

  //let vr = [0,0,1];
  //let theta = -Math.PI/16 + Math.PI/2;

  var ele = document.getElementById("ui_canvas");
  two.appendTo(ele);

  show_frame();

  fig_lune();

  two.update();

}
