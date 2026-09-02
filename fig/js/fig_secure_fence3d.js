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
// rotate point v0 around axis _vr by theta (?)
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

var g_theta = 0;
var g_dtheta = 0.01;

function p_cmp(a,b) {
  if (a[2] < b[2]) { return  1; }
  if (a[2] > b[2]) { return -1; }
  return 0;
}

//WIP!!!
//this is still pretty janky
//this hack will work some (most?) of the time
//  but if lines are close enough in z-order, the
//  order from this won't be right...
//
function e_cmp(a,b) {
  let apq = [ a[0], a[1] ];
  let bpq = [ b[0], b[1] ];

  if (a[0][2] > a[1][2]) { apq = [ a[1], a[0] ]; }
  if (b[0][2] > b[1][2]) { bpq = [ b[1], b[0] ]; }

  if (apq[0][2] < b[0][2]) { return  1; }
  if (apq[1][2] > b[1][2]) { return -1; }

  return 0;
}

function lex_cmp(a,b) {
  if (a[0] < b[0]) { return -1; }
  if (a[0] > b[0]) { return  1; }

  if (a[1] < b[1]) { return -1; }
  if (a[1] > b[1]) { return  1; }

  if (a[2] < b[2]) { return -1; }
  if (a[2] > b[2]) { return  1; }

  return 0;
}

function line_eq(lu,lv, _eps) {
  _eps = ((typeof _eps === "undefined") ? (1/(1024*1024)) : _eps);

  if (((njs.norm2( njs.sub(lu[0],lv[0]) ) < _eps) &&
       (njs.norm2( njs.sub(lu[1],lv[1]) ) < _eps)) ||
      ((njs.norm2( njs.sub(lu[0],lv[1]) ) < _eps) &&
       (njs.norm2( njs.sub(lu[1],lv[0]) ) < _eps))) {
    return 1;
  }

  return 0;
}


var g_debug = 0;

function project_cone(v, xy, l) {
  let two = g_fig_ctx.two;

  let _co_f = "rgb(150,60,50)";
  let _co_s = "rgb(150,60,50)";
  let _lw = 2;

  _co_f = "rgb(200,120,100)";
  _co_s = "rgb(200,120,100)";


  let Nv = njs.mul( 1/njs.norm2(v), v);
  let theta = Math.acos(Nv[2]);

  let h = l*Nv[2];

  let rho = Math.atan2(v[1], v[0]) + (Math.PI/2);

  let _e = two.makeEllipse( xy[0], xy[1], l, h );
  _e.linewidth = _lw;
  _e.stroke = _co_s;
  _e.fill = _co_f;
  _e.rotation = rho;
  
  //let _c = Math.cos(rho - (Math.PI/2));
  //let _s = Math.sin(rho - (Math.PI/2));

  let _c = Math.cos(-rho);
  let _s = Math.sin(-rho);

  let p_tri = njs.dot( 
    [
      [ 0, -2*l*Math.sin(theta)],
      [ l, 0],
      [-l, 0] ],
    [ [_c, -_s], [_s, _c] ]
  );

  for (let i=0; i<p_tri.length; i++) {
    p_tri[i][0] += xy[0];
    p_tri[i][1] += xy[1];
  }

  let a_tri = makeTwoAnchor(p_tri);

  let _path2 = two.makePath(a_tri);
  _path2.fill = _co_f;
  _path2.stroke = _co_s;
  _path2.linewidth = _lw;
  _path2.join = "round";

}

function project_arrow(p,q,l) {
  let two = g_fig_ctx.two;

  let dqp = njs.sub(q,p);
  let Nqp = njs.mul( 1/njs.norm2(dqp), dqp);

  let _f = 30;

  let qq = njs.add( q, njs.mul( _f, Nqp ) );

  //let _l = two.makeLine(p[0], p[1], q[0], q[1]);
  let _l = two.makeLine(q[0], q[1], qq[0], qq[1]);
  _l.fill = "rgb(100,200,120)";
  
  //project_cone(Nqp, q, l);
  project_cone(Nqp, qq, l);

}

function show() {
  let two = g_fig_ctx.two;
  let data = DATA;

  let center = [300,300,300];
  let scale = 100;

  let fence_post = data.fence_post;
  let face_edge = data.face_edge;

  let M = [
    [ 4.7, 0, 0 ],
    [ 0, 3.5, 0 ],
    [ 0, 0, 1 ]
  ];

  for (let idir=0; idir<fence_post.length; idir++) {

    for (let fpi=0; fpi<fence_post[idir].length; fpi++) {
      let fp_a = fence_post[idir][fpi];
      let fp_b = fence_post[idir][(fpi+1)%fence_post[idir].length];

      let p_a = njs.add(njs.mul(scale, njs.dot(M, fp_a)), center);
      let p_b = njs.add(njs.mul(scale, njs.dot(M, fp_b)), center);

      two.makeLine( p_a[0], p_a[1], p_b[0], p_b[1] );
    }
  }

}

function init() {
  let two = g_fig_ctx.two;
  var ele = document.getElementById("ui_canvas");
  two.appendTo(ele);

  show_frame();

  show();

  two.update();
}


var DATA = {
  "plane_a"   : {
    "P"  : [ [0.25, -0.5, 0.5], [-0.5, 0.15, 0.5], [-0.5, -0.45, -0.5], [-0.15, -0.5, -0.5] ],
    "Pe" : [
      [ 0.36875            , -0.54375,  0.625],
      [-0.56875            ,  0.26875,  0.625],
      [-0.56875            , -0.48125, -0.625],
      [-0.13124999999999998, -0.54375, -0.625]
    ],
    "com": [-0.225, -0.325, 0]
  },
  "plane_b"   : {
    "P"  : [ [-0.12, 0.5, 0.5],    [0.5, 0.5, 0.25],    [0.5, -0.15, 0.5] ],
    "Pe" : [ [-0.368, 0.63, 0.55], [0.624, 0.63, 0.15], [0.624, -0.41, 0.55] ],
    "com": [ 0.29333333333333333,  0.2833333333333333,                 0.4166666666666667                  ]
  },
  "fence_post": [
    [
      [0.5, -0.5, -0.5], [0.5,  0  , -0.5], [0.5,  0.5, -0.5],
      [0.5, -0.5,  0  ], [0.5,  0  ,  0  ], [0.5,  0.5,  0  ],
      [0.5, -0.5,  0.5], [0.5,  0  ,  0.5], [0.5,  0.5,  0.5]
    ],
    [
      [-0.5, -0.5, -0.5], [-0.5,  0  , -0.5], [-0.5,  0.5, -0.5],
      [-0.5, -0.5,  0  ], [-0.5,  0  ,  0  ], [-0.5,  0.5,  0  ],
      [-0.5, -0.5,  0.5], [-0.5,  0  ,  0.5], [-0.5,  0.5,  0.5]
    ],
    [
      [-0.5, 0.5, -0.5], [ 0  , 0.5, -0.5], [ 0.5, 0.5, -0.5],
      [-0.5, 0.5,  0  ], [ 0  , 0.5,  0  ], [ 0.5, 0.5,  0  ],
      [-0.5, 0.5,  0.5], [ 0  , 0.5,  0.5], [ 0.5, 0.5,  0.5]
    ],
    [
      [-0.5, -0.5, -0.5], [ 0  , -0.5, -0.5], [ 0.5, -0.5, -0.5],
      [-0.5, -0.5,  0  ], [ 0  , -0.5,  0  ], [ 0.5, -0.5,  0  ],
      [-0.5, -0.5,  0.5], [ 0  , -0.5,  0.5], [ 0.5, -0.5,  0.5]
    ],
    [
      [-0.5, -0.5, 0.5], [-0.5,  0  , 0.5], [-0.5,  0.5, 0.5],
      [ 0  , -0.5, 0.5], [ 0  ,  0  , 0.5], [ 0  ,  0.5, 0.5],
      [ 0.5, -0.5, 0.5], [ 0.5,  0  , 0.5], [ 0.5,  0.5, 0.5]
    ],
    [
      [-0.5, -0.5, -0.5], [-0.5,  0  , -0.5], [-0.5,  0.5, -0.5],
      [ 0  , -0.5, -0.5], [ 0  ,  0  , -0.5], [ 0  ,  0.5, -0.5],
      [ 0.5, -0.5, -0.5], [ 0.5,  0  , -0.5], [ 0.5,  0.5, -0.5]
    ]
  ],
  "p"         : [0, 0, 0],
  "face_edge" : [
    [ [ 0.5, -0.5, -0.5], [ 0.5,  0.5, -0.5], [ 0.5,  0.5,  0.5], [ 0.5, -0.5,  0.5] ],
    [ [-0.5, -0.5,  0.5], [-0.5,  0.5,  0.5], [-0.5,  0.5, -0.5], [-0.5, -0.5, -0.5] ],
    [ [ 0.5,  0.5, -0.5], [-0.5,  0.5, -0.5], [-0.5,  0.5,  0.5], [ 0.5,  0.5,  0.5] ],
    [ [ 0.5, -0.5,  0.5], [-0.5, -0.5,  0.5], [-0.5, -0.5, -0.5], [ 0.5, -0.5, -0.5] ],
    [ [-0.5, -0.5,  0.5], [-0.5,  0.5,  0.5], [ 0.5,  0.5,  0.5], [ 0.5, -0.5,  0.5] ],
    [ [ 0.5, -0.5, -0.5], [ 0.5,  0.5, -0.5], [-0.5,  0.5, -0.5], [-0.5, -0.5, -0.5] ]
  ]
};
