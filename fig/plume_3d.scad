s = 1;
k = 2;

l0 = 2*s;
l1 = 2*(2*k+1)*s;
W=(2*k+1)*s;
h=2*k*s + s;

// _c corner
// _s side
// _m middle (center of square top)
//
p_c = [s,s,s];
p_s = [s,0,s];
p_m = [0,0,s];

q0 = [W,W,h];
q1 = [-W,W,h];
q2 = [-W,-W,h];
q3 = [W,-W,h];

translate([s,s,s]) sphere(r = 1/16, $fn=100);

R= 1/8;

translate(q0) sphere(r = R, $fn=100);
translate(q1) sphere(r = R, $fn=100);
translate(q2) sphere(r = R, $fn=100);
translate(q3) sphere(r = R, $fn=100);

translate(c0) sphere(r = R, $fn=100);
translate(c1) sphere(r = R, $fn=100);
translate(c2) sphere(r = R, $fn=100);
translate(c3) sphere(r = R, $fn=100);


c0 = (q0 + p_c) / 2;
cr0 = norm( c0 - p_c );

c1 = (q1 + p_c) / 2;
cr1 = norm( c1 - p_c );

c2 = (q2 + p_c) / 2;
cr2 = norm( c2 - p_c );

c3 = (q3 + p_c) / 2;
cr3 = norm( c3 - p_c );

intersection() {
  translate(c0) sphere(r = cr0, $fn=100);
  translate(c1) sphere(r = cr1, $fn=100);
  translate(c2) sphere(r = cr2, $fn=100);
  translate(c3) sphere(r = cr3, $fn=100);
};

color( c=[0.2,0.2,0.2], alpha = 0.3) {
  cube([l0,l0,l0], center=true);
}


color( c=[0.1,0.1,0.1], alpha = 0.2) {
  cube([l1,l1,l1], center=true);
}


