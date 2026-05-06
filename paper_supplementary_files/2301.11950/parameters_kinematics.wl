(* ::Package:: *)

(* PDS scheme cutoff *)
\[CapitalLambda]PDS=0;
\[CapitalLambda]=0;
(* angle relating couplings of Subscript[T, cc]^+ to each channel *)
\[Theta]=-32.4Degree;
(* mass of D^+ *)
mDp=1869.66;
(* mass of D^0 *)
mD0=1864.84;
(* mass of D^(*+) *)
mDps=2010.26;
(* mass of D^(*0) *)
mD0s=2006.85;
(* use binding energy from unitarized Breit Wigner LHCb fit *)
bindingenergy=-0.360;
mT=mDps+mD0+bindingenergy;
(* pion decay constant *)
f\[Pi]=130.;
(* axial coupling of HH\[Chi]PT *)
g=0.54;
(* mass of \[Pi]^0 *)
m\[Pi]0=134.9768;
(* mass of \[Pi]^+ *)
m\[Pi]p=139.57039;
(* photon coupling diagrams *)
(* reduced mass *)
\[Mu]RM[m1_,m2_]:=(m1^-1+m2^-1)^-1
\[Gamma]Sq[m1_,m2_]:=2\[Mu]RM[m1,m2](m1+m2-mT)
(*mySqrt is defined to deal with expressions involving Sqrt[x-i\[Epsilon]]*)
mySqrt[x_]:=If[x>=0,Sqrt[Abs[x]],-I Sqrt[Abs[x]]]
(* D^*D diagram in PDS scheme *)
\[CapitalSigma][c_]:=1/(4\[Pi]) (\[CapitalLambda]PDS-mySqrt[c])
SimpsonsRule[f_,{a_,b_},n_]:=
(* f needs to be a function with only one argument, the integration variable. n must be even *)
Module[
{h,x},
h=(b-a)/n;
x[j_]:=a+j h;
N[h/3 (f[x[0]]+4Sum[f[x[2j-1]],{j,1,n/2}]+2Sum[f[x[2j]],{j,1,n/2-1}]+f[x[n]])]
]


(* Follows PDG section on kinematics *)
m12[m3_,p3Sq_]:=Sqrt[(mT-m3)^2-mT/m3 p3Sq];
E2[m1_,m2_,m3_,p3Sq_]:=(m12[m3,p3Sq]^2+m2^2-m1^2)/(2m12[m3,p3Sq]);
E3[m1_,m2_,m3_,p3Sq_]:=(mT^2-m3^2-m12[m3,p3Sq]^2)/(2m12[m3,p3Sq]);
p2mag[m1_,m2_,m3_,p3Sq_]:=Sqrt[E2[m1,m2,m3,p3Sq]^2-m2^2];
p3mag[m1_,m2_,m3_,p3Sq_]:=Sqrt[E3[m1,m2,m3,p3Sq]^2-m3^2];
m23SqMin[m1_,m2_,m3_,p3Sq_]:=(E2[m1,m2,m3,p3Sq]+E3[m1,m2,m3,p3Sq])^2-(p2mag[m1,m2,m3,p3Sq]+p3mag[m1,m2,m3,p3Sq])^2;
m23SqMax[m1_,m2_,m3_,p3Sq_]:=(E2[m1,m2,m3,p3Sq]+E3[m1,m2,m3,p3Sq])^2-(p2mag[m1,m2,m3,p3Sq]-p3mag[m1,m2,m3,p3Sq])^2;
p1SqMin[m1_,m2_,m3_,p3Sq_]:=m1/mT ((mT-m1)^2-m23SqMax[m1,m2,m3,p3Sq]);
p1SqMax[m1_,m2_,m3_,p3Sq_]:=m1/mT ((mT-m1)^2-m23SqMin[m1,m2,m3,p3Sq]);
p3SqMin[m1_,m2_,m3_]:=0;
p3SqMax[m1_,m2_,m3_]:=m3/mT ((mT-m3)^2-(m1+m2)^2);
