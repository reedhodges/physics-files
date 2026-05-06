(* ::Package:: *)

(* Basis integrals: from Appendix A of notes *)
h1[c1_,c2_,b_,pSq_]:=1/(16 b^3 pSq^(3/2)) (2 ((c1-c2)^2+4 b^2 c1 pSq) ArcTan[(2 b mySqrt[pSq] mySqrt[c2-b^2 pSq])/(-c1+c2-2 b^2 pSq)]-I ((c1-c2)^2+4 b^2 c1 pSq) Log[(c1-c2+2 I b mySqrt[c1] mySqrt[pSq])/(c1-c2-2 I b mySqrt[c1] mySqrt[pSq])]+4 b (-c1+c2) mySqrt[c1] mySqrt[pSq]+4 b (c1-c2+2 b^2 pSq) mySqrt[pSq] mySqrt[c2-b^2 pSq])
h2[c1_,c2_,b_,pSq_]:=1/(16 b^5 pSq^(5/2)) (2 (3 (c1-c2)^2+4 b^2 c1 pSq) ArcTan[(2 b mySqrt[pSq] mySqrt[c2-b^2 pSq])/(-c1+c2-2 b^2 pSq)]-I (3 (c1-c2)^2+4 b^2 c1 pSq) Log[(c1-c2+2 I b mySqrt[c1] mySqrt[pSq])/(c1-c2-2 I b mySqrt[c1] mySqrt[pSq])]+12 b (-c1+c2) mySqrt[c1] mySqrt[pSq]-4 b (-3 c1+3 c2+2 b^2 pSq) mySqrt[pSq] mySqrt[c2-b^2 pSq])
Scalar[c1_,c2_,b_,pSq_]:=1/(8\[Pi]) 1/mySqrt[b^2 pSq] (ArcTan[(c2-c1)/(2mySqrt[b^2 pSq c1])]+ArcTan[(2b^2 pSq+c1-c2)/(2mySqrt[b^2 pSq(c2-b^2 pSq)])])
Linear[c1_,c2_,b_,pSq_]:=1/(8\[Pi] b pSq) mySqrt[c1]-1/(8\[Pi] b pSq) mySqrt[c2-b^2 pSq]+1/(2b pSq) (c2-c1)Scalar[c1,c2,b,pSq]
Quadratic0[c1_,c2_,b_,pSq_]:=b^2/(8\[Pi]) h2[c1,c2,b,pSq]
Quadratic1[c1_,c2_,b_,pSq_]:=1/pSq (\[CapitalLambda]/(12\[Pi])-1/(8\[Pi]) h1[c1,c2,b,pSq])
You can see numerically that using h1 and h2 is the same as writing the quadratic integrals in terms of the scalar and linear integral:
NewQuad0[c1_,c2_,b_,pSq_]:=1/pSq (-1/(16\[Pi]) Sqrt[c2-b^2 pSq]+c1/2 Scalar[c1,c2,b,pSq]+3/4 (c2-c1)/b Linear[c1,c2,b,pSq])
NewQuad1[c1_,c2_,b_,pSq_]:=1/pSq (\[CapitalLambda]/(12\[Pi])-1/(16\[Pi]) Sqrt[c2-b^2 pSq]-c1/2 Scalar[c1,c2,b,pSq]-1/4 (c2-c1)/b Linear[c1,c2,b,pSq])
N[Quadratic0[2,7,3.4,5000]]
N[NewQuad0[2,7,3.4,5000]]
N[Quadratic1[2,7,3.4,5000]]
N[NewQuad1[2,7,3.4,5000]]


LODecay[g\[Pi]_,pextSq_,m_,mstar_]:=(2I g\[Pi] SP[\[Epsilon]T,p\[Pi]]\[Mu]RM[mstar,m])/(pextSq+\[Gamma]Sq[mstar,m])
NLOTriangleDecay[g1_,g2_,g3_,pext_,pextSq_,m_,m1star_,m\[Pi]_,m2star_,mext_]:=Module[{c1,c2,b},
c1=\[Gamma]Sq[m,m1star];
c2=pextSq-(mT-m-mext)^2+m\[Pi]^2;
b=1;
g1 g2 g3 (4I \[Mu]RM[m1star,m]\[Mu]RM[m2star,mext])/(pextSq+\[Gamma]Sq[mext,m2star]) (SP[\[Epsilon]T,pext]SP[p\[Pi],pext](Scalar[c1,c2,b,pextSq]+Quadratic0[c1,c2,b,pextSq]-2Linear[c1,c2,b,pextSq])+SP[\[Epsilon]T,p\[Pi]]pextSq Quadratic1[c1,c2,b,pextSq])]
C\[Pi]Decay[g\[Pi]_,C\[Pi]_,pext_,pextSq_,m_,mstar_,m\[Pi]_,mext_]:=Module[{c1,c2,b},
c1=\[Gamma]Sq[m,mstar];
c2=pextSq-(mT-m-mext)^2+m\[Pi]^2;
b=1;
2I \[Mu]RM[mstar,m]g\[Pi] C\[Pi] SP[\[Epsilon]T,pext](Linear[c1,c2,b,pextSq]-Scalar[c1,c2,b,pextSq])]
C2Decay[g\[Pi]_,C2_,pextSq_,mext_,m1star_,m_,m2star_]:=-(1/\[Pi])I g\[Pi] C2 SP[\[Epsilon]T,p\[Pi]]\[Mu]RM[m,m1star]\[Mu]RM[mext,m2star](\[CapitalLambda]-mySqrt[\[Gamma]Sq[m,m1star]]) (pextSq-\[Gamma]Sq[m,m1star])/(pextSq+\[Gamma]Sq[mext,m2star])
B1Decay[B1_,m_,mstar_]:=(I B1 SP[\[Epsilon]T,p\[Pi]]\[Mu]RM[mstar,m])/(2\[Pi]) (\[CapitalLambda]-mySqrt[\[Gamma]Sq[m,mstar]])
C0DDecay[g\[Pi]_,C0D_,m1_,m2_,mstar_,mext1_,mext2_,m\[Pi]_,pext1Sq_,pext2Sq_]:=
Module[{c1,c2,b,p\[Pi]0,p\[Pi]Sq},
p\[Pi]0= (mT-2mD0)-(mext1-mD0+pext1Sq/(2mext1))-(mext2-mD0+pext2Sq/(2mext2));(*by conservation of four-momentum betw init and final states*)
p\[Pi]Sq=(1/(mext1 mext2) (mext1+mext2-mT) (mext1^2 mext2+mext2 pext1Sq+mext1 (mext2^2-mext2 mT+pext2Sq)))-m\[Pi]^2;
(* from on-shell condition for pion, keeping only O(p^2) terms *)
c1=\[Gamma]Sq[m2,mstar];
c2=-2\[Mu]RM[m1,m2](mT-m1-m2-p\[Pi]0-p\[Pi]Sq/(2m1));
b=\[Mu]RM[m1,m2]/m1;
4I \[Mu]RM[mstar,m2]\[Mu]RM[m1,m2]g\[Pi] C0D SP[\[Epsilon]T,p\[Pi]] Scalar[c1,c2,b,p\[Pi]Sq]
]


DerivOneLoop\[CapitalSigma][m_,mStar_]:=\[Mu]RM[mStar,m]^2/(2\[Pi] mySqrt[\[Gamma]Sq[m,mStar]])
DerivOPEtwoLoop[m1_,m1star_,m2_,m2star_,m\[Pi]_,g1_,g2_]:=
Module[{\[Gamma]1,\[Gamma]2,\[Gamma]3},
\[Gamma]1=mySqrt[2\[Mu]RM[m1star,m1](m1star+m1-mT)];
\[Gamma]2=mySqrt[2\[Mu]RM[m2star,m2](m2star+m2-mT)];
\[Gamma]3=mySqrt[(m2star-m1)^2-m\[Pi]^2];
 (g1 g2 \[Mu]RM[m1star,m1]^2 \[Mu]RM[m2star,m2])/(12\[Pi]^2) ((\[Gamma]3^2 (\[Gamma]1+\[Gamma]2))/(\[Gamma]1((\[Gamma]1+\[Gamma]2)^2+\[Gamma]3^2))+(\[CapitalLambda]-\[Gamma]2)/\[Gamma]1)+ (g1 g2 \[Mu]RM[m1star,m1] \[Mu]RM[m2star,m2]^2)/(12\[Pi]^2) ((\[Gamma]3^2 (\[Gamma]1+\[Gamma]2))/(\[Gamma]2((\[Gamma]1+\[Gamma]2)^2+\[Gamma]3^2))+(\[CapitalLambda]-\[Gamma]1)/\[Gamma]2)]
