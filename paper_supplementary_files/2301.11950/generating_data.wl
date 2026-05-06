(* ::Package:: *)

C\[Pi]Min=1/197 {(0.76-0.09),(0.76-0.09),(3.0-0.32),(-(3.0-0.32))};
C\[Pi]Max=1/197 {(0.76+0.14),(0.76+0.14),(3.0+0.4),(-(3.0+0.4))};
C0DMin=-(1)^2/197^2;
C0DMax=(0.5)^2/197^2;
\[Beta]Min={1/100^2,0,1/100^2,0};
\[Beta]Max={-1/100^2,-0.26,-1/100^2,-0.26};
SPrule[pDpSq_,pD0Sq_,p\[Pi]Sq_]:={SP[\[Epsilon]T,p\[Pi]]^2->p\[Pi]Sq/3,SP[\[Epsilon]T,pD0]^2->pD0Sq/3,SP[\[Epsilon]T,pDp]^2->pDpSq/3,SP[\[Epsilon]T,pDp]SP[\[Epsilon]T,p\[Pi]]->SP[pDp,p\[Pi]]/3,SP[\[Epsilon]T,pD0]SP[\[Epsilon]T,p\[Pi]]->SP[pD0,p\[Pi]]/3,SP[pDp,p\[Pi]]->1/2 (pD0Sq-pDpSq-p\[Pi]Sq),SP[pD0,p\[Pi]]->1/2 (pDpSq-pD0Sq-p\[Pi]Sq),Arg[pDpSq]->0,Arg[pD0Sq]->0,Arg[-pDpSq]->\[Pi],Arg[-pD0Sq]->\[Pi],SP[x_,y_]->SP[y,x]};
Re\[CapitalSigma]pLO=DerivOneLoop\[CapitalSigma][mD0,mDps]+DerivOneLoop\[CapitalSigma][mDp,mD0s];
NAterm[pDpSq_,pD0Sq_,p\[Pi]Sq_]:=Evaluate[ComplexExpand[2/Re\[CapitalSigma]pLO Re[LODecay[-g/(Sqrt[2]f\[Pi]),pDpSq,mDp,mD0s]Conjugate[NLOTriangleDecay[-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),pD0,pD0Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]+NLOTriangleDecay[g/f\[Pi],g/f\[Pi],-g/(Sqrt[2]f\[Pi]),pDp,pDpSq,mDp,mD0s,m\[Pi]p,mD0s,mDp]-NLOTriangleDecay[g/f\[Pi],g/f\[Pi],-g/(Sqrt[2]f\[Pi]),pD0,pD0Sq,mD0,mDps,m\[Pi]p,mDps,mD0]-NLOTriangleDecay[g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),pDp,pDpSq,mD0,mDps,m\[Pi]0,mD0s,mDp]]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]]+Evaluate[ComplexExpand[2/Re\[CapitalSigma]pLO Re[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]Conjugate[NLOTriangleDecay[g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),pDp,pDpSq,mD0,mDps,m\[Pi]0,mD0s,mDp]+NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/(Sqrt[2]f\[Pi]),pD0,pD0Sq,mD0,mDps,m\[Pi]p,mDps,mD0]-NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/(Sqrt[2]f\[Pi]),pDp,pDpSq,mDp,mD0s,m\[Pi]p,mD0s,mDp]-NLOTriangleDecay[-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),pD0,pD0Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
C\[Pi]C0Dterm[pDpSq_,pD0Sq_,p\[Pi]Sq_,{C\[Pi]DpDp\[Pi]0\[Pi]0_,C\[Pi]D0D0\[Pi]0\[Pi]0_,C\[Pi]DpD0\[Pi]p\[Pi]0_,C\[Pi]DpD0\[Pi]m\[Pi]0_},C0D_]:=Evaluate[ComplexExpand[2/Re\[CapitalSigma]pLO Re[LODecay[-g/(Sqrt[2]f\[Pi]),pDpSq,mDp,mD0s]Conjugate[C\[Pi]Decay[-g/(Sqrt[2]f\[Pi]),C\[Pi]DpDp\[Pi]0\[Pi]0,pD0,pD0Sq,mDp,mD0s,m\[Pi]0,mD0]+C0DDecay[-g/(Sqrt[2]f\[Pi]),C0D,mD0,mDp,mD0s,mD0,mDp,m\[Pi]0,pD0Sq,pDpSq]-C\[Pi]Decay[g/f\[Pi],C\[Pi]DpD0\[Pi]p\[Pi]0,pD0,pD0Sq,mD0,mDps,m\[Pi]p,mD0]-C0DDecay[g/(Sqrt[2]f\[Pi]),C0D,mDp,mD0,mDps,mD0,mDp,m\[Pi]0,pD0Sq,pDpSq]]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]]+Evaluate[ComplexExpand[2/Re\[CapitalSigma]pLO Re[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]Conjugate[C\[Pi]Decay[g/(Sqrt[2]f\[Pi]),C\[Pi]D0D0\[Pi]0\[Pi]0,pDp,pDpSq,mD0,mDps,m\[Pi]0,mDp]+C0DDecay[g/(Sqrt[2]f\[Pi]),C0D,mDp,mD0,mDps,mDp,mD0,m\[Pi]0,pDpSq,pD0Sq]-C\[Pi]Decay[g/f\[Pi],C\[Pi]DpD0\[Pi]m\[Pi]0,pDp,pDpSq,mDp,mD0s,m\[Pi]p,mDp]-C0DDecay[-g/(Sqrt[2]f\[Pi]),C0D,mD0,mDp,mD0s,mDp,mD0,m\[Pi]0,pDpSq,pD0Sq]]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
C2B1[pDpSq_,pD0Sq_,p\[Pi]Sq_,{\[Beta]1_,\[Beta]2_,\[Beta]3_,\[Beta]4_}]:=Evaluate[ComplexExpand[-1/Re\[CapitalSigma]pLO ((Abs[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]]^2-LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]Conjugate[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]])(\[Beta]1(pDpSq+Sqrt[2\[Mu]RM[mD0s,mDp](mD0s+mDp-mT)])+\[Beta]2)+(Abs[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]]^2-LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]Conjugate[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]])(\[Beta]3(pD0Sq+Sqrt[2\[Mu]RM[mD0,mDps](mDps+mD0-mT)])+\[Beta]4))]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
\[CapitalGamma]0LO[pDpSq_,pD0Sq_,p\[Pi]Sq_]:=Evaluate[1/Re\[CapitalSigma]pLO ComplexExpand[Abs[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]]^2+Abs[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]]^2-LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]Conjugate[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]]-LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]Conjugate[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
Re\[CapitalSigma]pNLO=DerivOPEtwoLoop[mDp,mD0s,mDp,mD0s,m\[Pi]p,g/f\[Pi],g/f\[Pi]]+DerivOPEtwoLoop[mD0,mDps,mD0,mDps,m\[Pi]p,g/f\[Pi],g/f\[Pi]]-DerivOPEtwoLoop[mDp,mD0s,mD0,mDps,m\[Pi]0,-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi])]-DerivOPEtwoLoop[mD0,mDps,mDp,mD0s,m\[Pi]0,g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi])];
SelfEnergyCorrection[pDpSq_,pD0Sq_,p\[Pi]Sq_]:=Evaluate[-\[CapitalGamma]0LO [pDpSq,pD0Sq,p\[Pi]Sq] Re\[CapitalSigma]pNLO/Re\[CapitalSigma]pLO//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
\[CapitalGamma]0NLO[pDpSq_,pD0Sq_,p\[Pi]Sq_,{C\[Pi]DpDp\[Pi]0\[Pi]0_,C\[Pi]D0D0\[Pi]0\[Pi]0_,C\[Pi]DpD0\[Pi]p\[Pi]0_,C\[Pi]DpD0\[Pi]m\[Pi]0_},C0D_,{\[Beta]1_,\[Beta]2_,\[Beta]3_,\[Beta]4_}]:=NAterm[pDpSq,pD0Sq,p\[Pi]Sq]+C\[Pi]C0Dterm[pDpSq,pD0Sq,p\[Pi]Sq,{C\[Pi]DpDp\[Pi]0\[Pi]0,C\[Pi]D0D0\[Pi]0\[Pi]0,C\[Pi]DpD0\[Pi]p\[Pi]0,C\[Pi]DpD0\[Pi]m\[Pi]0},C0D]+C2B1[pDpSq,pD0Sq,p\[Pi]Sq,{\[Beta]1,\[Beta]2,\[Beta]3,\[Beta]4}]+SelfEnergyCorrection[pDpSq,pD0Sq,p\[Pi]Sq]


(* ::Chapter:: *)
(*neutral pion decay*)


Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mDp;
m2=m\[Pi]0;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mDp-pDpSq/(2mDp)-pD0Sq/(2mD0))^2-m\[Pi]0^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LO[pDpSq,pD0Sq,p\[Pi]Sq],{pD0Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pDpSq,p1SqMin[m1,m2,m3,pD0Sq],p1SqMax[m1,m2,m3,pD0Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mDp;
m2=m\[Pi]0;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mDp-pDpSq/(2mDp)-pD0Sq/(2mD0))^2-m\[Pi]0^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0NLO[pDpSq,pD0Sq,p\[Pi]Sq,C\[Pi]Max,C0DMax,\[Beta]Max],{pD0Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pDpSq,p1SqMin[m1,m2,m3,pD0Sq],p1SqMax[m1,m2,m3,pD0Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mDp;
m2=m\[Pi]0;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mDp-pDpSq/(2mDp)-pD0Sq/(2mD0))^2-m\[Pi]0^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0NLO[pDpSq,pD0Sq,p\[Pi]Sq,C\[Pi]Min,C0DMin,\[Beta]Min],{pD0Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pDpSq,p1SqMin[m1,m2,m3,pD0Sq],p1SqMax[m1,m2,m3,pD0Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]


DateString[]
LOData1=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD0Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mDp;
m2=mD0;
m3=m\[Pi]0;
T=(mT^2-mDD^2+m\[Pi]0^2)/(2mT)-m\[Pi]0;
p\[Pi]Sq=2m3 T;
pD0Sq[pDpSq_]:=2m2(mT-m1-m2-pDpSq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pDpSq_]:=1/(32\[Pi]^3 mDD) 10^3 \[CapitalGamma]0LO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,mD0+mDp,mT-m\[Pi]0-1,(mT-m\[Pi]0-(mD0+mDp))/100}];
DateString[]
DateString[]
MinData1=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD0Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mDp;
m2=mD0;
m3=m\[Pi]0;
T=(mT^2-mDD^2+m\[Pi]0^2)/(2mT)-m\[Pi]0;
p\[Pi]Sq=2m3 T;
pD0Sq[pDpSq_]:=2m2(mT-m1-m2-pDpSq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pDpSq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 (\[CapitalGamma]0LO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq]+\[CapitalGamma]0NLO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq,C\[Pi]Min,C0DMin,\[Beta]Min])];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,mD0+mDp,mT-m\[Pi]0-1,(mT-m\[Pi]0-(mD0+mDp))/100}];
DateString[]
DateString[]
MaxData1=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD0Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mDp;
m2=mD0;
m3=m\[Pi]0;
T=(mT^2-mDD^2+m\[Pi]0^2)/(2mT)-m\[Pi]0;
p\[Pi]Sq=2m3 T;
pD0Sq[pDpSq_]:=2m2(mT-m1-m2-pDpSq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pDpSq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 (\[CapitalGamma]0LO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq]+\[CapitalGamma]0NLO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq,C\[Pi]Max,C0DMax,\[Beta]Max])];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,mD0+mDp,mT-m\[Pi]0-1,(mT-m\[Pi]0-(mD0+mDp))/100}];
DateString[]


(* ::Chapter:: *)
(*charged pion decay*)


C\[Pi]Min=1/197 {(2.9-0.18),(3.0-0.32)};
C\[Pi]Max=1/197 {(2.9+0.27),(3.0+0.4)};
C0DMin=-(1)^2/197^2;
C0DMax=(0.5)^2/197^2;
\[Beta]Min={0,1/100^2};
\[Beta]Max={-0.26,-1/100^2};
SPrule[pD1Sq_,pD2Sq_,p\[Pi]Sq_]:={SP[\[Epsilon]T,p\[Pi]]^2->p\[Pi]Sq/3,SP[\[Epsilon]T,pD1]^2->pD1Sq/3,SP[\[Epsilon]T,pD2]^2->pD2Sq/3,SP[\[Epsilon]T,pD2]SP[\[Epsilon]T,p\[Pi]]->SP[pD2,p\[Pi]]/3,SP[\[Epsilon]T,pD1]SP[\[Epsilon]T,p\[Pi]]->SP[pD1,p\[Pi]]/3,SP[pD2,p\[Pi]]->1/2 (pD1Sq-pD2Sq-p\[Pi]Sq),SP[pD1,p\[Pi]]->1/2 (pD2Sq-pD1Sq-p\[Pi]Sq),Arg[pD2Sq]->0,Arg[pD1Sq]->0,Arg[-pD2Sq]->\[Pi],Arg[-pD1Sq]->\[Pi],SP[x_,y_]->SP[y,x]};
Re\[CapitalSigma]pLO=DerivOneLoop\[CapitalSigma][mD0,mDps]+DerivOneLoop\[CapitalSigma][mDp,mD0s];
NAterm[pD1Sq_,pD2Sq_,p\[Pi]Sq_]:=Evaluate[ComplexExpand[1/Re\[CapitalSigma]pLO Re[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]Conjugate[NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/f\[Pi],pD1,pD1Sq,mD0,mDps,m\[Pi]p,mDps,mD0]+NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/f\[Pi],pD2,pD2Sq,mD0,mDps,m\[Pi]p,mDps,mD0]-NLOTriangleDecay[-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),g/f\[Pi],pD1,pD1Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]-NLOTriangleDecay[g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),g/f\[Pi],pD2,pD2Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]]]]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]]+Evaluate[ComplexExpand[1/Re\[CapitalSigma]pLO Re[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]Conjugate[NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/f\[Pi],pD2,pD2Sq,mD0,mDps,m\[Pi]p,mDps,mD0]+NLOTriangleDecay[g/f\[Pi],g/f\[Pi],g/f\[Pi],pD1,pD1Sq,mD0,mDps,m\[Pi]p,mDps,mD0]-NLOTriangleDecay[-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi]),g/f\[Pi],pD2,pD2Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]-NLOTriangleDecay[g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi]),g/f\[Pi],pD1,pD1Sq,mDp,mD0s,m\[Pi]0,mDps,mD0]]]]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]]
C\[Pi]C0Dterm[pD1Sq_,pD2Sq_,p\[Pi]Sq_,{C\[Pi]D0D0\[Pi]p\[Pi]p_,C\[Pi]DpD0\[Pi]p\[Pi]0_},C0D_]:=Evaluate[ComplexExpand[1/Re\[CapitalSigma]pLO Re[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]Conjugate[C\[Pi]Decay[g/f\[Pi],C\[Pi]D0D0\[Pi]p\[Pi]p,pD1,pD1Sq,mD0,mDps,m\[Pi]p,mD0]+C0DDecay[g/f\[Pi],C0D/2,mD0,mD0,mDps,mD0,mD0,m\[Pi]p,pD1Sq,pD2Sq]-C\[Pi]Decay[-g/(Sqrt[2]f\[Pi]),C\[Pi]DpD0\[Pi]p\[Pi]0,pD1,pD1Sq,mDp,mD0s,m\[Pi]0,mD0]]]]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]]+Evaluate[ComplexExpand[1/Re\[CapitalSigma]pLO Re[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]Conjugate[C\[Pi]Decay[g/f\[Pi],C\[Pi]D0D0\[Pi]p\[Pi]p,pD2,pD2Sq,mD0,mDps,m\[Pi]p,mD0]+C0DDecay[g/f\[Pi],C0D/2,mD0,mD0,mDps,mD0,mD0,m\[Pi]p,pD2Sq,pD1Sq]-C\[Pi]Decay[-g/(Sqrt[2]f\[Pi]),C\[Pi]DpD0\[Pi]p\[Pi]0,pD2,pD2Sq,mDp,mD0s,m\[Pi]0,mD0]]]]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]]
C2B1[pD1Sq_,pD2Sq_,p\[Pi]Sq_,\[Beta]5_]:=Evaluate[ComplexExpand[1/Re\[CapitalSigma]pLO ((4g^2 \[Mu]RM[mD0,mDps]^2 p\[Pi]Sq)/(3f\[Pi]^2))(-\[Beta]5)(1/(pD1Sq+2\[Mu]RM[mD0,mDps](mD0+mDps-mT))+1/(pD2Sq+2\[Mu]RM[mD0,mDps](mD0+mDps-mT)))]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]];
\[CapitalGamma]0LO[pD1Sq_,pD2Sq_,p\[Pi]Sq_]:=Evaluate[1/2 1/Re\[CapitalSigma]pLO ComplexExpand[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]Conjugate[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]]+Abs[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]]^2+LODecay[g/f\[Pi],pD1Sq,mD0,mDps]Conjugate[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]]+Abs[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]]^2]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]];
Re\[CapitalSigma]pNLO=DerivOPEtwoLoop[mDp,mD0s,mDp,mD0s,m\[Pi]p,g/f\[Pi],g/f\[Pi]]+DerivOPEtwoLoop[mD0,mDps,mD0,mDps,m\[Pi]p,g/f\[Pi],g/f\[Pi]]-DerivOPEtwoLoop[mDp,mD0s,mD0,mDps,m\[Pi]0,-g/(Sqrt[2]f\[Pi]),g/(Sqrt[2]f\[Pi])]-DerivOPEtwoLoop[mD0,mDps,mDp,mD0s,m\[Pi]0,g/(Sqrt[2]f\[Pi]),-g/(Sqrt[2]f\[Pi])];
SelfEnergyCorrection[pD1Sq_,pD2Sq_,p\[Pi]Sq_,\[Beta]4_]:=Evaluate[\[CapitalGamma]0LO [pD1Sq,pD2Sq,p\[Pi]Sq](-\[Beta]4-Re\[CapitalSigma]pNLO/Re\[CapitalSigma]pLO)//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]];
\[CapitalGamma]0NLO[pD1Sq_,pD2Sq_,p\[Pi]Sq_,{C\[Pi]D0D0\[Pi]p\[Pi]p_,C\[Pi]DpD0\[Pi]p\[Pi]0_},C0D_,{\[Beta]4_,\[Beta]5_}]:=(NAterm[pD1Sq,pD2Sq,p\[Pi]Sq]+C\[Pi]C0Dterm[pD1Sq,pD2Sq,p\[Pi]Sq,{C\[Pi]D0D0\[Pi]p\[Pi]p,C\[Pi]DpD0\[Pi]p\[Pi]0},C0D]+C2B1[pD1Sq,pD2Sq,p\[Pi]Sq,\[Beta]5]+SelfEnergyCorrection[pD1Sq,pD2Sq,p\[Pi]Sq,\[Beta]4])


Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mD0;
m2=m\[Pi]p;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mD0-pD1Sq/(2mD0)-pD2Sq/(2mD0))^2-m\[Pi]p^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LO[pD1Sq,pD2Sq,p\[Pi]Sq],{pD2Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pD1Sq,p1SqMin[m1,m2,m3,pD2Sq],p1SqMax[m1,m2,m3,pD2Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mD0;
m2=m\[Pi]p;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mD0-pD1Sq/(2mD0)-pD2Sq/(2mD0))^2-m\[Pi]p^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0NLO[pD1Sq,pD2Sq,p\[Pi]Sq,C\[Pi]Max,C0DMax,\[Beta]Max],{pD2Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pD1Sq,p1SqMin[m1,m2,m3,pD2Sq],p1SqMax[m1,m2,m3,pD2Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mD0;
m2=m\[Pi]p;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mD0-pD1Sq/(2mD0)-pD2Sq/(2mD0))^2-m\[Pi]p^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0NLO[pD1Sq,pD2Sq,p\[Pi]Sq,C\[Pi]Min,C0DMin,\[Beta]Min],{pD2Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pD1Sq,p1SqMin[m1,m2,m3,pD2Sq],p1SqMax[m1,m2,m3,pD2Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]


DateString[]
LOData2=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD2Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mD0;
m2=mD0;
m3=m\[Pi]p;
T=(mT^2-mDD^2+m\[Pi]p^2)/(2mT)-m\[Pi]p;
p\[Pi]Sq=2m3 T;
pD2Sq[pD1Sq_]:=2m2(mT-m1-m2-pD1Sq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pD1Sq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 \[CapitalGamma]0LO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq]];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,2mD0,mT-m\[Pi]p-1,(mT-m\[Pi]p-2mD0)/100}];
DateString[]
DateString[]
MinData2=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD2Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mD0;
m2=mD0;
m3=m\[Pi]p;
T=(mT^2-mDD^2+m\[Pi]p^2)/(2mT)-m\[Pi]p;
p\[Pi]Sq=2m3 T;
pD2Sq[pD1Sq_]:=2m2(mT-m1-m2-pD1Sq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pD1Sq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 (\[CapitalGamma]0LO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq]+\[CapitalGamma]0NLO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq,C\[Pi]Min,C0DMin,\[Beta]Min])];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,2mD0,mT-m\[Pi]p-1,(mT-m\[Pi]p-2mD0)/100}];
DateString[]
DateString[]
MaxData2=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD2Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mD0;
m2=mD0;
m3=m\[Pi]p;
T=(mT^2-mDD^2+m\[Pi]p^2)/(2mT)-m\[Pi]p;
p\[Pi]Sq=2m3 T;
pD2Sq[pD1Sq_]:=2m2(mT-m1-m2-pD1Sq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pD1Sq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 (\[CapitalGamma]0LO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq]+\[CapitalGamma]0NLO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq,C\[Pi]Max,C0DMax,\[Beta]Max])];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,2mD0,mT-m\[Pi]p-1,(mT-m\[Pi]p-2mD0)/100}];
DateString[]


(* ::Chapter:: *)
(*constant propagator plots*)


(* ::Section:: *)
(*neutral pion decay*)


SPrule[pDpSq_,pD0Sq_,p\[Pi]Sq_]:={SP[\[Epsilon]T,p\[Pi]]^2->p\[Pi]Sq/3,SP[\[Epsilon]T,pD0]^2->pD0Sq/3,SP[\[Epsilon]T,pDp]^2->pDpSq/3,SP[\[Epsilon]T,pDp]SP[\[Epsilon]T,p\[Pi]]->SP[pDp,p\[Pi]]/3,SP[\[Epsilon]T,pD0]SP[\[Epsilon]T,p\[Pi]]->SP[pD0,p\[Pi]]/3,SP[pDp,p\[Pi]]->1/2 (pD0Sq-pDpSq-p\[Pi]Sq),SP[pD0,p\[Pi]]->1/2 (pDpSq-pD0Sq-p\[Pi]Sq),Arg[pDpSq]->0,Arg[pD0Sq]->0,Arg[-pDpSq]->\[Pi],Arg[-pD0Sq]->\[Pi],SP[x_,y_]->SP[y,x]};
\[CapitalGamma]0LO[pDpSq_,pD0Sq_,p\[Pi]Sq_]:=Evaluate[1/(DerivOneLoop\[CapitalSigma][mD0,mDps]+DerivOneLoop\[CapitalSigma][mDp,mD0s]) ComplexExpand[Abs[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]]^2+Abs[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]]^2-LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]Conjugate[LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]]-LODecay[g/(Sqrt[2]f\[Pi]),pD0Sq,mD0,mDps]Conjugate[LODecay[-(g/(Sqrt[2]f\[Pi])),pDpSq,mDp,mD0s]]]//.SPrule[pDpSq,pD0Sq,p\[Pi]Sq]];
(* find the normalizations *)
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mDp;
m2=m\[Pi]0;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mDp-pDpSq/(2mDp)-pD0Sq/(2mD0))^2-m\[Pi]0^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LO[pDpSq,pD0Sq,p\[Pi]Sq],{pD0Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pDpSq,p1SqMin[m1,m2,m3,pD0Sq],p1SqMax[m1,m2,m3,pD0Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mDp;
m2=m\[Pi]0;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mDp-pDpSq/(2mDp)-pD0Sq/(2mD0))^2-m\[Pi]0^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LOconst[pDpSq,pD0Sq,p\[Pi]Sq],{pD0Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pDpSq,p1SqMin[m1,m2,m3,pD0Sq],p1SqMax[m1,m2,m3,pD0Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
DateString[]
LODataNormalized1=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD0Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mDp;
m2=mD0;
m3=m\[Pi]0;
T=(mT^2-mDD^2+m\[Pi]0^2)/(2mT)-m\[Pi]0;
p\[Pi]Sq=2m3 T;
pD0Sq[pDpSq_]:=2m2(mT-m1-m2-pDpSq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pDpSq_]:=1/(32\[Pi]^3 mDD) 10^3 \[CapitalGamma]0LO[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,mD0+mDp,mT-m\[Pi]0-1,(mT-m\[Pi]0-(mD0+mDp))/100}];
DateString[]
DateString[]
LODataConstNormalized1=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD0Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mDp;
m2=mD0;
m3=m\[Pi]0;
T=(mT^2-mDD^2+m\[Pi]0^2)/(2mT)-m\[Pi]0;
p\[Pi]Sq=2m3 T;
pD0Sq[pDpSq_]:=2m2(mT-m1-m2-pDpSq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pDpSq_]:=1/(32\[Pi]^3 mDD) 10^3 13.104646941678425`(*normalization const*)/149.8992189683825` \[CapitalGamma]0LOconst[pDpSq,pD0Sq[pDpSq],p\[Pi]Sq];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,mD0+mDp,mT-m\[Pi]0-1,(mT-m\[Pi]0-(mD0+mDp))/100}];
DateString[]


(* ::Section:: *)
(*charged pion decay*)


SPrule[pD1Sq_,pD2Sq_,p\[Pi]Sq_]:={SP[\[Epsilon]T,p\[Pi]]^2->p\[Pi]Sq/3,SP[\[Epsilon]T,pD1]^2->pD1Sq/3,SP[\[Epsilon]T,pD2]^2->pD2Sq/3,SP[\[Epsilon]T,pD2]SP[\[Epsilon]T,p\[Pi]]->SP[pD2,p\[Pi]]/3,SP[\[Epsilon]T,pD1]SP[\[Epsilon]T,p\[Pi]]->SP[pD1,p\[Pi]]/3,SP[pD2,p\[Pi]]->1/2 (pD1Sq-pD2Sq-p\[Pi]Sq),SP[pD1,p\[Pi]]->1/2 (pD2Sq-pD1Sq-p\[Pi]Sq),Arg[pD2Sq]->0,Arg[pD1Sq]->0,Arg[-pD2Sq]->\[Pi],Arg[-pD1Sq]->\[Pi],SP[x_,y_]->SP[y,x]};
\[CapitalGamma]0LO[pD1Sq_,pD2Sq_,p\[Pi]Sq_]:=Evaluate[1/2 1/(DerivOneLoop\[CapitalSigma][mD0,mDps]+DerivOneLoop\[CapitalSigma][mDp,mD0s]) ComplexExpand[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]Conjugate[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]]+Abs[LODecay[g/f\[Pi],pD1Sq,mD0,mDps]]^2+LODecay[g/f\[Pi],pD1Sq,mD0,mDps]Conjugate[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]]+Abs[LODecay[g/f\[Pi],pD2Sq,mD0,mDps]]^2]//.SPrule[pD1Sq,pD2Sq,p\[Pi]Sq]];
(* find the normalizations *)
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mD0;
m2=m\[Pi]p;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mD0-pD1Sq/(2mD0)-pD2Sq/(2mD0))^2-m\[Pi]p^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LO[pD1Sq,pD2Sq,p\[Pi]Sq],{pD2Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pD1Sq,p1SqMin[m1,m2,m3,pD2Sq],p1SqMax[m1,m2,m3,pD2Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
Timing[Module[{m1,m2,m3,p\[Pi]Sq},
m1=mD0;
m2=m\[Pi]p;
m3=mD0;

p\[Pi]Sq=(mT-mD0-mD0-pD1Sq/(2mD0)-pD2Sq/(2mD0))^2-m\[Pi]p^2;NIntegrate[1/(32\[Pi]^3) 10^3 \[CapitalGamma]0LOconst[pD1Sq,pD2Sq,p\[Pi]Sq],{pD2Sq,p3SqMin[m1,m2,m3],p3SqMax[m1,m2,m3]},{pD1Sq,p1SqMin[m1,m2,m3,pD2Sq],p1SqMax[m1,m2,m3,pD2Sq]},Method->"LocalAdaptive",PrecisionGoal->2]]]
DateString[]
LODataNormalized2=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD2Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mD0;
m2=mD0;
m3=m\[Pi]p;
T=(mT^2-mDD^2+m\[Pi]p^2)/(2mT)-m\[Pi]p;
p\[Pi]Sq=2m3 T;
pD2Sq[pD1Sq_]:=2m2(mT-m1-m2-pD1Sq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pD1Sq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 \[CapitalGamma]0LO[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq]];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,2mD0,mT-m\[Pi]p-1,(mT-m\[Pi]p-2mD0)/100}];
DateString[]
DateString[]
LODataConstNormalized2=Table[{mDD,Module[{m1,m2,m3,p\[Pi]Sq,pD2Sq,T,f,a,b},
(* these masses are in a different order from earlier *)
m1=mD0;
m2=mD0;
m3=m\[Pi]p;
T=(mT^2-mDD^2+m\[Pi]p^2)/(2mT)-m\[Pi]p;
p\[Pi]Sq=2m3 T;
pD2Sq[pD1Sq_]:=2m2(mT-m1-m2-pD1Sq/(2m1)-Sqrt[2m3 T+m3^2]);
f[pD1Sq_]:=Re[1/(32\[Pi]^3 mDD) 10^3 27.699370016072265`(* normalization const*)/491.1695822520524` \[CapitalGamma]0LOconst[pD1Sq,pD2Sq[pD1Sq],p\[Pi]Sq]];
a=p1SqMin[m1,m2,m3,2m3 T];
b=p1SqMax[m1,m2,m3,2m3 T];
SimpsonsRule[f,{a,b},20]
]},{mDD,2mD0,mT-m\[Pi]p-1,(mT-m\[Pi]p-2mD0)/100}];
DateString[]
