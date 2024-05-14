(* ::Package:: *)

(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:57fa\:672c\:5b9a\:4e49*)*)*)*)*)*)*)*)


(* ::Input::Initialization:: *)
a=o;
SuperDagger[a[x_]]=a[-x];


freeFromOp[x_]:=!MemberQ[x,o,{-1},Heads->True]


(* ::Input::Initialization:: *)
(*Power[x_o,n_]/;n>1^:=NonCommutativeMultiply@@Table[x,n](*\:5728\:8f93\:5165\:4e2d\:53ef\:4ee5\:4f7f\:7528\:7b97\:7b26\:7684\:5e42\:6b21*)
Unprotect[Power];
Power[x_,n_]/;(n>1&&MemberQ[{x},o,{-1},Heads->True]):=NonCommutativeMultiply@@Table[x,n]
Protect[Power];*)
NonCommutativeMultiplyPower[x_,n_]/;n>1:=NonCommutativeMultiply@@Table[x,n];
NonCommutativeMultiplyPower[x_,n_]/;n==0:=1;
NonCommutativeMultiplyPower[x_,n_]/;n==1:=x;
Unprotect[NonCommutativeMultiply];


(* ::Input::Initialization:: *)
Verbatim[NonCommutativeMultiply][x_]:=x;
(*ClearAttributes[NonCommutativeMultiply,Flat];*)(*\:8fd8\:662f\:4e0d\:8981\:53bb\:6389\:7ed3\:5408\:5f8b\:4e86\:ff0c\:5426\:5219\:95ee\:9898\:53d8\:5f97\:66f4\:52a0\:590d\:6742*)


(* ::Input::Initialization:: *)
grid=Column[#,Frame->All]&;


(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:5bf9\:6613\:5b50*)*)*)*)*)*)*)*)


(* ::Input::Initialization:: *)
com[a[x__],a[y__]]/;OrderedQ[{{x}[[1]],{y}[[1]]}]:=a[x]**a[y]-a[y]**a[x](*\:5b9a\:4e49\:6700\:57fa\:7840\:7684\:5bf9\:6613\:5173\:7cfb*)


(* ::Input::Initialization:: *)
com[x_,y_]/;(freeFromOp[x])||(freeFromOp[y]):=0(*\:5f53x\:6216\:8005y\:4e2d\:6709\:4e00\:4e2a\:6ca1\:6709o\:65f6\:ff0c\:5bf9\:6613\:5b50\:4e3a\:96f6*)(*\:4e00\:4e2a\:91cd\:8981\:7684\:6539\:8fdb\:ff0c\:628a\:68c0\:67e5\:6574\:4e2a\:51fd\:6570\:8868\:8fbe\:5f0f\:6539\:6210\:53ea\:7528\:68c0\:67e5\:5012\:6570\:51e0\:4e2alevel\:ff0c\:5f85\:529e*)
com[Plus[x_,y_],a_]:=com[x,a]+com[y,a]
com[a_,Plus[x_,y_]]:=com[a,x]+com[a,y]
(*com[s_,k_]:=com[Expand[s],Expand[k]]*)(*expand\:7684\:4f5c\:7528\:662f\:4ec0\:4e48\:ff1f\:4e3a\:4ec0\:4e48\:9677\:5165\:4e86\:5faa\:73af?*)
com[a_,Times[b_o,y_]]:= y com[a,b]
com[Times[x_,a_o],b_]:=x  com[a,b]


(* ::Input::Initialization:: *)
com[a_o**b_o,c_]:=a**com[b,c]+com[a,c]**b(*\:6709\:65f6\:5019\:9700\:8981\:4f7f\:7528ExpandAll\:5c06\:5b89\:6392\:66b4\:9732\:51fa\:6765\:624d\:80fd\:5e94\:7528\:8fd9\:4e2a\:89c4\:5219*)
com[a_,b_o**c_o]:=b**com[a,c]+com[a,b]**c(*\:65e2\:7136\:6709\:957f\:89c4\:5219\:ff0c\:90a3\:4e48\:77ed\:89c4\:5219\:7684\:610f\:4e49\:662f\:4ec0\:4e48\:ff1f*)
com[a:Except[__NonCommutativeMultiply],b:Except[__NonCommutativeMultiply]]/;!OrderedQ[{a[[1]],b[[1]]}]:=-com[b,a](*\:8fd4\:56de\:7279\:5b9a\:987a\:5e8f\:7684\:5bf9\:6613\:5b50\:ff0c\:907f\:514d\:9677\:5165\:65e0\:9650\:5faa\:73af*)(*\:6839\:636e\:7b2c\:4e00\:4e2a\:6570\:5b57\:5224\:65ad\:662f\:5426\:6709\:6b63\:786e\:7684\:987a\:5e8f*)
com[NonCommutativeMultiply[a_,b_,r__],c_]:=a**com[NonCommutativeMultiply[b,r],c]+NonCommutativeMultiply[com[a,c],b,r]
com[c_,NonCommutativeMultiply[a_,b_,r__]]:=a**com[c,NonCommutativeMultiply[b,r]]+NonCommutativeMultiply[com[c,a],b,r]
(*com[a:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]:=-com[b,a]*)
com[Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply],z_]:=x com[y,z]
com[z_,Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply]]:=x com[z,y]


(* ::Input::Initialization:: *)
com[x_,y_]/;MatrixQ[x]&&MatrixQ[y]&&Dimensions[x]==Dimensions[y]:=Block[{d},d=Dimensions[x][[1]];Table[Sum[x[[i,j]]**y[[j,k]]-y[[i,j]]**x[[j,k]],{j,d}],{i,d},{k,d}]]


(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:53cd\:5bf9\:6613\:5b50*)*)*)*)*)*)*)*)


(* ::Input::Initialization:: *)
acm[a[x__],a[y__]]/;OrderedQ[{{x}[[1]],{y}[[1]]}]:=a[x]**a[y]+a[y]**a[x](*\:5b9a\:4e49\:6700\:57fa\:7840\:7684\:5bf9\:6613\:5173\:7cfb*)


(* ::Input::Initialization:: *)
acm[a : Except[__NonCommutativeMultiply], b : Except[__NonCommutativeMultiply]] /; ! OrderedQ[{a[[1]], b[[1]]}] := acm[b, a](*\:8fd4\:56de\:7279\:5b9a\:987a\:5e8f\:7684\:5bf9\:6613\:5b50\:ff0c\:907f\:514d\:9677\:5165\:65e0\:9650\:5faa\:73af*)(*\:6839\:636e\:7b2c\:4e00\:4e2a\:6570\:5b57\:5224\:65ad\:662f\:5426\:6709\:6b63\:786e\:7684\:987a\:5e8f*)


(* ::Input::Initialization:: *)
acm[x_,y_]/;(freeFromOp[x])||(freeFromOp[y]):=0(*\:5f53x\:6216\:8005y\:4e2d\:6709\:4e00\:4e2a\:6ca1\:6709o\:65f6\:ff0c\:5bf9\:6613\:5b50\:4e3a\:96f6*)
acm[Plus[x_,y_],a_]:=acm[x,a]+acm[y,a]
acm[a_,Plus[x_,y_]]:=acm[a,x]+acm[a,y]
(*acm[s_,k_]:=acm[Expand[s],Expand[k]]*)(*expand\:7684\:4f5c\:7528\:662f\:4ec0\:4e48\:ff1f\:4e3a\:4ec0\:4e48\:9677\:5165\:4e86\:5faa\:73af?*)(*Expand\:7684\:4f5c\:7528\:662f\:66b4\:9732\:51fao\:ff0c\:4f7f\:5f97\:5316\:7b80\:53ef\:4ee5\:987a\:5229\:8fdb\:884c*)
acm[a_,Times[b_o,y_]]:= y acm[a,b]
acm[Times[x_,a_o],b_]:=x  acm[a,b]


(* ::Input::Initialization:: *)
acm[a_o**b_o,c_]:=a**acm[b,c]+acm[a,c]**b-2a**c**b
acm[a_,b_o**c_o]:=b**acm[a,c]+acm[a,b]**c-2b**a**c
acm[NonCommutativeMultiply[a_o,b_o,r__o],c_]:=a**acm[NonCommutativeMultiply[b,r],c]+NonCommutativeMultiply[acm[a,c],b,r]-2NonCommutativeMultiply[a,c,b,r]
acm[c_,NonCommutativeMultiply[a_,b_,r__]]:=a**acm[c,NonCommutativeMultiply[b,r]]+NonCommutativeMultiply[acm[c,a],b,r]-2NonCommutativeMultiply[a,c,b,r]
(*acm[a:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]:=-acm[b,a]*)
acm[Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply],z_]:=x acm[y,z]
acm[z_,Times[x:Except[_NonCommutativeMultiply],y_NonCommutativeMultiply]]:=x acm[z,y]


(* ::Input::Initialization:: *)
acm[x_,y_]/;MatrixQ[x]&&MatrixQ[y]&&Dimensions[x]==Dimensions[y]:=Block[{d},d=Dimensions[x][[1]];Table[Sum[x[[i,j]]**y[[j,k]]-y[[i,j]]**x[[j,k]],{j,d}],{i,d},{k,d}]]


(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:975e\:4ea4\:6362\:4e58\:6cd5 *)*)*)*)*)*)*)*)


(* ::Input:: *)
(*(*NonCommutativeMultiply[a_Plus,b_]:=Plus@@ (NonCommutativeMultiply[#, b] & /@ a);*)
(*NonCommutativeMultiply[a_, b_Plus] := Plus @@ (NonCommutativeMultiply[a, #] & /@ b);*)*)


(* ::Input::Initialization:: *)
NonCommutativeMultiply[a_Plus,b_]:= NonCommutativeMultiply[#, b] & /@ a;
NonCommutativeMultiply[a_, b_Plus] :=  NonCommutativeMultiply[a, #] & /@ b;
NonCommutativeMultiply[a_,Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_NonCommutativeMultiply],b_NonCommutativeMultiply],a_]:=c NonCommutativeMultiply[b,a]
NonCommutativeMultiply[a_,Times[c:Except[_o],b_o]]:=c NonCommutativeMultiply[a,b]
NonCommutativeMultiply[Times[c:Except[_o],b_o],a_]:=c NonCommutativeMultiply[b,a]


(*cNumberExtract[x_]:=x/.HoldPattern[NonCommutativeMultiply[m__]]:>Times@@Cases[NonCommutativeMultiply[m],y:Except[_o]] NonCommutativeMultiply@@Cases[NonCommutativeMultiply[m],y_o]*)


(* ::Input::Initialization:: *)
cNumberExtractRule[x_]:=x/.HoldPattern[NonCommutativeMultiply[m__]]:>Times@@Cases[NonCommutativeMultiply[m],y_/;freeFromOp[y]] NonCommutativeMultiply@@Cases[NonCommutativeMultiply[m],y_/;Not[freeFromOp[y]]]
cNumberExtract[x_]:=cNumberExtractRule//@x;
cex=cNumberExtract;
sim[x_]:=x/.NonCommutativeMultiply[]->1


(* ::Section:: *)
(*\:7edd\:5bf9\:503c*)


Unprotect[Abs];
Abs/:MakeBoxes[Abs[x_],StandardForm]:=TemplateBox[{Parenthesize[x,StandardForm,Power]},"Abs",DisplayFunction->(RowBox[{"|",#1,"|"}]&)]
Protect[Abs];


(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:5171\:8f6d\:8f6c\:7f6e*)*)*)*)*)*)*)*)


(* ::Input::Initialization:: *)
Unprotect[Conjugate];
Conjugate/:MakeBoxes[Conjugate[x_],StandardForm]:=TemplateBox[{Parenthesize[x,StandardForm,Power]},"Conjugate",DisplayFunction->(SuperscriptBox[#1,"*"]&)]
Protect[Conjugate];


(* ::Input::Initialization:: *)
SuperDagger[((f:(Times|Plus|NonCommutativeMultiply))[x__]|Subscript)]/;Not[f===o]:=SuperDagger[#]&/@f@@Reverse[{x}](*\:8ba9dagger\:7a7f\:900f\:6240\:6709\:7684\:51fd\:6570\:5934\:ff0c\:9664\:4e86o*)


(* ::Input::Initialization:: *)
SuperDagger[o[x__]]:=o@@Flatten[{-{x}[[1]],{x}[[2;;-1]]}]


(* ::Input:: *)
(*(*((f_)[x__])^\[Dagger]/;Not[f===o]&&MemberQ[Attributes[f],Orderless]:=#^\[Dagger]&/@f[x](*\:52a0\:4e0a\:5224\:65ad\:ff0c\:5982\:679c\:6709orderless\:5c31\:4e0d\:7528\:6267\:884creverse*)*)
(*((f_)[x__])^\[Dagger]/;Not[f===o]&&Not[MemberQ[Attributes[f],Orderless]]:=#^\[Dagger]&/@f@@Reverse[{x}]*)*)


(* ::Input::Initialization:: *)
SuperDagger[(x:Except[_o])]:=Conjugate[x]


(* ::Input:: *)
(*(*x_^\[Dagger]/;NumberQ[x]:=Conjugate@x*)*)


(* ::Input:: *)
(*(*(x:Except[_o])^\[Dagger]^\[Dagger]:=x*)*)


SuperDagger[x__]:=Sequence@@(SuperDagger/@{x})(*\:53ef\:80fd\:4f1a\:5b58\:5728\:95ee\:9898*)


(* ::Section::Initialization:: *)
(*(*(*(*(*(*(*(*\:5316\:7b80\:4e0e\:5c55\:793a\:8868\:8fbe\:5f0f*)*)*)*)*)*)*)*)


(* ::Input::Initialization:: *)
(*sim[p_]:=p/.NonCommutativeMultiply[x_]:>x;(*\:7b2c\:4e8c\:4e2a\:89c4\:5219\:7684\:4f5c\:7528\:662f\:5c06\:591a\:4e2a\:7b97\:7b26\:7684\:4e58\:79ef\:5c55\:793a\:4e3a\:5e42\:6b21*)*)


(* ::Input::Initialization:: *)
dis[p_]:=p//.{o[x__]/;{x}[[1]]>0:>Subscript[HoldForm@a,If[Length[{x}]>=2,Sequence@@({Abs[{x}[[1]]]}~Join~{x}[[2;;-1]]),Abs[x]]],o[x__]/;{x}[[1]]<0:>Power[Subscript[HoldForm@a,If[Length[{x}]>=2,Sequence@@({Abs[{x}[[1]]]}~Join~{x}[[2;;-1]])(*Row[({Abs[{x}[[1]]]}~Join~{x}[[2;;-1]]),","]*),Abs[x]]],HoldForm@\[Dagger]],HoldPattern[NonCommutativeMultiply[x__]]:>Row[{x}]} ;
(*\:5c06\:975e\:4ea4\:6362\:4e58\:6cd5\:91cc\:9762\:7684\:5143\:7d20\:4ee5\:884c\:7684\:5f62\:5f0f\:5c55\:793a\:ff0c\:5e76\:4e14\:5c06o\:66ff\:6362\:4e3a\:53ef\:8bfb\:6027\:597d\:7684\:5f62\:5f0f*)


(* ::Input::Initialization:: *)
col[p_]:=p//.HoldPattern[z___**x__o]/;Length[{x}]>1&&(SameQ@@((Part[#,1;;-1]&/@{x}))):>z**Superscript[o@@({x}[[1,1;;-1]]),Length[{x}]]//.HoldPattern[x__o**y___]/;SameQ@@((Part[#,1;;-1]&/@{x}))&&Length[{x}]>1:>Superscript[o@@({x}[[1,1;;-1]]),Length[{x}]]**y;
