Require FinMap.finmap.
Require FinMap.ordtype.

Require SendRec.Atom.
Require SendRec.Env.
Require SendRec.SyntaxO.
Require SendRec.TypesO.

Require dpdgraph.dpdgraph.

Set DependGraph File "Env.dpd".
Print FileDependGraph Env.

Set DependGraph File "SyntaxO.dpd".
Print FileDependGraph SyntaxO.

Set DependGraph File "TypesO.dpd".
Print FileDependGraph TypesO.

Require SendRec.SyntaxR.
Require SendRec.TypesR.
Require SendRec.SafetyR.

Set DependGraph File "SyntaxR.dpd".
Print FileDependGraph SyntaxR.

Set DependGraph File "TypesR.dpd".
Print FileDependGraph TypesR.

Set DependGraph File "SafetyR.dpd".
Print FileDependGraph SafetyR.


Set DependGraph File "SR.dpd".
Print DependGraph SendRec.SafetyR.SubjectReduction.