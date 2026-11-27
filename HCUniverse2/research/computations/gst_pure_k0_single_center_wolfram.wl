rows = Table[
 Module[{ch, c, r = 2 p + 7, m = 2, k = 3, clearFactor = 6, f, e, ft, et, b,
   bt, expected, z, h},
  f = Join[{3}, Array[a, p]];
  e = f; e[[p + 1]] += clearFactor z;
  ft = Table[Sum[f[[j + 1]] (m h)^(i - j)/(i - j)!, {j, 0, i}], {i, 0, p}];
  et = Table[Sum[e[[j + 1]] (m h)^(i - j)/(i - j)!, {j, 0, i}], {i, 0, p}];
  b = Expand[et - ft + Join[{r}, ConstantArray[0, p]]];
  bt = Table[Sum[b[[j + 1]] (k h)^(i - j)/(i - j)!, {j, 0, i}], {i, 0, p}];
  (* Independent exponential definition of total Chern, rather than Newton. *)
  c = Coefficient[Normal@Series[
      Exp[Sum[(-1)^(i - 1) (i - 1)! bt[[i + 1]] t^i, {i, 1, p}]],
      {t, 0, p}], t, p];
  expected = Binomial[r, p] k^p h^p + (-1)^(p - 1) (p - 1)! clearFactor z;
  {p, Expand[c - expected] === 0,
   b === Join[{r}, ConstantArray[0, p - 1], {clearFactor z}]}],
 {p, 1, 10}];
{rows, And @@ Flatten[rows[[All, {2, 3}]]]} 
