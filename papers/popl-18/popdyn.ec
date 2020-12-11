(* -------------------------------------------------------------------- *)
require import AllCore Ring List FunExt.
require import Distr DInterval DList Momemtum.
import StdOrder.RealOrder StdRing.RField.


type W.
op ( +  ) : W -> W -> W.
op [ -  ] : W -> W.
op ( * ) : real -> W -> W.
abbrev (-) (x y : W) = x + -y. 
op zerow : W.

axiom addw0: right_id zerow (+).
axiom subww : forall (x : W), x - x = zerow.
axiom addC : forall (a b:W), a + b = b + a. 
axiom addA : forall (a b c:W), a + (b + c) = (a+b) + c.
axiom oppwK: forall (a:W), - - a = a.
axiom oppwD: forall (a b:W), - (a + b) = (-a) - b.
axiom mulA : forall (x y:real) (a:W), x * (y * a) = (x * y) * a. 
axiom mulD : forall x (a b:W), x * a + x * b = x * (a + b).
axiom mulO : forall x (a:W), - x * a = x * (-a).
lemma mulDM : forall x (a b:W), x * a - x * b = x * (a - b).
proof. smt (mulD mulO). qed.
axiom mul1O w : - w =  (- 1%r) * w.
lemma add0w: left_id zerow (+).
proof. by move=> x;rewrite addC addw0. qed.

op "`|_|" : W -> real.

axiom ge0_norm : forall w, 0%r <= `|w|.
axiom norm_add : forall (a b:W), `|a + b| <= `|a| + `|b|. 
axiom norm_opp : forall (a:W), `|-a| = `|a|.
axiom norm_mul : forall x (a:W), `|x * a| = `|x| * `|a|.
axiom norm_0   : `|zerow| = 0%r.

lemma norm_subC (a b:W) : `|a - b| = `|b - a|.
proof. by rewrite -norm_opp oppwD oppwK addC. qed.

op step : W -> W.
op Mult : W -> W distr.

op T : int.
axiom ge0_T : 0 <= T.
op N : int.
axiom gt0_N : 0 < N.

module Pop = {
  proc f (x:W) : W = {
    var t,j,p,z;
    t <- 0;
    while (t < T) {
      p <- step x;
      x <- zerow;
      j <- 0;
      while (j < N) {
        z <$ Mult(p);
        x <- x + 1%r/N%r * z;
        j <- j + 1;
      }
      t <- t + 1;
    }
    return x;
  }
}.

op L : real.

axiom gt0_L : 0%r < L.

pred lipschitzW k (f:W -> W) = 
    forall (x y: W), 
    `|f x - f y| <= k * `|x - y|.

axiom step_L : lipschitzW L step.

op INV (x1 x2:W) = exists p, `|x1 - x2| = p%r / N%r.

axiom INV_incr: forall x1 x2 z1 z2, INV x1 x2 => (exists p, `|z1 - z2| = p) => INV (x1 + inv N%r * z1) (x2 + inv N%r * z2).

momentum G : Pop.f ~ Pop.f : [(bigo T (fun (k:int) (x:real) => x * L))]
 INV x{1} x{2} | `|x{1} - x{2}| ==> 
 INV res{1} res{2} | `|res{1} - res{2}|.
proof.
  proc.
  seq 1 1: (INV x{1} x{2}  /\ t{1} = 0 /\ ={t}) 
   [(fun x => x) & (bigo T (fun (k:int) (x:real) => x * L)); `|x{1} - x{2}|];first 2 last.
  + done.
  + by apply bigo_affine => n Hn;apply (Affine _ L 0%r) => //;smt (gt0_L).
  + by wp;skip.
  momentum conseq ((INV x{1} x{2} /\ ={t}) /\ T - t{1} = T /\ 0 <= T ==> 
                   (INV x{1} x{2} /\ ={t}) /\ T - t{1} = 0) => />. move=> ????;apply ge0_T.
  momentum while (INV x{1} x{2} /\ ={t}) 
                 [fun (k:int) (x:real) => x * L ] (T - t) (T)=> />.
  + move=> _ _ _; apply (Affine _ L 0%r) => //;smt (gt0_L).
  + smt ().
  move=> k le0k ltkT;wp.
  pose delt := fun k x1 x2 p1 p2 => `|x1 - x2| + (k%r/N%r) * `|p1 - p2|.
  seq 3 3 : (INV x{1} x{2} /\ ={t,j,x} /\ N - j{1} = N /\ 0 <= N /\ T - t{1} = k + 1 /\ t{1} < T)
       [ (fun x => x * L) & (fun x => x); (delt N x{1} x{2} p{1} p{2})] => //=;first 2 last.
  + by apply idfun_affine.
  + auto => //=. progress. rewrite /INV subww norm_0;exists 0 => /#. smt (gt0_N).
    move=> ??;rewrite /delt subww norm_0 divrr /=;1:smt. 
    have /#:= step_L x{1} x{2}. 
  momentum conseq ([(bigo N (fun (_ : int) (x : real) => x))]
      (INV x{1} x{2} /\ ={t,j} /\ T - t{1} = k + 1 /\ t{1} < T) /\ N - j{1} = N /\ 0 <= N ==>
                   (INV x{1} x{2} /\ ={t,j} /\ T - t{1} = k + 1 /\ t{1} < T) /\ N - j{1} = 0 | delt 0 x{1} x{2} p{1} p{2}) => //;1:by smt(). 
  + by move=> &1 &2;rewrite bigo_id.
  momentum while (INV x{1} x{2} /\ ={t,j} /\ T - t{1} = k + 1 /\ t{1} < T)
                   [(fun (k:int) (x:real) => x)] (N -j) (N) & (fun n => delt n x{1} x{2} p{1} p{2}) => />.
  + by move=> ???;apply idfun_affine.
  + smt ().                     
  + move=> n le0n ltkN;wp.
  momentum conseq (_ | (1%r/N%r) * `|p{1} - p{2}| + (delt n x{1} x{2} p{1} p{2}) ==>
                   _ | (1%r/N%r) * `|z{1} - z{2}| + (delt n x{1} x{2} p{1} p{2}) ) => //=.
  + rewrite /delt => &1 &2 /> ????. smt.
  + rewrite /delt => &1 &2 /> ????.
    have -> : x{1} + inv N%r * z{1} - (x{2} + inv N%r * z{2}) = 
               (x{1} - x{2}) + inv N%r * (z{1} - z{2}).
    + rewrite -mulD -!addA;congr. 
      by rewrite addA (addC (-x{2})) -addA -mulO -oppwD.
    have := norm_add (x{1} - x{2}) (inv N%r * (z{1} - z{2})).
    rewrite norm_mul. rewrite /"`|_|".
    have -> /= /#: 0%r <= inv N%r by rewrite invr_ge0;smt (gt0_N).
  momentum FRAME  ((1%r/N%r) * `|p{1} - p{2}|) ((1%r/N%r) * `|z{1} - z{2}|) (delt n x{1} x{2} p{1} p{2}).
  momentum conseq ([fun x => x] & [1%r/N%r] true | `|p{1} - p{2}| ==> (exists p, `|z{1} - z{2}| = p) | `|z{1} - z{2}|).
  + move=> />.
  + move=> &1 &2 [#] [K] Hx !->> ??????? [p Hz] />;split.
    + by apply INV_incr;[exists K | exists p].
    smt ().  
  + smt().
  + move=> ?? _ /=; smt().
  + rewrite /= invr_ge0;smt (gt0_N).
  momentum mult Mult (fun (x y : W) => `|x - y|) => //.
  by move=> _ _ _ zL zR _; exists `|zL - zR|.
qed.
