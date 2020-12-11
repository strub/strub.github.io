(* -------------------------------------------------------------------- *)
require import AllCore Ring List FunExt.
require import Distr DInterval DList Momemtum.
import StdOrder.RealOrder StdRing.RField.

axiom square_le : forall (a b:real), 0%r <= a => 0%r <= b => a * a <= b * b => a <= b.
axiom exp_cst (d:'a distr) c: E d (fun _ => c) = c * mu d predT.


(* Partial axiomatization of vector spaces and norms       *)
(* -------------------------------------------------------------------- *)

type W. (* Parameter space, R^d in paper *)

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

(* Scalar product and norm *)

op scal: W -> W -> real.

axiom scalC : forall (a b:W), scal a b = scal b a.
axiom scal_add_l : forall (a b c:W), scal (a + b) c = scal a c + scal b c.
axiom scalO_l : forall (a b:W), scal (-a) b = - scal a b.
axiom scal_mul_l : forall x a b, scal (x * a) b = x * scal a b.

lemma scal_add_r (a b c:W): scal c (a + b) = scal c a + scal c b.
proof. smt (scalC scal_add_l). qed.

lemma scalO_r : forall (a b:W), scal a (-b) = - scal a b.
proof. smt (scalC scalO_l). qed.

op "`|_|" : W -> real.

axiom ge0_norm : forall w, 0%r <= `|w|.
axiom norm_add : forall (a b:W), `|a + b| <= `|a| + `|b|. 
axiom norm_opp : forall (a:W), `|-a| = `|a|.
axiom norm_mul : forall x (a:W), `|x * a| = `|x| * `|a|.
axiom norm_0   : forall (a:W), `|a - a| = 0%r.

axiom scal2 : forall (a:W), scal a a = `|a|*`|a|.

axiom norm_add_sq : forall (a b:W), `| a - b| * `|a - b| = `|a|*`|a| + `|b|*`|b| - 2%r * scal a b.


lemma sub_distr: forall (a b c d:W), (a - b) - (c - d) = (a - c) + (d - b).
    proof. smt (addC addA oppwK oppwD). qed.
  

axiom cauchy_schwartz : forall (a b:W), scal a b <= `|a|*`|b|.

(* Partial axiomatization of gradients      *)
(* -------------------------------------------------------------------- *) 
(* Gradient function *)

op G : (W -> real) -> W -> W.

axiom G_add : forall (f1 f2: W -> real) w, G (fun x => f1 x + f2 x) w = G f1 w + G f2 w.
axiom G_mul : forall (f:W -> real) c w, G (fun x => c * f x) w = c * G f w.

lemma G_opp : forall (f: W -> real) w , G (fun x => - f x) w = - G f w.
proof. move=> f w;rewrite mul1O -G_mul;congr;apply fun_ext => z;ring. qed.

lemma G_sub : forall (f1 f2: W -> real) w, G (fun x => f1 x - f2 x) w = G f1 w - G f2 w.
proof. by move=> f1 f2 w;rewrite G_add G_opp. qed.

axiom G_scalx : forall w, G (fun x => scal x x) w = 2%r * w.
axiom G_scalc : forall c a, G (fun x => scal c x) a = c.


(* Monotone, convex and Lipschitz functions *)
pred monotone (f:W->W) = 
  forall a b, 0%r <= scal (f a - f b) (a - b).

pred convex (f:W -> real) =
  forall a b,
  scal (G f a) (b - a) <= f b - f a.

lemma conv_mon (f:W->real): convex f => monotone (G f).
proof.
  rewrite /convex /monotone=> H a b.
  have Hab := H a b; have Hba := H b a.
  rewrite scal_add_l scalO_l.
  have Heq : (b - a) = -(a - b).
  + by rewrite oppwD oppwK addC.
  smt (scalO_r).
qed.

(* Axiom: if G f is monotone then f is convex *)

axiom mon_conv (f:W->real) : monotone (G f) => convex f.

pred lipschitzR k (f:W -> real) = 
    forall (x y: W), 
    `|f x - f y| <= k * `|x - y|.

(* Axiom: if f is L-Lipschitz then its gradient is upper bounded by L *)

axiom lipschitzR_grad : 
   forall L f w, lipschitzR L f => `|G f w| <= L.

pred lipschitzW k (f:W -> W) = 
    forall (x y: W), 
    `|f x - f y| <= k * `|x - y|.

pred smooth k (f:W -> real) = lipschitzW k (G f).

(* -------------------------------------------------------------------- *)

(* Key technical lemma, not explicit in original paper *)

lemma lemma1 (f:W->real) B:
   0%r < B =>
   convex f => 
   smooth B f =>
   forall a b, 
     1%r/B * (`|G f a - G f b| * `|G f a - G f b|) <= scal (G f a - G f b) (a - b).
proof.
  move=> HB Hyp_conv Hyp_smo.
  pose F := fun w t =>  f t - scal (G f w) t.
  have Fmin: forall w t, F w w <= F w t.
  + by move=> w t; have := Hyp_conv w t;rewrite scal_add_r scalO_r /#.
  have Fsmo : forall w, smooth B (F w).
  + move=> w x y; rewrite /F !G_sub !G_scalc; have := Hyp_smo x y.
    have -> // : G f x - G f w - (G f y - G f w) =  G f x - G f y.
    by rewrite oppwD oppwK (addC (- G f y)) addA addC -addA (addC (- G f w)) subww addw0 addC.
  pose H := fun w t => B/2%r * scal t t - F w t.
  have Hconv: forall w, convex (H w).  
  + move=> w;apply mon_conv => x y. 
    rewrite /H !(G_sub (fun t => B / 2%r * scal t t)).
    rewrite !scal_add_l !scalO_l !G_mul !G_scalx scal_add_l scalO_l.
    rewrite !scal_mul_l.
    have Heq1 : forall (x:real), (B / 2%r * (2%r * x)) = B * x by move=> ?;field.
    rewrite !Heq1.
    have -> : B * scal x (x - y) - scal (G (fun (x0 : W) => F w x0) x) (x - y) -
          (B * scal y (x - y) - scal (G (fun (x0 : W) => F w x0) y) (x - y)) =
           B * (scal x (x - y)  - scal y (x - y)) - 
           (scal (G (fun (x0 : W) => F w x0) x) (x - y) - scal (G (fun (x0 : W) => F w x0) y) (x - y)) by ring.
    rewrite -scalO_l -scal_add_l subr_ge0 -scalO_l -scal_add_l scal2.
    apply (ler_trans _ _ _ (cauchy_schwartz (G (fun (x0 : W) => F w x0) x - G (fun (x0 : W) => F w x0) y) (x - y))).
    rewrite mulrA;apply ler_wpmul2r;[ by apply ge0_norm | by apply Fsmo].
  have Fbound: forall w x y, F w x - F w y <= scal (G (F w) y) (x - y) + B/2%r * `|x-y| * `|x-y|.
  + move=> w x y; have := Hconv w y x;rewrite /H. 
    have -> : B / 2%r * scal x x - F w x - (B / 2%r * scal y y - F w y) = 
              B / 2%r * (scal x x - scal y y) - (F w x - F w y) by ring.
    rewrite ler_subr_addl -ler_subr_addr G_sub G_mul G_scalx scal_add_l !scal_mul_l scalO_l.
    rewrite -(scalO_r _ (x - y)) (opprD (B / 2%r * (2%r * scal y (x - y)))).
    rewrite addrA scalO_r.
    have ->: B / 2%r * (scal x x - scal y y) - (B / 2%r * (2%r * scal y (x - y))) = 
           B / 2%r * `|x - y| * `|x - y|.
    + by rewrite -(mulrA (B/2%r) `|x - y|) norm_add_sq scal_add_r scalO_r !scal2 scalC;field.
    by rewrite opprK (addrC (B / 2%r * `|x - y| * `|x - y|)) //.
  have Fbound2 : forall  w x, 1%r/(2%r*B) * `|G (F w) x| * `|G (F w) x| <= F w x - F w w.
  + move=> w x.
    have := Fbound w (x - 1%r/B * G (F w) x) x.
    have -> /#: scal (G (F w) x) (x - 1%r / B * G (F w) x - x) +
                 B / 2%r * `|x - 1%r / B * G (F w) x - x| * `|x - 1%r / B * G (F w) x - x| =
              -1%r/(2%r * B) * `|G (F w) x| * `|G (F w) x|.
    have -> : x - 1%r / B * G (F w) x - x = - 1%r / B * G (F w) x.
    + by rewrite -addA addC -addA (addC (-x)) subww addw0.
    rewrite scalC scalO_l scal_mul_l scal2 norm_opp norm_mul.
    have -> : `|1%r / B|  = 1%r / B by smt ().
    by field => // /#. 
  move=> x y. 
  have := ler_add _ _ _ _ (Fbound2 x y) (Fbound2 y x).
  rewrite /F !(G_sub, G_scalc) -norm_opp oppwD (addC (- G f y)) oppwK.
  by rewrite !(scal_add_l, scal_add_r, scalO_l, scalO_r) /#. 
qed.

(* Main proof *)

type Z. (* Example space *)

op a : int -> real. (* alpha in paper *)
op l : Z -> W -> real. (* loss function *)
op T : int.
op L : real.

axiom gt0_L : 0%r < L.
axiom l_L : forall z, lipschitzR L (l z).

op gamma : real. 
axiom gamma_bound : 
  forall c, 0 <= c < T => 
  2%r * `|a c| * L <= gamma.

op n : int.
axiom gt0_n : 0 < n.

op j : int.
axiom j_bounded : 1 <= j <= n.

axiom gt0_T : 0 < T.
axiom gt0_gamma : 0%r < gamma.

op beta_ =  (4%r * L)/gamma.

axiom smooth_l z : smooth beta_ (l z).
axiom convex_l z : convex (l z).

axiom ge0_a w : 0%r <= a w.

(* -------------------------------------------------------------------- *)
module M = {
  proc sgd(w0 : W, z : Z list) : W = {
    var w : W  = w0;
    var i : int;
    var c : int = 0;
    var g : W;
    

    while (c < T) {
      i <$ [1..(size z)];
      g <- G (l (nth witness z i)) w;
      w <- w - a c * g;
      c <- c + 1;
    }

    return w;
  }
}.

(* -------------------------------------------------------------------- *)

pred adj j (l1 l2: Z list) = 
  size l1 = size l2 /\
  forall i, i <> j => nth witness l1 i = nth witness l2 i.

(* Main result from Section 2: convex SGD is stable *)

momentum sgd_stable: M.sgd ~ M.sgd : [(fun (x:real) => x + T%r * gamma / n%r)]
  ={w0} /\ adj j z{1} z{2} /\ size z{1} = n | 0%r ==> true | `|res{2} - res{1}|.
proof.
proc=> /=.

(* Process the initialization code, rewrite distance using bigo, discharge side conditions *)
seq 2 2: (c{1} = 0 /\ ={w,c} /\  adj j z{1} z{2} /\ size z{1} = n) 
[(fun x => x) & (bigo T (fun (k:int) (x:real) => x + gamma / n%r)); 0%r];first 2 last.
move => x; rewrite (bigo_iter_shift T x). smt(gt0_T).
+ by done.
+ apply bigo_affine => p Hp.
  apply (Affine _ 1%r  (gamma / n%r)) => //.
  apply divr_ge0;first smt (gt0_gamma). 
  by apply le_fromint;smt (gt0_n).
+ by auto.
momentum conseq 
  ( ((={c} /\ adj j z{1} z{2} /\ size z{1} = n) /\ T - c{1} = T /\ 0 <= T) | `|w{2} - w{1}|  ==> 
    ((={c} /\ adj j z{1} z{2} /\ size z{1} = n) /\ T - c{1} = 0) ) => //.
+ move=> />;smt (gt0_T). 
      + by move=> />;rewrite norm_0.

(* Enter the body of the while loop *)
  
momentum while (={c} /\ adj j z{1} z{2} /\ size z{1} = n) 
                 [fun (k:int) (x:real) => x + gamma / n%r ] (T - c) (T)=> />.
+ move=> k H0k HkT.
  apply (Affine _ 1%r  (gamma / n%r)) => //.
  apply divr_ge0;first smt (gt0_gamma). 
  by apply le_fromint;smt (gt0_n).
+ smt ml=0.
move=> k le0k lekT.

(* Prepare for and apply SeqCase *)
                 
momentum conseq ([fun (x : real) =>
              1%r / n%r *
              transpose Real.(+) gamma ((fun (x0 : real) => x0) x) +
              (1%r - 1%r / n%r) *
              (fun (x0 : real) => x0) ((fun (x0 : real) => x0) x)]) => //=.
+ move=> &m1 &m2 /#. 
momentum case 
(fun x => x)  
[ (fun x => x + gamma) | (i = j) <= (1%r/n%r) ;
  (fun x => x) <= (1%r - 1%r/n%r)]
  `|w{2} - w{1}|
  (={c,i} /\ adj j z{1} z{2} /\ size z{1} = n /\ T - c{1} = k + 1)
  1 1 => //=.
+ by apply (Affine _ 1%r gamma) => //;smt (gt0_gamma).
    + by apply (Affine _ 1%r 0%r).

(* Bound probability of events *)  
+ move=> &m2.
  rnd (fun i => i = j);skip => />.
  move=> &hr _ _ -> _ _.
  by have := dinter1E 1 n j;rewrite /mu_x /pred1 j_bounded /= /#.
+ move=> &m2.
  rnd (fun i => i <> j);skip => />.
  move=> &hr _ _ -> _ _.
  have -> : mu [1..n] (fun (i : int) => i <> j) = mu [1..n] (predC (pred1 j)) by done.
  have := dinter1E 1 n j;rewrite /mu_x /pred1 j_bounded /=.
    by have := weight_dinter 1 n; rewrite mu_not /weight => -> /#.

(* First premise of SeqCase, sample i *) 
+ rnd;skip=> /> &m1 &m2.
  + move=> <- //.
  rewrite exp_cst.
  have := (weight_dinter 1 (size z{m1}));rewrite /weight => -> ??.
  move=> ?;have -> : 1 <= size z{m1} by smt (gt0_n).
    by rewrite b2r1.

(* Second premise of SeqCase, rest of code, assuming i{1}=j. Apply wp and do calculaionts*)  
  
+ wp; skip => />.
  + by move=> /#.
  + move=> &m1 &m2 H1 H2 H3.
    rewrite sub_distr.
    have := norm_add (w{m2} - w{m1}) ((a c{m2} * G (l (nth witness z{m1} j)) w{m1} -
              a c{m2} * G (l (nth witness z{m2} j)) w{m2})).
    have := norm_add (a c{m2} * G (l (nth witness z{m1} j)) w{m1}) 
              (- a c{m2} * G (l (nth witness z{m2} j)) w{m2}).
    rewrite norm_opp !norm_mul.
    have := lipschitzR_grad L (l (nth witness z{m1} j)) w{m1} (l_L (nth witness z{m1} j)).
    have := lipschitzR_grad L (l (nth witness z{m2} j)) w{m2} (l_L (nth witness z{m2} j)).
                smt (gamma_bound).

(* Second premise of SeqCase, rest of code, assuming i{1}<>j. Apply wp and do calculaionts*)               
              
wp;skip=> //=.
+ move=> /#.
move=> /= &m1 &m2 [#] <- <- []_ Hadj _ _ Hdiff.
rewrite (Hadj _ Hdiff).
have -> : w{m2} - a c{m1} * G (l (nth witness z{m2} i{m1})) w{m2} -
          (w{m1} - a c{m1} * G (l (nth witness z{m2} i{m1})) w{m1}) = 
          (w{m2} - w{m1}) - a c{m1} * (G (l (nth witness z{m2} i{m1})) w{m2} 
                                       - G (l (nth witness z{m2} i{m1})) w{m1}). 
+ by rewrite -mulDM !oppwD oppwK -!addA;congr;rewrite addC -!addA;congr;rewrite addC. 
apply square_le;1,2:by apply ge0_norm.
rewrite norm_add_sq norm_mul scalC.
have := smooth_l (nth witness z{m2} i{m1}); have := convex_l (nth witness z{m2} i{m1}).
pose f := (l (nth witness z{m2} i{m1}));move=> Hc Hs.
have gt0_beta : 0%r < beta_.
+ apply divr_gt0;first by by apply mulr_gt0 => //;apply gt0_L.
  by apply gt0_gamma.
have H := lemma1 f beta_ gt0_beta Hc Hs w{m2} w{m1}.
rewrite scal_mul_l.
have -> : `|a c{m1}| * `|G f w{m2} - G f w{m1}| * (`|a c{m1}| * `|G f w{m2} - G f w{m1}|) =
      a c{m1} * a c{m1} * `|G f w{m2} - G f w{m1}| * `|G f w{m2} - G f w{m1}| by smt ().
have -> : `|w{m2} - w{m1}| * `|w{m2} - w{m1}| +
        a c{m1} * a c{m1} * `|G f w{m2} - G f w{m1}| * `|G f w{m2} - G f w{m1}| -
        2%r * (a c{m1} * scal (G f w{m2} - G f w{m1}) (w{m2} - w{m1})) =
       `|w{m2} - w{m1}| * `|w{m2} - w{m1}| +
       a c{m1} * (a c{m1} * (`|G f w{m2} - G f w{m1}| *  `|G f w{m2} - G f w{m1}|) -
                       2%r * scal (G f w{m2} - G f w{m1}) (w{m2} - w{m1})) by ring.
apply (ler_trans (
  `|w{m2} - w{m1}| * `|w{m2} - w{m1}| +
   a c{m1} * (a c{m1} * (`|G f w{m2} - G f w{m1}| * `|G f w{m2} - G f w{m1}|) -
             2%r * 1%r / beta_ * (`|G f w{m2} - G f w{m1}| * `|G f w{m2} - G f w{m1}|)))).
+ apply ler_add => //; apply ler_wpmul2l;first by apply ge0_a.
  by apply ler_add => //;rewrite ler_opp2 -!mulrA; apply ler_wpmul2l.
apply ger_addl;apply mulr_ge0_le0;first by apply ge0_a.
rewrite ler_subl_addl /=.
pose GG := (`|G f w{m2} - G f w{m1}| * `|G f w{m2} - G f w{m1}|).
have : 0%r <= GG by apply mulr_ge0;apply ge0_norm.
move:GG => GG GG0;rewrite (mulrC (2%r * GG)) mulrA. 
apply ler_wpmul2r => //.
have -> : a c{m1} = `|a c{m1}| by smt (ge0_a).
rewrite ler_pdivl_mull //;rewrite /beta_.
have H1 := gamma_bound c{m1} _;first by smt().
rewrite -mulrA (mulrC (inv gamma)) mulrA ler_pdivr_mulr 1:gt0_gamma /#. 
qed.
