(* -------------------------------------------------------------------- *)
require import AllCore Momemtum Distr List DList FunExt DProd.
require (*--*) FinType StdRing StdOrder.
(*---*) import StdRing.RField StdOrder.RealOrder.

  pragma +implicits.

(* Graphs *)

(* -------------------------------------------------------------------- *)
type vertex.

clone MFinite as FinVertex with type t <- vertex.

op edge : vertex -> vertex -> bool.

axiom edge_irrefl : forall x, !edge x x.
axiom edge_sym    : forall x y, edge x y => edge y x.

abbrev nvertices = FinVertex.Support.card.
abbrev vertices  = FinVertex.Support.enum.

op diameter : int.

axiom diameter_ok : forall (v : vertex), count (edge v) vertices <= diameter.

hint exact : FinVertex.Support.card_gt0.

(* Colorings *)
(* -------------------------------------------------------------------- *)
type color.

clone MFinite as FinColor with type t <- color.

abbrev ncolors = FinColor.Support.card.
abbrev colors  = FinColor.Support.enum.

(* -------------------------------------------------------------------- *)
type coloring = vertex -> color.

op valid_cond (W : coloring) (v : vertex) (c : color) =
  forall v', edge v v' => W v' <> c.

(* -------------------------------------------------------------------- *)
op adj_wit (W1 W2 : coloring) (v : vertex) (c1 c2 : color) =
  W1 v = c1 && W2 v = c2 && c1 <> c2 &&
  (forall v', W1 v' <> W2 v' => v' = v).

op adj (W1 W2 : coloring) =
  exists c, W1 c <> W2 c &&
    (forall c', W1 c' <> W2 c' => c' = c).

(* Distance and properties *)    
(* -------------------------------------------------------------------- *)
op cdiffer (W1 W2 : coloring) =
  count (fun c => W1 c <> W2 c) FinVertex.Support.enum.

lemma cdiffer_ge0 W1 W2 : 0 <= cdiffer W1 W2.
proof. exact/count_ge0. qed.

lemma cdiffer_refl W : cdiffer W W = 0.
proof. by rewrite /cdiffer count_pred0_eq. qed.

lemma cdiffer_refl_eq W1 W2 : W1 = W2 => cdiffer W1 W2 = 0.
proof. by move=> ->; apply/cdiffer_refl. qed.

lemma cdiffer_sym W1 W2 : cdiffer W1 W2 = cdiffer W2 W1.
proof. by apply/eq_count=> c /=; split=> ->. qed.

lemma cdiffer_eq1 W1 W2 : cdiffer W1 W2 = 1 <=> adj W1 W2.
proof. split.
+ case/count_eq1=> c |> hc ne_W eq; exists c; split=> //.
  move=> _ c'; apply: contraR=> ne; apply/eq => //.
  by apply FinVertex.Support.enumP.
+ case => c [ne_W h]; have: perm_eq vertices (c :: rem c vertices).
  * by apply/perm_to_rem/FinVertex.Support.enumP.
  move/perm_eqP => @/cdiffer ->/=; rewrite ne_W b2i1.
  rewrite (@eq_in_count _ pred0) ?count_pred0 //=.
  move=> y; rewrite rem_filter ?FinVertex.Support.enum_uniq.
  by rewrite mem_filter /#.
qed.

lemma cdiffer_eq0 W1 W2 : cdiffer W1 W2 = 0 => W1 = W2.
proof.
move=> h; apply/fun_ext=> c; case: (W1 c = W2 c) => // ne_W.
have hc: c \in vertices by apply FinVertex.Support.enumP.
by move: h; rewrite -count_eq0 => /hasPn /(_ c hc).
qed.

lemma cdiffer_ti W1 W2 W3 :
  cdiffer W1 W3 <= cdiffer W1 W2 + cdiffer W2 W3.
proof. by rewrite /cdiffer; elim: vertices => //= c s ih /#. qed.

lemma cdiffer_ite W1 W2 v c1 c2 :
   cdiffer
     (fun x => if x = v then c1 else W1 x)
     (fun x => if x = v then c2 else W2 x)
   <= (cdiffer W1 W2) + (b2i (c1 <> c2)).
proof.
rewrite /cdiffer (@count_rem _ _ v) ?FinVertex.Support.enumP /=.
rewrite addzC lez_add2r; pose p := fun c => W1 c <> W2 c.
apply/(@lez_trans (count p (rem v vertices))); last first.
+ by apply/count_subseq/rem_subseq.
rewrite lez_eqVlt; left; apply/eq_in_count => v' /=.
rewrite rem_filter ?FinVertex.Support.enum_uniq.
by rewrite mem_filter; case=> @/predC1 ->.
qed.

lemma cdiffer_ite' W1 W2 v c :
  cdiffer (fun x => if x = v then c else W1 x) W2 <= (cdiffer W1 W2) + 1.
proof.
have {1}->: W2 = fun x => if x = v then W2 v else W2 x.
+ by apply/fun_ext=> v'; case: (v' = v) => [->|].
apply: (@lez_trans (cdiffer W1 W2 + (b2i (c <> W2 v)))).
+ by apply/cdiffer_ite.
+ by apply/lez_add2l/b2i_le1.
qed.

lemma cdiffer_succ W1 W2 n : 0 <= n
  => cdiffer W1 W2 = n + 1
  => exists W, cdiffer W1 W = 1 /\ cdiffer W W2 = n.
proof.
move=> ge0_n eqc; have: 0 < cdiffer W1 W2 by smt().
rewrite -has_count => /hasP[c /= [hc ne_W]].
pose W := fun x => if x = c then W2 c else W1 x; exists W; do! split.
+ have: perm_eq vertices (c :: rem c vertices).
  * by apply/perm_to_rem/FinVertex.Support.enumP.
  move/perm_eqP=> -> /=; rewrite (@eq_in_count _ pred0) ?count_pred0 2:/#.
  move=> v; rewrite rem_filter ?FinVertex.Support.enum_uniq.
  by rewrite mem_filter /#.
+ have h: perm_eq vertices (c :: rem c vertices).
  * by apply/perm_to_rem/FinVertex.Support.enumP.
  move/perm_eqP: (h) => -> /=; rewrite /W b2i0 /=.
  move: eqc; move/perm_eqP: h => -> /=; rewrite ne_W b2i1.
  rewrite addzC => /addIz <-; apply/eq_in_count => /=.
  move=> c'; rewrite rem_filter ?FinVertex.Support.enum_uniq.
  by rewrite mem_filter /#.
qed.

lemma cdiffer_le1 W1 W2 v :
  (forall v', v'<> v => W1 v' = W2 v') => cdiffer W1 W2 <= 1.
proof.
move=> h; case: (W1 v = W2 v) => eq.
+ by rewrite /cdiffer count_pred0_eq //= => /#.
have: perm_eq vertices (v :: rem v vertices).
+ by apply/perm_to_rem/FinVertex.Support.enumP.
move/perm_eqP=> @/cdiffer -> /=; rewrite eq b2i1.
rewrite (@eq_in_count _ pred0) ?count_pred0 // => v'.
by rewrite rem_filter ?FinVertex.Support.enum_uniq // mem_filter /#.
qed.

hint exact : cdiffer_ge0.

(* -------------------------------------------------------------------- *)
op T0 : int.

axiom ge0_T0 : 0 <= T0.

hint exact : ge0_T0.

(* Main program. We wrap sampling in a procedure to use results from ProdSampling *)

clone ProdSampling as PS0 with
  type t1<-vertex, type t2<-color,
  op d1 <- FinVertex.dunifin, op d2 <- FinColor.dunifin.

(* -------------------------------------------------------------------- *)
module M = {
  proc f(w : coloring) : coloring = {
    var i : int;
    var v : vertex;
    var c : color;

    i <- 0;
    while (i < T0) {
       (v,c) <@ PS0.S.sample2();
      if (valid_cond w v c) {
        w <- (fun x => if x = v then c else w x);
      }
      i <- i + 1;
    }

    return w;
  }
}.

(* -------------------------------------------------------------------- *)
(* Probabilities of bad, neutral, and good events *)

op mu0 = FinVertex.dunifin `*` FinColor.dunifin.

op good w vdelta (red : color) (x : vertex * color) =
   x.`1 = vdelta /\ forall v', edge vdelta v' = true => x.`2 <> w v'.

op neutral w vdelta red (x : vertex * color) =
     (x.`1 <> vdelta \/ !valid_cond w x.`1 x.`2)
  /\ (!edge x.`1 vdelta \/ (edge x.`1 vdelta /\ x.`2 <> red)).

op bad (w : coloring) vdelta red (x : vertex * color) =
  edge x.`1 vdelta /\ x.`2 = red.

lemma good_neutral_excl w vdelta red x :
  !(good w vdelta red x /\ neutral w vdelta red x).
proof. smt. qed.

lemma neutral_bad_excl w vdelta red x :
  !(neutral w vdelta red x /\ bad w vdelta red x).
proof. smt. qed.

lemma good_bad_excl w vdelta red x :
  !(good w vdelta red x /\ bad w vdelta red x).
proof. smt. qed.

op prob0 w vdelta (red : color) =
  mu mu0 (good w vdelta red).

op prob1 w vdelta red =
  mu mu0 (neutral w vdelta red).

op prob2 (w : coloring) vdelta red =
  mu mu0 (bad w vdelta red).

lemma pr_aux w vdelta :
     (ncolors - diameter)%r / ncolors%r
  <= mu FinColor.dunifin (fun (x : color) =>
       forall (v' : vertex), edge vdelta v' = true => x <> w v').
proof.
rewrite FinColor.dunifinE ler_wpmul2r.
+ by rewrite invr_ge0 le_fromint ltzW FinColor.Support.card_gt0.
apply/le_fromint; pose p := fun (x : color) =>
  forall (v' : vertex), edge vdelta v' = true => x <> w v'.
have ->: count p colors = ncolors - count (predC p) colors.
+ smt(count_predC).
rewrite lez_add2l StdOrder.IntOrder.ler_opp2.
have ->: count (predC p) colors
  = count (fun x => exists v', edge vdelta v' /\ x = w v') colors.
+ by apply/eq_count=> /#. + smt.
qed.

lemma prob0_bound w vdelta red :
  (ncolors - diameter)%r / (ncolors * nvertices)%r <= prob0 w vdelta red.
proof.
rewrite /prob0 /mu0 =>//=; have ->:
  mu (FinVertex.dunifin `*` FinColor.dunifin)
    (fun (x : vertex * color) =>
       x.`1 = vdelta /\
       forall (v' : vertex), edge vdelta v' = true => x.`2 <> w v') =
  mu FinVertex.dunifin
    (fun x => x = vdelta) *
  mu FinColor.dunifin
    (fun x => forall (v' : vertex), edge vdelta v' = true => x <> w v').
  + by rewrite -dprodE /#.
have ->:
    (ncolors - diameter)%r / (ncolors * nvertices)%r
  = (inv nvertices%r) * ((ncolors - diameter)%r / ncolors%r) by smt().
rewrite FinVertex.dunifin1E div1r ler_wpmul2l ?invr_ge0.
+ by rewrite le_fromint ltzW.
by apply pr_aux.
qed.

lemma prob2_bound w vdelta red :
  prob2 w vdelta red = diameter%r / (ncolors * nvertices)%r.
proof.
rewrite /prob2 /mu0 =>//=; have ->:
    mu (FinVertex.dunifin `*` FinColor.dunifin)
       (fun (x : vertex * color) => edge x.`1 vdelta /\ x.`2 = red)
  = mu FinVertex.dunifin (fun x => edge x vdelta) *
    mu FinColor.dunifin  (fun x  => x = red).
+ by rewrite -dprodE /#.
by rewrite FinColor.dunifin1E; smt.
qed.

lemma prob_all w vdelta red :
  prob0 w vdelta red + prob1 w vdelta red + prob2 w vdelta red = 1%r.
proof.
rewrite -!mu_disjoint; 1,2:smt(good_neutral_excl neutral_bad_excl good_bad_excl).
pose p := predU _ _; have ->: p = predT.
+ by apply/fun_ext=> x @/p @/predT @/predU /#.
by rewrite -/(is_lossless mu0) dprod_ll !duniform_ll; smt.
qed.

op Beta =
    1%r - (ncolors - diameter)%r / (ncolors * nvertices)%r
  + diameter%r / (ncolors * nvertices)%r.

lemma beta_ok w v c : prob1 w v c + 2%r * prob2 w v c <= Beta. 
proof.
suff ->:
    prob1 w v c + 2%r * prob2 w v c
  = 1%r - prob0 w v c + prob2 w v c by smt. smt.
qed.

(* We assume that Beta is positive *)
axiom ge0_beta: 0%r <= Beta.

(* -------------------------------------------------------------------- *)
abbrev dist = fun x => exp Beta T0 * x.

lemma affine_dist : affine dist.
proof.
apply (@Affine _ (exp Beta T0) 0%r) => //.
by apply/ge0_exp/ge0_beta.
qed.
    
hint exact : affine_dist.

(* -------------------------------------------------------------------- *)
lemma Glauber : momentum [M.f ~ M.f : [dist]

     true | (cdiffer w{1} w{2})%r
  ==> true | (cdiffer res{1} res{2})%r].
proof.
proc => /=.

(* Process initialization code, rewrite distance using bigo *)
seq 1 1 : (i{1} = 0 /\ ={i})
    [(fun x => x) & dist; (cdiffer w{1} w{2})%r] => //=.
+ by auto=> &1 &2 _; rewrite le_fromint.
momentum conseq ([(bigo T0 (fun _ x => Beta * x))]
      (={i} /\ T0 - i{1} = T0 /\ 0 <= T0)
    |  (cdiffer w{1} w{2})%r
==>   (={i} /\ T0 - i{1} = 0)
    | (cdiffer w{1} w{2})%r) => //=.
  + by move => &m1 &m2 H; rewrite bigo_iter_geo //=.

(* Enter body of while rule *)
momentum while (={i})
               [fun _ x => Beta * x] (T0-i) T0 => //=.
+ by move => k H H'; apply (@Affine _ Beta 0%r); smt(ge0_beta).
+ smt().
move=> k ge0_k gt_k_T0.
momentum conseq (( ={i} /\ T0 - i{1} = k + 1)
                 ==> ( ={i} /\ T0 - i{1} = k)) => />.

(* Apply transitivity and discharge side conditions *)              
momentum transitivity => //=.
+ by apply (@Linear _  Beta); smt(ge0_beta).
+ smt.
+ by move=> &m; rewrite eq_fromint cdiffer_refl.
  + by move=> &1 &2 &3; smt(cdiffer_ti).
+ move => &m1 &m2 n [[Hi Ht] [Hpos /eq_fromint Hdiff]].
  move: (cdiffer_succ w{m1} w{m2} n Hpos Hdiff) => [W [Hn H1]].
by exists (i{m1},W) => //= /#.

(* Case distance=0, use the fact that distance 0 is equality *)
               
+ momentum conseq ((={i,w} /\ T0 - i{1} = k + 1) ==>
(={i} /\ T0 - i{1} = k)); first 5 by smt(cdiffer_eq0).
  seq 1 1: (={i, w, v, c} /\ 
  T0 - i{1} = k + 1) [(fun x => 0%r) & dist; (cdiffer w{1} w{2})%r].
  inline *; wp; rnd; rnd; skip; auto => &m1 &m2 [[_ Hw] _].
    by rewrite Hw cdiffer_refl => //=; rewrite !exp_cst /#.
  * wp; skip; auto.
    - move=> &m1 &m2 [[Hi [Hw [Hv Hc]]] Heq].
      rewrite Hi Hw Hv Hc; case: (valid_cond w{m2} v{m2} c{m2});
        by smt.
    - move=> &m1 &m2 [[Hi [Hw [Hv Hc]]] Heq];
        by rewrite Hw Hv Hc; smt.
    - smt().
  * by apply affine_dist.

(* Case distance=1*)

  (* use existential introduction to make initial values explicit *)

momentum conseq ((exists coloring vertex blue red,
     adj_wit w{1} w{2} vertex blue red /\ ={i} /\ T0 - i{1} = k + 1 /\ w{1} = coloring) ==> _ );
 first 5 by (smt(cdiffer_eq1)).
elim* => coloring vdelta blue red => //=.

(* Apply SeqCase rule and discharge side conditions *)
momentum case (fun x => Beta)  
[  (fun x => 0%r)   | (v=vdelta /\
     forall v', edge vdelta v'= true => c <> w v')  <= 1%r;
  (fun x => 1%r)   | ((v<>vdelta \/ !valid_cond w v c) /\ (!edge v vdelta \/
      (edge v vdelta /\ c <> red)))
   <= (prob1 coloring vdelta red);
    (fun x => 2%r)   | (edge v vdelta /\ c = red) <= (prob2 coloring vdelta red)]
  Beta 

( ={v,i} /\ adj_wit w{1} w{2} vdelta blue red
  /\ T0 - i{1} = k + 1 /\
  let pi = (fun x => if (edge v{1} vdelta=true) then
    if x = blue then red else (if x = red then blue else x)
    else x) in c{1}= pi c{2})
      1 1 => //=.
+ smt.
+ by apply (@Affine _ 0%r 0%r); smt().
+ by apply (@Affine _ 0%r 1%r); smt().
  + by apply (@Affine _ 0%r 2%r); smt().

(* Upper bound probabilities of neutral event. Goal is initially
stated in phoare.  Use bypr then byequiv to convert to phoare for a
single random assignment on the product distribution. Ugly, but
works *)

move => &m.
  call (_ : true ==> (res.`1 <> vdelta \/ ! valid_cond coloring res.`1  res.`2) /\
  (! edge res.`1 vdelta \/ edge res.`1 vdelta /\ res.`2 <> red)).
bypr.
move => &m' _.
have <-: (Pr[PS0.S.sample() @ &m' :
   (res.`1 <> vdelta \/ ! valid_cond coloring res.`1 res.`2) /\
   (! edge res.`1 vdelta \/ edge res.`1 vdelta /\ res.`2 <> red)] =
Pr[PS0.S.sample2() @ &m' :
   (res.`1 <> vdelta \/ ! valid_cond coloring res.`1 res.`2) /\
   (! edge res.`1 vdelta \/ edge res.`1 vdelta /\ res.`2 <> red)]).
byequiv PS0.sample_sample2 => //.
byphoare => //.
     proc.
     rnd; skip =>  //.
auto.

(* Upper bound probabilities of bad event. Goal is initially
stated in phoare.  Use bypr then byequiv to convert to phoare for a
single random assignment on the product distribution. Ugly, but
works *)
move => &m.
     call (_ : true ==>  edge res.`1 vdelta /\ res.`2 = red).
bypr.
move => &m' _.
have <-: (Pr[PS0.S.sample() @ &m' :
   edge res.`1 vdelta /\ res.`2 = red] =
Pr[PS0.S.sample2() @ &m' : edge res.`1 vdelta /\ res.`2 = red]).
byequiv PS0.sample_sample2 => //.
byphoare => //.
     proc.
     rnd; skip =>  //.
auto.

+ (* First premise of SeqCase: random sampling *)
  inline *; wp; rnd (fun x =>
    if (edge r1{1} vdelta=true) then
      if x = blue then red else (if x = red then blue else x)
    else x).
  rnd; auto; first by smt.
  by move => &m1 &m2 H //= />; rewrite !exp_cst => //=; smt.

+ (* Second premise of SeqCase: good case. Apply wp and do calculations *)
  momentum conseq ((={v, i, c} /\ adj_wit w{1} w{2} v{2} blue red /\
    T0 - i{1} = k + 1 /\ 
    forall (v' : vertex), edge v{1} v' = true => c{1} <> w{1} v') ==> _);
    first 5 by smt. 
  auto; first by smt.
  move => &m1 &m2 [[Hv [Hi Hc]] Hall] => //=.
  rewrite !Hv !Hc.
  have: (valid_cond w{m1} v{m2} c{m2} =true) by smt.
  have: (valid_cond w{m2} v{m2} c{m2}=true) by smt. 
  move => Hval Hval'; rewrite Hval Hval' => //=.
  rewrite (cdiffer_refl_eq); first by apply/fun_ext; smt.
  smt.

(* Neutral case *)
  + auto=> &m1 &m2  [[[Hv Hi] [Hwit [Ht Hc]]] [Hneutral1 Hneutral2]] => //=.
  * smt.
 +(* This rewrites the goal in a more palatable way *)
have: (cdiffer (fun (x : vertex) => if (valid_cond w{m1} v{m1} c{m1} 
&& x = v{m1}) then c{m1} else w{m1} x)
(fun (x : vertex) => if (valid_cond w{m2} v{m2} c{m2} && x = v{m2}) then c{m2} else w{m2} x) <= 1); last by (case (valid_cond w{m2} v{m2} c{m2});
case (valid_cond w{m1} v{m1} c{m1}) => //=; smt).

(* Must now proceed by case analysis *)

elim Hneutral2; move => Hedge.

(* case !edge v{m1} delta *)

move: Hc; rewrite Hedge => //=; move => Hc.


have: (valid_cond w{m1} v{m1} c{m1} <=> valid_cond w{m2} v{m2} c{m2}).
split; move => hyp v0 H0.
have: (v0 <> vdelta) by smt.
have: (w{m1} v0 = w{m2} v0) by smt.
  smt.
have: (v0 <> vdelta) by smt.
have: (w{m1} v0 = w{m2} v0) by smt.
smt.
move => Hvv.
apply (cdiffer_le1 vdelta).
move => v' Hneq => //=.
case: (valid_cond w{m1} v{m1} c{m1} && v' = v{m1}); smt.

(* case c{m1}<>red *)
move: Hedge; move => [Hedge Hcol].
move: Hc; rewrite Hedge => //=.
move => Hc.
have: (c{m2}<> blue) by smt.
move => Hblue.
move: Hc; rewrite Hblue => //=.
move => Hc.
have:((c{m2}=red/\c{m1}=blue)\/(c{m1}=c{m2}/\c{m2}<>red)) by smt.
move: {Hi}. move: {Ht}. move: {Hc}. 
move => [ [Hred' Hblue'] | [Hc Hcred]].
have: !(valid_cond w{m2} v{m2} c{m2}) by smt.
move => H'; rewrite H' => //=.
have: !(valid_cond w{m1} v{m1} c{m1}) by smt.
move => H''; rewrite H'' => //=.
apply (cdiffer_le1 vdelta).
move => v' Hneq => //=.
smt.

have: (valid_cond w{m1} v{m1} c{m1} <=> valid_cond w{m2} v{m2} c{m2}).
split; move => hyp v0 H0.
case: (v0=vdelta); last by smt.
smt.
case: (v0=vdelta); last by smt.
smt.
move => Hvalid; rewrite Hvalid.
rewrite Hv Hc.
apply (cdiffer_le1 vdelta).
move => v' Hneq => //=.
smt.

+ (* Fourth premise of SeqCase: Bad case *)
  if{1}; if{2}; auto;
    move => &m1 &m2  [[[[[Hv Hi] [Hadj H] H']] Hvc1] Hvc2] => //=.
  * smt.
  * rewrite Hv.
    move: (cdiffer_ite w{m1} w{m2} v{m2} c{m1} c{m2}).
    have: cdiffer w{m1} w{m2} = 1 by smt.
    smt.
  * smt.
  * have H1: cdiffer  w{m1} w{m2} = 1 by smt.
    have H1ite := cdiffer_ite' w{m1}  w{m2} v{m1} c{m1}.
    smt.
  * smt.
  * rewrite cdiffer_sym.
    have H1: cdiffer w{m1} w{m2} = 1 by smt.
    have H1ite := cdiffer_ite' w{m2} w{m1} v{m2} c{m2}.
    smt(cdiffer_sym).
  * smt.
  * have: cdiffer w{m1} w{m2} = 1 by smt. smt.

(* Cases are comprehensive *)

move => &m1 &m2  [[Hv Hi] H].
case: (forall (v' : vertex), edge vdelta v' = true => c{m1} <> w{m1} v') => //=; last by smt.
smt.
qed.
