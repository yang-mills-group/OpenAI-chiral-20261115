import YM.SU5.FiniteGaugeData.ArchiveK.Polecat
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
attribute [local instance] opCStarAlgebra
variable (G:E4 ≃ₗᵢ[ℝ] E4) (r:ℝ)
namespace LightK
abbrev Plate(r:ℝ):= {x: Space3 // x∈ Metric.closedBall (0:Space3) r}
protected lemma resident : CompactSpace (Plate r):= isCompact_iff_compactSpace.mp (isCompact_closedBall ..)
attribute [local instance] LightK.resident
local notation "Υ"=> Plate r
local notation "Φ"=> ContinuousMap (Plate r) ℂ
def bud(i:Cover): ContinuousMap (Plate r) ℂ:= ⟨fun x=> gust G x.val i,(gust_safe G i).comp continuous_subtype_val⟩
-- cabin via Submodule.span.B better than conform.
def Cabin(G:E4 ≃ₗᵢ[ℝ] E4)(r:ℝ) := Submodule.span ℂ (Set.range (bud G r))
lemma cabin (b:Cover): bud G r b∈ Cabin G r:= Submodule.subset_span ⟨b,rfl⟩
variable {G r}
lemma enter (x y:Cover): bud G r x * bud G r y=bud G r (x+y):=by ext1 p; change gust G p.val x*gust G p.val y=_; exact (mode_shift _ x y).symm
open scoped Classical
lemma bond1 : bud G r (0:Cover)=1:= by ext1; exact mode_zero _
-- show Subalgebra.
lemma cabin_mul (A B:Φ)(h:A∈Cabin G r)(t:B∈Cabin G r): A*B∈Cabin G r:= by
 let X:= Cabin G r; have he (i:Cover)(x:Φ)(v:x∈X): bud G r i * x∈X:= by
    refine Submodule.span_induction (p:=fun y _=>bud G r i*y∈ X) ?_ ?_ ?_ ?_ v; · rintro x ⟨j,rfl⟩; rw [enter]; exact cabin G r _
    · rw [mul_zero]; exact X.zero_mem
    · intro f g hf hg hh hr; rw [mul_add]; exact X.add_mem hh hr
    intro a f g hf; rw [mul_smul_comm]; exact X.smul_mem _ hf
 refine Submodule.span_induction (p:=fun y _=> y*B∈X) ?_ ?_ ?_ ?_ h; · rintro y ⟨i,rfl⟩; exact he i B t
 · rw [zero_mul]; exact X.zero_mem
 · intro f g hf hg hy hz; rw [add_mul]; exact X.add_mem hy hz
 intro a f g hf; rw [smul_mul_assoc]; exact X.smul_mem _ hf
def Cab (G:E4 ≃ₗᵢ[ℝ] E4)(r:ℝ): Subalgebra ℂ (ContinuousMap (Plate r) ℂ):= (Cabin G r).toSubalgebra (bond1 ▸ cabin G r 0) (cabin_mul (G:=G)) -- tune.
lemma Cab_entry (i:Cover): bud G r i∈ Cab G r:= cabin G r i
abbrev Cof (G:E4≃ₗᵢ[ℝ] E4) (r:ℝ):= (Cab G r).topologicalClosure
variable {D m:ℕ} (K:ZephyrG G D m)
open ContinuousMap
-- special 'real normal' zeta compact. ℂ-valued real argument. polynomial composed.
def buoy (p:Plate r):ℝ:= Real.exp (-(D:ℝ)*‖p.val‖) -- D implicit
@[fun_prop] lemma buoy_c : Continuous (@buoy r D):=by unfold buoy; fun_prop
open Polynomial
include K
local notation "zκ"=> runeX K 3
def mere (F:Polynomial ℝ) :Φ:= ⟨fun x=> ((F.eval (buoy (D:=D) x) : ℝ):ℂ), Complex.continuous_ofReal.comp (F.continuous.comp buoy_c)⟩
lemma buoy_mem(F:Polynomial ℝ): mere (r:=r) (D:=D) F∈Cab G r:=by
 let A:= Cab G r; let P :=@mere r D; induction F using Polynomial.induction_on' with
 | add f g hf hg=>
   change P (f+g)∈A; have he:P (f+g)=P f+ P g:=by ext1 x; simp [P,mere, eval_add,ContinuousMap.add_apply]; -- tune
   rw [he]; exact A.add_mem hf hg
 | monomial n c =>
   let Y:= bud G r zκ; have ht:P (Polynomial.monomial n c) = (c:ℂ) • Y^n:=by ext1 x; simp [P,mere, Y, bud, eval_monomial,Gust_t x.val K,buoy] -- tune simp.t
   change P _∈A; rw [ht]; exact A.smul_mem (A.pow_mem (Cab_entry _) _) _ -- arg order
#check exists_polynomial_near_of_continuousOn
lemma conjugate_b {i:Cover} : star (bud G r i) ∈ Cof G r:= by
 let A:= Cof G r; let MU:= bud G r (-i); let z:= @buoy r D; let a:ℝ:= depthG G (emitX i); let f(x:ℝ):= Real.exp ((2*a/D)*Real.log x); let g:= Real.exp (-(D:ℝ)*r); have he:= (show 0<(D:ℝ) from Nat.cast_pos.mpr K.unitC); have hb(p:Υ): z p∈Set.Icc g 1:= by
    unfold z buoy; refine ⟨Real.exp_monotone ?_,Real.exp_le_one_iff.mpr ?_⟩; · exact mul_le_mul_of_nonpos_left (mem_closedBall_zero_iff.mp p.property) (by linarith only [he]); -- precedence
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he.le) (norm_nonneg p.val)
 have hx: ContinuousOn f (Set.Icc g 1):= (Real.continuous_exp.continuousOn.comp ((continuousOn_const.mul (Real.continuousOn_log.mono (fun i v=>(show i≠0 from ((Real.exp_pos _).trans_le v.1).ne'))))) (Set.mapsTo_univ ..)); -- tune contOn
 let Y:Φ:= ⟨fun p=> (f (z p):ℂ), by apply Continuous.comp Complex.continuous_ofReal; exact hx.comp_continuous buoy_c hb⟩ -- tune.
 have hp: star (bud G r i)=Y*MU:=by ext1 x; change star (gust G x.val i)= ↑(f (z x))* gust G x.val (-i); rw [GustZ G x.val]; apply congrArg (fun z:ℝ=> (z:ℂ)*_); unfold f z buoy a; rw [Real.log_exp]; congr 1; field_simp
 rw [hp]; apply A.mul_mem _ ((Cab G r).le_topologicalClosure (Cab_entry _)); refine Metric.mem_closure_iff.mpr ?_; intro ε e; obtain ⟨v,h⟩:= exists_polynomial_near_of_continuousOn g 1 f hx ε e; let U:= mere (r:=r) (D:=D) v; refine ⟨U,buoy_mem K _,?_⟩; rw [dist_comm,dist_eq_norm]; apply (ContinuousMap.norm_lt_iff _ e).mpr; intro i; change ‖(((v.eval (z i):ℝ):ℂ))-↑(f (z i))‖ < ε; rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact h _ (hb i)
private lemma star_stow : ∀ x∈Cab G r, star x∈ Cof G r:=by
 intro x hx; let A:= Cof G r; refine Submodule.span_induction (p:=fun z _=> star z∈A) (fun i v=>?_ ) ?_ ?_ ?_ (show x∈ Cabin G r from hx); · obtain ⟨i,rfl⟩:= v; exact conjugate_b K
 · rw [star_zero]; exact A.zero_mem
 · intro i j hi hj p q; rw [star_add]; exact A.add_mem p q
 intro u i h v; rw [star_smul]; exact A.smul_mem v _
omit K in
private def opal (S:ZephyrG G D m) : StarSubalgebra ℂ Φ:= {
 (Cof G r) with
 star_mem':= by
    let A:=Cof G r; intro x h
    change star x∈ ((Cab G r).topologicalClosure:Set Φ); exact Set.MapsTo.closure_left (f:=star) (s:= (Cab G r :Set Φ)) (t:=((Cab G r).topologicalClosure : Set Φ)) (fun i v=>star_stow S _ v) continuous_star (Cab G r).isClosed_topologicalClosure h }
-- firewall use generic closure upgrade.Spot kernel definition heartbeat.

set_option maxHeartbeats 9500 in
omit K in
private lemma first_top(Y:Type) {R:Type*}[RCLike R][TopologicalSpace Y][CompactSpace Y](A: StarSubalgebra R (ContinuousMap Y R))(v:IsClosed (A.toSubalgebra : Set (ContinuousMap Y R))): A.topologicalClosure=A:=
 le_antisymm (StarSubalgebra.topologicalClosure_minimal (s:=A) (t:=A) le_rfl v) A.le_topologicalClosure
set_option maxHeartbeats 9500 in
omit K in
private lemma next_top(Y:Type) {R:Type*}[RCLike R][TopologicalSpace Y][CompactSpace Y](A: StarSubalgebra R (ContinuousMap Y R))(u:A.toSubalgebra.SeparatesPoints) : A.topologicalClosure=⊤:= starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A u
set_option maxHeartbeats 9500 in
omit K in
private lemma finally_top(Y:Type) {R:Type*}[RCLike R][TopologicalSpace Y][CompactSpace Y](A: StarSubalgebra R (ContinuousMap Y R))(u:A=⊤) : A.toSubalgebra=⊤:= by
 apply top_unique; intro j hj; exact (StarSubalgebra.eq_top_iff.mp u j)

set_option maxHeartbeats 30000 in
omit K in
private lemma fullTop(Y:Type) {R:Type*}[RCLike R][TopologicalSpace Y][CompactSpace Y](A: StarSubalgebra R (ContinuousMap Y R))(u:A.toSubalgebra.SeparatesPoints)(v:IsClosed (A.toSubalgebra : Set (ContinuousMap Y R))) : A.toSubalgebra=⊤:=by
 exact finally_top Y _ ((first_top Y _ v).symm.trans (next_top Y _ u))
private lemma opal_fire: (opal (r:=r) K).toSubalgebra=Cof G r:=rfl
set_option maxHeartbeats 30000 in
private lemma pledge (h:4*r≤m): (Cof G r).SeparatesPoints:=by
 intro i j p; obtain ⟨v,e⟩:= (not_forall.mp (mt (Gust_in i.val j.val K h (mem_closedBall_zero_iff.mp i.property) (mem_closedBall_zero_iff.mp j.property)) (fun v=>p (Subtype.ext v)))); let x:= bud G r v; exact ⟨(x : Υ → ℂ), ⟨x,(Cab G r).le_topologicalClosure (show x∈ Cab G r from Cab_entry _),rfl⟩,e⟩
set_option maxHeartbeats 30000 in
lemma metal (h:4*r≤m): Cof G r=⊤:= by
 rw [←opal_fire K]; apply fullTop (Plate r) (opal (r:=r) K) ?_ ?_
 · rw [opal_fire K]; exact pledge K h
 rw [opal_fire K]; exact (Cab G r).isClosed_topologicalClosure
omit K
structure FilterK where
 s : Finset Cover
 f : Cover→ℂ -- terms outside unused
namespace FilterK
protected abbrev pay (L:FilterK) (G:E4 ≃ₗᵢ[ℝ] E4) (p:Space3):=∑ i∈ L.s,L.f i*gust G p i
def total {G:E4≃ₗᵢ[ℝ] E4} (L:FilterK) :Φ:= ∑ i∈L.s, L.f i • bud G r i -- G parameter implicit?
lemma totals (L:FilterK)(i:Plate r) : (total (G:=G) L) i=L.pay G i.val:=by unfold total FilterK.pay; simp [bud]
@[fun_prop] lemma pay_c (L:FilterK)(G:E4≃ₗᵢ[ℝ] E4): Continuous (L.pay G):= by unfold FilterK.pay; fun_prop
end FilterK
lemma silt(x:Φ) (h:x∈Cab G r): ∃ f:FilterK,x=f.total (G:=G):= by
 let A(u:FilterK):= u.total (G:=G) (r:=r)
 refine Submodule.span_induction (p:=fun a _=> ∃ u, a=A u) ?_ ?_ ?_ ?_ (show x∈Cabin G r from h)
 · rintro v ⟨i,rfl⟩; exact ⟨⟨{i},1⟩,by simp [A,FilterK.total]⟩
 · exact ⟨⟨∅,0⟩,by simp [A,FilterK.total]⟩
 · rintro i j _ _ ⟨u,rfl⟩ ⟨v,rfl⟩; let g(L:FilterK)(i:Cover):ℂ:= if i∈L.s then L.f i else 0; let S:= u.s∪ v.s; have he(L:FilterK)(b:L.s⊆S): A L=∑ i∈ S, g L i • bud G r i:=by
      unfold g; simp_rw [ite_smul,zero_smul]; rw [Finset.sum_ite]; rw [Finset.sum_const_zero, add_zero]; rw [show S.filter (fun x:Cover=>x∈L.s)=L.s from (by ext x; exact mem_filter.trans ⟨And.right,(fun t=>⟨b t,t⟩)⟩)]; rfl
   refine ⟨⟨S,g u+g v⟩,?_⟩; change _+_ =∑ i∈ S, (g u i+g v i) •_; rw [he u subset_union_left,he v subset_union_right]; simp_rw [add_smul,sum_add_distrib]
 rintro c y _ ⟨t,rfl⟩; refine ⟨⟨t.s, c • t.f⟩,?_⟩; unfold A FilterK.total; simp_rw [Finset.smul_sum, smul_smul]; rfl
include K
#print axioms metal
lemma pearl (h:4*r≤m) : ∃ M:FilterK,∀ p:Space3,‖p‖≤r→1/2 ≤ (M.pay G p * leer (pulseG G p)^8).re :=by
 let Y:Φ:= ⟨fun p=>leer (pulseG G p.val)^8,( (leer_safe.comp (pulse_cont G)).pow 8 ).comp continuous_subtype_val⟩; have hp(p:Υ):Y p≠0:=gust3 K p.val; let Z:Φ:=⟨fun p=>(Y p)⁻¹,Y.continuous.inv₀ hp⟩; let u:=1/(2*(1+‖Y‖)); have ht:0<u:= by unfold u; positivity
 have he:Z∈Cof G r:=by rw [metal K h]; trivial
 obtain ⟨A,H,g⟩:= Metric.mem_closure_iff.mp he u ht; obtain ⟨f,rfl⟩:= silt A H; refine ⟨f,fun p t=>?_⟩; let v:Υ:= ⟨p,(mem_closedBall_zero_iff.mpr t)⟩; let A:= f.total (G:=G) (r:=r); have hb: ‖A v- Z v‖ < u:= (norm_lt_iff (A-Z) ht).1 (by rw [dist_eq_norm] at g; exact (norm_sub_rev ..).trans_lt g) v -- name
 let x:=A v*Y v; have hx: A v=f.pay G p:=FilterK.totals f v; have hh:‖x-1‖≤ (1:ℝ)/2:=by
    have hz: Z v*Y v=1:= inv_mul_cancel₀ (hp _)
    unfold x; rw [←hz,←sub_mul, norm_mul]; refine (mul_le_mul hb.le (norm_coe_le_norm Y v) (norm_nonneg _) ht.le).trans ?_; unfold u; rw [← mul_div_right_comm,one_mul]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith -- tune
 rw [←hx]; change _ ≤ x.re; have he:= neg_le_abs (x-1).re; have hf:= abs_re_le_norm (x-1); rw [Complex.sub_re, Complex.one_re] at he hf; linarith
#print axioms pearl
end LightK
end YM.CF.Window.ArchiveK
