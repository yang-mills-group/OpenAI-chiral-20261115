import YM.CF.Brace.Card
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B : Side}{U:Skin m B}{s:ArrayF m}{X:Sheen m B}
def airing(m B: Side)(U:Skin m B)(s:ArrayF m)(w:Sq) : Sheen m B:=fun i=> box (paint m B U s w i)
lemma rise_zero(m B U s)(w:Sq)(x:Sheen m B): ark m B U s x 0 w=x:=by
 funext i; unfold ark roofV; simp only [zero_smul,sub_zero,one_smul,zero_add]; apply Subtype.ext; rw [box_u (norm_pos_iff.mp (by rw [hookN]; norm_num)),ren,hookN,inv_one,one_smul]; rfl
lemma rise_one(m B U s w)(x:Sheen m B): ark m B U s x 1 w=airing m B U s w:=by funext i; simp [ark,roofV,airing]
lemma ark_same(m B U)(s t:ArrayF m)(r:Zone)(h:∀ i:Spot m,i.2∈r → s i=t i)(X v){q:Sq}(e:q∈zone r):ark m B U s X v q=ark m B U t X v q:=by
 funext i; unfold ark roofV; have he: paint m B U s q i=paint m B U t q i:=by
   apply sum_congr rfl; rintro ⟨x,j⟩ _; by_cases g:j∈r
   · rw [h _ g]
   rw [empty_cash (e.2 _ g),zero_smul,zero_smul];
 rw [he]
abbrev hip(m B:Side):= Skin m B×ArrayF m ×Sheen m B×Sq
lemma push_c(m B:Side)(t:ℝ)(i: Site (Domain m B)):Continuous (fun x:hip m B=> roofV m B x.1 x.2.1 x.2.2.1 t x.2.2.2 i):=by
 let f :=fun x:hip m B=>(x.1,x.2.1,x.2.2.2); have hv:Continuous f:=continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp (continuous_snd.comp continuous_snd)))
 refine (((continuous_const (y:=t))).smul ((continuous_apply i).comp ((paint_cont m B).comp hv))).add ( (continuous_const (y:=1-t)).smul ?_) -- tune
 exact continuous_subtype_val.comp ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
lemma ark_at (e p d t:ℝ) (r:Zone)(f:Guide B e p d) (y:hip m B)(h:Foil m B e p r y.2.1 y.2.2.1 y.1)(g:y.2.2.2∈zone r)(he:t∈ Set.Icc 0 1): ContinuousAt (fun x:hip m B=> ark m B x.1 x.2.1 x.2.2.1 t x.2.2.2) y:= by
 apply continuousAt_pi.mpr; intro i
 exact (box_cont (norm_pos_iff.mp ((half_pos low_p).trans_le (angel h f _ g t he i)))).comp (f:=fun x:hip m B=> roofV m B x.1 x.2.1 x.2.2.1 t x.2.2.2 i) ((push_c m B t i).continuousAt) -- tune
structure CoinG(j l b n:ℕ)(d a x:ℝ) : Prop where
 posT :0<d
 stock : blendS j l d x a b
 fresh : ∀ (N: Side),b≤N.val→∀ M: Tulip.Male, PairsB j l d N M
 steps: 0<n
 size : 4/low*(2*(1/(n:ℝ))) < d
lemma coin_v (j:ℕ)(hj:1≤j):∃ l d a x b n, 0<a∧0<x∧ CoinG j l b n d a x:=by
 obtain ⟨l,p,h⟩:= (monoto j hj).youth (show Odd (1:Side).val from odd_one)
 obtain ⟨d,a,K,hp,ha,hk,b,g,hT⟩:= Dial.stops j l hj p h
 obtain ⟨n,H⟩:= exists_nat_gt (8/low/d); have he:=low_p; have hv:0<(n:ℝ):= (show 0<(8/low/d:ℝ) by positivity).trans H
 exact ⟨l,d,a,K,b,n,ha,hk,hp,g,(fun N=>hT),Nat.cast_pos.mp hv,by field_simp at *; linarith⟩ -- field_simp at * tune
variable {j l b n:ℕ}{e p d a w:ℝ}{r:Zone}
abbrev facePay (j l n:ℕ)(M:Tulip.Male)(m B:Side)(U:Skin m B)(s:ArrayF m)(X:Sheen m B)(q:Sq)(i:ℕ):ℂ:=openC j l M U (ark m B U s X (berth n i) q) (ark m B U s X (berth n (i+1)) q)
def torque (j l n:ℕ)(M:Tulip.Male)(m B:Side)(U:Skin m B)(s:ArrayF m)(X:Sheen m B)(q:Sq):ℂ:= ∑ i∈range n, facePay j l n M m B U s X q i
variable (H:CoinG j l b n d a w)(G:Guide B e p d)
include H G
lemma rail_g (h:Foil m B e p r s X U) {q:Sq}(g:q∈zone r)(i)(p:i<n): Gaze U (ark m B U s X (berth n i) q) (ark m B U s X (berth n (i+1)) q) d:=by
 let S:= ber_m n (Nat.le_add_right i 1); have ht:= railIn n i p; let u:=berth n i; have hx:u∈ Set.Icc 0 1:=ht ⟨le_rfl,S⟩; have hy : berth n (i+1)∈Set.Icc 0 1:=ht ⟨S,le_rfl⟩
 refine ⟨h.guard.shrink G.vote,ark_bound h G _ g _ hx,ark_bound h G _ g _ hy,fun x=>?_⟩
 apply (canvas h G _ g (berth n i) _ hx hy x).trans_lt; rw [abs_sub_comm,berth_diff n H.steps,abs_of_nonneg (by positivity)]; exact H.size
variable (hm:b≤(CSide m B).val)
include hm
lemma tor_ok (h:Foil m B e p r s X U) {q:Sq}(g:q∈zone r) (M:Tulip.Male): Complex.exp (torque j l n M m B U s X q) • coneP j M U X= coneP j M U (airing m B U s q) ∧ coneP j M U X≠0:=by
 let C:=coneP j M U; let F:=facePay j l n M m B U s X q; let R (i):=ark m B U s X (berth n i) q
 have he:R 0=X:=by unfold R; rw [berth0]; exact rise_zero ..
 have hp(i)(hx:i<n): Complex.exp (F i) • C (R i)=C (R (i+1)) ∧ C (R i) ≠0:=by
   obtain ⟨-,t,u,-⟩:= H.fresh _ hm _ _ _ _ (rail_g H G h g i hx)
   exact ⟨t,u⟩
 have hy(i)(hx:i≤ n):Complex.exp (∑ j∈range i,F j) • C X = C (R i):=by
   induction i with| zero=> simp [he] | succ i ih=> rw [sum_range_succ, add_comm, Complex.exp_add,mul_smul, ih (by omega), (hp i hx).1] -- tune add_comm
 exact ⟨(hy n le_rfl).trans (congrArg C (show R n= _ from (by unfold R; rw [berthLast n H.steps,rise_one]))),he ▸ (hp 0 H.steps).2⟩
end YM.CF.Brace
