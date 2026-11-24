import YM.CF.Cascade.Temple
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m X B L:Side}{ho:Odd L.val}{d e:ℝ}{Y:Pricing j L ho (Vault.Thread j)}{P:Grasp Y B e} {G:Ratio (CSide m B) (CSide X B)}{T:Roam m X B}{F:Forest T.ratio}{z:Vox m B→AxisChart group F}{M: Male}
open Pec
local notation "dη"=>Aroma.port
local notation "μN"=> Ember.pinch
-- telescope divisor estimates
lemma alignsR(G:Ratio n f): base_u f = (G.count.val:ℝ)^2 * base_u n:=by
 unfold base_u; change date f * μN f^2= _; have hv:date f=date n*(G.count.val:ℝ)^4:=by unfold date; simp [More,G.exact_size,site_card]; ring
 rw [hv,slideN G]; field_simp -- tune
abbrev Natht(v: Side):= (v.val:ℝ)
abbrev Taper(v:Side):=Real.sqrt (Natht v)
def spiceM:ℝ:=60/(12*Real.pi^2)
lemma log_l(G:Ratio n f): Real.log f.val=Real.log n.val+Real.log G.count.val:=by rw [G.exact_size,Nat.cast_mul,Real.log_mul (side_pos n).ne' (side_pos G.count).ne']
lemma pineN (x: Side): 0<Taper x ∧1≤Taper x ∧ Taper x*Taper x=Natht x∧Real.log x.val ≤ 2*Taper x∧0≤Real.log x.val:=by
 have hx:0<(x.val:ℝ):=side_pos _; let t:= Taper x; have hp: t*t=Natht x:=Real.mul_self_sqrt hx.le; have he:0<t:=Real.sqrt_pos.mpr hx; have h:1≤Natht x:=by exact_mod_cast x.property
 refine ⟨he,?_,hp,?_,Real.log_nonneg h⟩; change 1≤t; nlinarith
 rw [show (x.val:ℝ)=_ from hp.symm, Real.log_mul he.ne' he.ne']; linarith only [Real.log_le_self he.le]
lemma gapN(A B:ℝ)(h:0<A)(p:0<B)(L:Side) :∃ C:ℝ,0<C ∧∀ c f: Side,∀ (G:Ratio c f),G.count=L→∀ u v:ℝ, |u-spiceM*Real.log f.val| ≤ A→|v-1| ≤ B/c.val→|(v-1)*u|≤ C/(Taper c):=by
 have ht:0<spiceM:=by unfold spiceM; positivity
 let C:=A+spiceM*Real.log L.val+2*spiceM; have he:0<C:=by unfold C; linarith [mul_nonneg ht.le (pineN L).2.2.2.2]
 refine ⟨B*C,mul_pos p he,fun c f G e u v s y=>?_⟩
 rw [log_l G,e] at s
 obtain ⟨t,f',g,k,z⟩:= pineN c; have hL:= pineN L; have hx : |u|≤ C*Taper c:=by
    let D:=spiceM*(Real.log c.val+Real.log L.val); have hp: 0≤D:=mul_nonneg ht.le (add_nonneg z hL.2.2.2.2)
    rw [show u=u-D+D from (sub_add_cancel ..).symm]; apply (abs_add_le ..).trans; refine (add_le_add s (abs_of_nonneg hp).le).trans ?_; unfold C D; rw [mul_add spiceM,add_mul]; have hh:= mul_le_mul_of_nonneg_left k ht.le; nlinarith [le_mul_of_one_le_right (show 0≤A+spiceM*Real.log L.val from add_nonneg h.le (mul_nonneg ht.le hL.2.2.2.2)) f']
 rw [abs_mul]; apply (mul_le_mul y hx (abs_nonneg _) (by positivity)).trans_eq; rw [show (c.val:ℝ)=_ from g.symm]; field_simp
-- calibrated prices per level; subtract supplies log universal
structure Aurora (H:Momentum→ℝ)(y:Side)(b:ℝ):Prop where
 hint :|H (dη y)/base_u y - spiceM*Real.log y.val|≤b
 full(v:Momentum):physical v→ |H v|≤b*y.val*date y
lemma upper {α b B v:ℝ}(U L V:Side)(q:0≤b) (hx: 0≤ B)(r:0≤v)(h:0<α): α ≤ v/U.val→α ≤ v/Taper U:=by
 intro e; have he:= pineN U; exact e.trans (div_le_div_of_nonneg_left r he.1 (by nlinarith [he.2.2.1,he.2.1])) -- unnecessary
lemma equalH (h:4≤j)(e:4≤t)(g:0<k)(L: Side)(a b c d:ℝ)(p:0<a)(q:0<b)(r:0<c)(l:0<d):∃ i:ℕ,∃ A:ℝ,0<A∧∀ (P:Flight j t),P.L=L→∀ (s t:Side)(G:Ratio s t),G.count=L→∀ (H:Momentum→ℝ)(f β:ℝ)(V:Bed), i≤s.val→ V.metric.strip c d→ V.metric.read 0=1→Aurora H t b→|β|≤a→ f+β*(base_u s*baser s V)=∑ i:Site P.L, ‖angel k P (dη s) i‖^2*H (aliasAt (dη s) i)→ |f/base_u s+β-H (dη t)/ base_u t|≤ A/(Taper s):=by
 obtain ⟨C,hc,D⟩:=boundL g h e L q; obtain ⟨J,hj,j',E⟩:=angelV g h e L; obtain ⟨K,hK,Q⟩:=gapN b J q hj L; obtain ⟨W,hW,z,Z⟩:=gradeCash r l
 refine ⟨z+j'+3,K+C+a*W*Real.pi,by positivity,fun P t s u G r' H f v X p' Y n S v' H' =>?_⟩
 have hj: aliasAt (dη s) (0: Site P.L)=dη u:=by -- dependent
   have hg:P.L=G.count:=t.trans r'.symm; have hh(A B:Side)(h:A=B):aliasAt (dη s) (0:Site A)=aliasAt (dη s) (0:Site B):= h ▸ rfl
   exact (hh _ _ hg).trans (slideK G)
 let G' := ‖angel k P (dη s) 0‖^2 * (L.val:ℝ)^2; let g' := H (dη u)/base_u u; let z':= ∑ i∈(univ:Finset (Site P.L)).erase 0,‖angel k P (dη s) i‖^2 * H (aliasAt (dη s) i)
 have H0:f+ v*(base_u s*baser s X)= ‖angel k P (dη s) 0‖^2 * H (dη u)+z':=by apply H'.trans; rw [←hj]; exact (Finset.add_sum_erase (univ (α:=Site P.L)) _ (mem_univ 0)).symm
 obtain ⟨U,V,hB,hp,hY⟩:=pineN s; have hz:Taper s≤ s.val:=by nlinarith only [hB,V]
 have ht:= base_p s; have hg: |(G'-1)*g'| ≤ K/Taper s:= Q _ _ G r' _ _ S.hint (E P t s (by omega)); have hp: |z'/ base_u s|≤ C/Taper s:=(D P t _ _ G r' (by unfold card_c; simp [More]; omega) H S.full).trans (div_le_div_of_nonneg_left hc.le U hz)
 have hα: |v*(baser s X-1)| ≤ a*W*Real.pi / Taper s :=by rw [abs_mul]; apply (mul_le_mul v' (Z s (by omega) X Y n) (abs_nonneg _) p.le).trans; apply le_trans _ (div_le_div_of_nonneg_left (by positivity) U hz); unfold Cascade.pulse Ember.pinch; ring_nf; exact le_rfl -- tune
 have hm:f/base_u s+v*baser s X= G'*g'+z'/base_u s :=by
    rw [show f/base_u s+v*baser s X= (f+v*(base_u s*baser s X))/base_u s by field_simp, H0,add_div]; unfold G' g'; rw [alignsR G,r']; field_simp
 change |f/base_u s+v-g'|≤_; rw [show f/base_u s+v-g'= (G'-1)*g'+z'/base_u s-(v*(baser s X-1)) from ?_]; exact (abs_sub _ _).trans ((add_le_add ((abs_add_le ..).trans (add_le_add hg hp)) hα).trans_eq (by ring)); linarith
end YM.CF.Cascade
