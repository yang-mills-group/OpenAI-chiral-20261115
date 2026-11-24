import YM.CF.Facet.Hemp
import YM.CF.Facet.Horn
import YM.CF.Cour.Culm
import YM.CF.Tarn.Sold
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Facet
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff  InnerProductSpace
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
local notation "G₅"=> SU.group
open Cube Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ v w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {F:Tab T}{C V R Z η:ℝ}{Q: Msca m X B G e}{Φ:nomA m X B→ ℂ}{i:Site (More (CSide m B))}
lemma owing(g:Ratio c f)(A: Seal (Site f)→ℝ)(K:ℝ)(p:∀ S,0 ≤ A S)(t:∀ x,hitE a A x≤ K)(i:Site c)(h:0 ≤ a)(L: Finset (Seal (Site f))): (∑ j∈L,|turtle g j i| * A j) ≤g.count.val^4*K:=by
 let f(j)(v:Site g.count):= if g.assemble (i,v)∈j then Branch.rent a j*A j else 0; have hf(j v): 0 ≤ f j v:=by unfold f; split; exact mul_nonneg (rent_pos ..|>.le) (p j); rfl
 refine (sum_le_sum (g:=fun j=>∑ u,f j u) ?_).trans ?_
 · intro z h; by_cases hx:i∈ mount g z; swap; simp only [turtle,if_neg hx,abs_zero,zero_mul]; exact sum_nonneg fun i _=>hf _ _
   obtain ⟨y,ht,hy⟩:=mem_image.mp hx; apply (mul_le_of_le_one_left (p _) (turtle_u ..)).trans; let V:= g.residue y
   apply le_trans _ (single_le_sum (fun i _=>hf z i) (mem_univ V)); unfold f; rw [if_pos (show _∈ z from ?_)]; exact le_mul_of_one_le_left (p _) (rent_one (by assumption) _); rw [←hy,show g.assemble (g.parent y,V)= y from g.unpack_at y]; exact ht -- tune
 rw [Finset.sum_comm]; apply (sum_le_sum (g:=fun _=>K) (fun k _=>?_)).trans
 · simp only [sum_const, card_univ,nsmul_eq_mul,Lattice.site_card, Nat.cast_pow]; rfl -- tune
 apply le_trans _ (t (g.assemble (i,k))); unfold hitE hit0; rw [sum_filter]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _=> hf i _ -- tune
abbrev InterestP (T:Tube G₅ S)(x:ℝ)(l:ℕ)(P:Tab S)(n:ℕ)(u r t A:ℝ): Prop:= let Φ:=Souk.flute P.1 (sol S T P.2 x P.1 l) u; ∀ i:Mast G₅ c,‖i‖ <1→ ‖Φ i‖< r ∧ Jet.Allows n Φ i A ∧ Fire T x P.1 P.2 l u n t i
lemma mallB(K:Teller G₅)(P:Patch)(t:ℕ)(p:P.Branches K.bind G₅)(n l:ℕ)(hk:2 ≤ n)(hx:l ≤18)(f:ℝ)(W:Push.Uniform.Before G₅ K.top.width K.top.paths K.j K.bind (n+2))(D:Push.Uniform.Before G₅ K.top.width K.top.paths K.j K.bind (n+3))(hp:0<f):∃ r a b:ℝ,0<r∧ r≤1∧0<a∧0≤b ∧∀ᶠ x in atTop, ∀ {c f':Side}(S:StepData c f')(T:Tube G₅ S)(H:Tab S), Cert P K S T x→ sizedP G₅ P K S T H.1→ InterestP T x l H n r f a b:=by
 obtain ⟨A,s,hA,hS,J⟩:= persp K P p n l hk hx D W
 obtain ⟨B,Z,v,hB,hZ,hv,F⟩:=Vol.lift_paid Thera.yet_one K P p n l hk W
 let X:= max B 1; have hx:0<X:= zero_lt_one.trans_le (le_max_right ..); let c:=min f 1; let r:=min ((c/4)/X) (min (v/2) s); have he:0<c:=lt_min hp zero_lt_one; have hr:0<r:=lt_min (div_pos (by positivity) hx) (lt_min (half_pos hv) hS); have ht:0<4*X*r:=by positivity
 have hy:r ≤ X*r:=le_mul_of_one_le_left hr.le (le_max_right ..); have hp:X*r ≤ c/4:= by rw [mul_comm]; exact (le_div_iff₀ hx).mp (min_le_left ..)
 have hF:3*X*r<c:=by linarith
 have hU: r < c:=by linarith
 have hz:r ≤1:=hU.le.trans (min_le_right ..)
 refine ⟨r,A,1,hr,hz,hA,zero_le_one,?_⟩; filter_upwards [J,F,lamp_s.eventually (ge_mem_nhds hr)] with x hg hK hL c' f' S T P hx hv y hy'
 let Φ:= Souk.flute P.1 (sol S T P.2 x P.1 l) r
 obtain ⟨z,t,s,Q'⟩:=hK S T P.1 hx hv; -- shadow
 let Z':= sol S T P.2 x P.1 l; have he:∀ i:Mast G₅ c',‖i‖< v→Jet.Allows n Z' i X∧ Z' 0=0:=fun i t=> ⟨((Q' P.2 i t).1.mono (le_max_left ..)), (Q' P.2 i t).2.1⟩
 have hK' :Jet.Allows n (fun i=>Z' (r • i)) y (X*r):=by
    -- near_s needs r<v strict; currently r≤v; y<1 choose slightly smaller? `near_s` argument uses `r<v`; revise
    have hh:= Newt.near_s hr.le hz (show 1 ≤ n by omega) (show r<v from ?_) (fun i p=>(he i p).1) hy'.le; swap
    · unfold r; exact (min_le_right ..).trans_lt ((min_le_left ..).trans_lt (half_lt_self (by assumption)))
    simp_rw [(he 0 (by simp_all)).2,sub_zero] at hh; exact hh
 have hP:Jet.Allows n Φ y (3*X*r):= (turn_safe hK' hK' hr.le (le_max_right B 1) hy' 0 (Set.left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp; rfl)
 exact ⟨hP.value.trans_lt (hF.trans_le (min_le_left ..)),hP.mono (hF.le.trans (min_le_right ..)), hg.2.2.2 S T P.1 hx hv P.2 r hL ((min_le_right ..).trans (min_le_right ..)) y hy'⟩
section
variable {t u γ z:ℝ}{q:Chi}{b:Site c}{N: mSeal X B→ℝ}
lemma on_turf (j:Tab T)(t:0<e)(h:Fleck G t j.1 η C k)(hp:InterestP p x l j k u η V R) : ∀ y:Mast G₅ (More (CSide m B)),‖y‖<1→ hornY p q x d l j (satU G₅ u y)∈ Rent0 G e:=fun y hy=> wreath p q x d l j y (hp y hy).2.2 |>.symm ▸ h.onP _ (hp y hy).1
lemma lane (o:Site (More (CSide m B)))(U:Tab T)(t:0<e)(h:Fleck G t U.1 η C k)(hp:InterestP p x l U k u η V R)
 (p':Tally Q Φ η C a Z k)(q:Chi)(d:ℝ)(hS:0 ≤ a)(hR:0≤ R):∀ y:Mast G₅ (More (CSide m B)),‖y‖<1 → Jet.Allows k (turf G p q x d l Q t U o ∘ satU G₅ u) y (Jet.composeCost k (G.count.val^4*Z) R):=by
 obtain ⟨V,H,Y⟩:=p'.members
 intro y hy; let W:= Souk.flute U.1 (sol T p U.2 x U.1 l) u; let L:=univ.filter fun j:mSeal X B=> j.card≤ Stores.till x
 let M(i:mSeal X B):= Q i ∘ frameT G t U.1
 have he(i)(h':i∈L):Jet.Allows k (M i) (W y) (V i):=(H i).plot _ (ball 0 η) isOpen_ball _ h.mark (W y) (mem_ball_zero_iff.mpr (hp y hy).1)
 let g(i):=turtle (ratio G) i o
 apply (((allows_sum (s:=L) (f:=fun i y=> g i • M i y) (fun i hi=> (he i hi).smul _)).mono (owing _ V Z (fun i=>(H i).pos) Y o hS L)).comp (hp y hy|>.2.1)).germ
 filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hy)] with v hv -- tune
 change _= ∑ i∈L, _; apply Finset.sum_congr rfl; intro i hi; unfold M test; rw [wreath p q x d l U v (hp v (mem_ball_zero_iff.mp hv)|>.2.2)]; rfl -- tune
end
end YM.CF.Facet
