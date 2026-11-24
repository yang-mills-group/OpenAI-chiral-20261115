/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Taxi.Pout
import YM.CF.Haro.Tacit
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local
open StressFlux AnalyticBridge.VerifiedReset
abbrev RealP(n:Side):=Scree.Hub n→Pot SU.group (More n)
variable (F:RealP n)(V:Sweep n)(X0:Scree.Hub n){u₀:Scree.Hub n→ℝ}
local notation "Vp"=> (moveHub V X0)
local notation "Rp"=> (Ratio.embed (assembly n)) V.b
local notation "Gp"=> boxA V
lemma chart_p : X0.val.1=affine V.s Rp (moveHub V X0).val.1∧ X0.val.2= (moveHub V X0).val.2.image (affine V.s Rp):=by
 have he:affine V.s Rp=boxA V:=funext fun i=>(sitA ..).symm; rw [he]; refine ⟨(Equiv.apply_symm_apply ..).symm,?_⟩; ext i; change i∈X0.val.2 ↔i∈(X0.val.2.map (boxA V).symm.toEmbedding).image _; obtain ⟨i,rfl⟩:=(boxA V).surjective i; simp [(boxA V).injective.eq_iff]
lemma marks : Nonwrapping (villa X0) X0.val.1 ↔ Nonwrapping (villa (moveHub V X0)) (moveHub V X0).val.1:=by
 obtain ⟨p,t⟩:=chart_p V X0; have hp (x): x∈ villa Vp ↔ Gp x∈ villa X0:=by
    unfold villa; rw [mem_union,mem_union,halo_spec,halo_spec]; refine or_congr ?_ ?_; exact Finset.mem_map_equiv
    simp only [Finset.mem_singleton,exists_eq_left]; rw [p,←sitA,sitT]
 have hv : villa X0=(villa Vp).image (affine V.s Rp):=by ext x; obtain ⟨x,rfl⟩:=(boxA V).surjective x; rw [←hp]; simp [(show affine V.s Rp= Gp from funext fun i=>(sitA ..).symm),(boxA V).injective.eq_iff]
 rw [hv,p]; exact spin_wrap ..
abbrev βsP (F:RealP n) : Prop:=∀ (X0:Scree.Hub n)(s:Sweep n) (x:Pane n),s.charge=false→ F (moveHub s X0) (pull s.s ((assembly n).embed s.b) x)=F X0 x
local notation "ZP"=> AnalyticBridge.VerifiedReset.quad
variable(v:βsP F)(p:∀ X,BandS P X (F X) (u₀ X))(hn:60<(More n).val)
include v p hn
lemma pin_M (a b: Flux SU.group)(t:V.charge=false) : ZP (fluxP X0 (F X0)) a b= ZP (fluxP Vp (F Vp)) (reframe a V.s) (reframe b V.s):=by
 have ht:=chart_p V X0; have hp : F X0= F (moveHub V X0) ∘ pull V.s Rp:=funext fun i=> (v X0 V i t).symm
 have hg:=marks V X0; let Y:=moveHub V X0; by_cases h:Nonwrapping (villa X0) X0.val.1; swap; · simp [AnalyticBridge.VerifiedReset.quad,fluxP,h,mt hg.2 h]
 unfold fluxP; simp only [h,hg.1 h,↓reduceIte]; have he:= flux_hessian_pull V.s Rp Y.val.1 Thera.yet_one (p Y).regular (show Nonwrapping Y.val.2 Y.val.1 from fun x r=>hg.1 h x (mem_union_left _ r)) (by omega) a b; rw [← hp,←ht.1] at he; rw [flux_formula _ Thera.yet_one (p X0).regular, flux_formula _ Thera.yet_one (p Y).regular] at he; exact he -- tune hp wr V
omit p v hn
abbrev payoutF(o: Site (More n))(a b:PlaqAxes):ℝ:=∑ X:Scree.Hub n,motto X.val.1 o * fluxP X (F X) a b
private lemma cup_m(o: Site (More n))(u w:Flux SU.group) : ZP (payoutF F o) u w=∑ X:Scree.Hub n, motto X.val.1 o* ZP (fluxP X (F X)) u w:=by
 unfold AnalyticBridge.VerifiedReset.quad payoutF; simp_rw [sum_mul, Finset.mul_sum, mul_assoc]; symm; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]
include p v hn
private lemma quad_t (o: Site (More n))(a b:Flux SU.group)(t:V.charge=false) : ZP (payoutF F (affine V.s Rp o)) a b= ZP (payoutF F o) (reframe a V.s) (reframe b V.s):=by
 rw [cup_m,cup_m]; let L:= Equiv.ofBijective (moveHub V) ⟨Haro.pure_s V,Finite.surjective_of_injective (Haro.pure_s V)⟩
 refine (Fintype.sum_equiv L _ _ fun i=>?_)
 rw [pin_M F V i v p hn a b t,(chart_p V i).1,mot_g]; rfl
omit p hn v
-- adaptive spin formula but finite centers cells.L union. proof adapted from IVEBill native
variable {G₁:Gauge}
private lemma persona (p q : PlaqAxes) (s : Signed) (hs : s.perm p.val.1 = q.val.1) (ht : s.perm p.val.2 = q.val.2) :
    reframe (Averaging.ray q (G:=G₁)) s = (sign s p.val.1 * sign s p.val.2) • Averaging.ray p := by
  ext1 j
  simp only [reframe,Averaging.ray,orderedDir,Pi.smul_apply]
  by_cases hp : j=p
  · subst j; simp [hs,ht,q.property,not_lt_of_gt q.property]
  have h₁ : (s.perm j.val.1, s.perm j.val.2) ≠ q.val := fun h => hp (by
    have := s.perm.injective; apply Subtype.ext; apply Prod.ext <;> apply this <;> grind)
  have h₂ : (s.perm j.val.2, s.perm j.val.1) ≠ q.val := fun h => by
    have ha : j.val.1 = p.val.2 := s.perm.injective (by grind)
    have hb : j.val.2 = p.val.1 := s.perm.injective (by grind)
    exact lt_asymm p.property (show p.val.2 < p.val.1 by rw [← ha,← hb]; exact j.property)
  simp only [Subtype.ext_iff]; split_ifs <;> simp_all
private lemma tutela (q : PlaqAxes → PlaqAxes → ℝ) (hG : G₁.Simple) (a b : PlaqAxes) (u v : ℝ) :
    AnalyticBridge.VerifiedReset.quad q (u • (Averaging.ray a (G:=G₁))) (v • Averaging.ray b) = q a b * (u*v) := by
  rw [AnalyticBridge.VerifiedReset.quad, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]; swap
  · intro x _ hx; simp [Averaging.ray,hx]
  rw [Finset.sum_eq_single_of_mem b (Finset.mem_univ _)]; swap
  · intro y _ hy; simp [Averaging.ray,hy]
  simp [Averaging.ray,real_inner_smul_left,real_inner_smul_right,spike_norm hG,mul_comm v u]

private abbrev dryT (F:RealP n)(o:Site (More n))(i j: PlaqAxes):ℝ:=∑ x:Scree.Hub n with x.val.1=o,fluxP x (F x) i j
private lemma duties (o':Site (More n))(a b:PlaqAxes): payoutF F o' a b=∑ v:Site (More n), motto v o' * dryT F v a b:=by
 unfold payoutF dryT; rw [← sum_fiberwise (univ:Finset (Scree.Hub n)) (fun i=> i.val.1)]; apply sum_congr rfl; intro i _; rw [mul_sum]; apply sum_congr rfl; intro j u; rw [(show j.val.1=i from (mem_filter.mp u).2)]
include p hn v
private lemma shiver(o: Site (More n))(x:Site n)(i j:PlaqAxes): dryT F (o+(assembly n).embed x) i j=dryT F o i j:=by
 let vQ:Sweep n:=⟨1,x,false⟩; let R:= Equiv.ofBijective (moveHub vQ) ⟨Haro.pure_s vQ,Finite.surjective_of_injective (Haro.pure_s vQ)⟩; let L:= (assembly n).embed x; unfold dryT; refine Finset.sum_equiv R ?_ ?_
 · intro i; have he:= (chart_p vQ i).1; change i.val.1=affine 1 L (R i).val.1 at he; unfold affine at he; rw [Signed.act_one] at he; simp [he,L]
 intro i' h; have hh:=pin_M F vQ i' v p hn ((1:ℝ) • Averaging.ray i) ((1:ℝ) • Averaging.ray j) rfl; change ZP _ ((1:ℝ) • Averaging.ray i) ((1:ℝ) • Averaging.ray j)= ZP _ (reframe _ 1) (reframe _ 1) at hh -- tune type
 let S:=Thera.yet_one
 rw [tutela _ S,one_smul,one_smul,persona i i 1 rfl rfl,persona j j 1 rfl rfl,tutela _ S] at hh; simp [sign] at hh; -- tune sign
 exact hh
private lemma voteB(o:Site (More n)): payoutF F o=payoutF F 0:=by
 ext a b; let A(x:Site (More n)):=dryT F x a b; have h(x):payoutF F x a b=fs*∑ s:Signed,spanK s A 0:=by rw [duties]; exact blareR _ (fun i y=>shiver F v p hn i y a b) _
 exact (h o).trans (h 0).symm
abbrev lureC (F: RealP n):ℝ:= payoutF F 0 Averaging.axes01 Averaging.axes01
lemma betaK (o: Site (More n))(a b:PlaqAxes): payoutF F o a b= if a=b then lureC F else 0:=by
 have he (d e i j:PlaqAxes)(s:Signed)(hd:s.perm i.val.1=d.val.1 ∧ s.perm i.val.2=d.val.2)(hg:s.perm j.val.1=e.val.1∧ s.perm j.val.2=e.val.2):payoutF F 0 d e=payoutF F 0 i j*((sign s i.val.1*sign s i.val.2)*(sign s j.val.1*sign s j.val.2)):=by
    let vQ:Sweep n:=⟨s,0,false⟩; have hl:=quad_t F vQ v p hn 0 ((1:ℝ) • Averaging.ray d) ((1:ℝ) • Averaging.ray e) rfl; let S:=Thera.yet_one
    change ZP (payoutF F (affine s ((assembly n).embed 0) 0)) ((1:ℝ) • Averaging.ray d) ((1:ℝ) • Averaging.ray e)= ZP _ (reframe _ s) (reframe _ s) at hl
    rw [voteB F v p hn,tutela _ S,one_smul,one_smul,persona i d s hd.1 hd.2,persona j e s hg.1 hg.2,tutela _ S,one_mul,mul_one] at hl; exact hl -- tune
 rw [voteB F v p hn]; split
 next h=> subst b; obtain ⟨t,l,hb⟩:=extend_two a.val.1 a.val.2 a.property.ne; simpa only [sign, Bool.false_eq_true,if_false,mul_one, lureC] using he a a Averaging.axes01 Averaging.axes01 ⟨t,fun _=> false⟩ ⟨l,hb⟩ ⟨l,hb⟩ -- syntax t etc
 next hn=>
    have H(x:Axis):= he a b a b (Signed.mirror x) ⟨rfl,rfl⟩ ⟨rfl,rfl⟩
    simp only [sign,Signed.mirror,decide_eq_true_eq] at H
    have ha:=H a.val.1; have hb:= H a.val.2; have H₁:= a.property; have H₂:= b.property; have he:a.val.1 ≠ b.val.1 ∨ a.val.2 ≠ b.val.2:= by grind
    simp only [↓reduceIte,if_neg H₁.ne,if_neg (Ne.symm H₁.ne),one_mul,mul_one] at ha hb
    rcases (show (a.val.1 ≠ b.val.1∧a.val.1 ≠ b.val.2)∨(a.val.2 ≠ b.val.1∧ a.val.2 ≠ b.val.2) by grind) with ⟨t,g⟩|⟨t,g⟩
    · simp only [if_neg t,if_neg g,mul_one,mul_neg] at ha; linarith
    simp only [if_neg t,if_neg g,mul_one,mul_neg] at hb; linarith
lemma mergeT (o:Skye.Seat n)(V:Pane n): (∑ X:Scree.Hub n, fuelC X (F X) o V) = lureC F*((∑ i:PlaqAxes,‖AnalyticBridge.VerifiedReset.petals V o i‖^2)/2):=by
 let v':=AnalyticBridge.VerifiedReset.petals V o; have hp := cup_m F o v' v'
 have hx(j:PlaqAxes):∑ i:PlaqAxes,payoutF F o j i * inner ℝ (v' j) (v' i)=lureC F* ‖v' j‖^2:=by
    rw [sum_eq_single j]; · rw [betaK F v p hn o,if_pos rfl,real_inner_self_eq_norm_sq]
    · intro i _ t; rw [betaK F v p hn o,if_neg (Ne.symm t),zero_mul]
    simp
 have ht': ZP (payoutF F o) v' v'=lureC F* ∑ i:PlaqAxes,‖v' i‖^2:=by unfold AnalyticBridge.VerifiedReset.quad; simp_rw [hx,mul_sum]
 rw [ht'] at hp; rw [← mul_div_assoc,show (lureC F * ∑ i:PlaqAxes,‖v' i‖^2) =_ from hp] -- tune motive
 rw [sum_div]; apply sum_congr rfl; intro j _; unfold fuelC counter; simp only [Pi.smul_apply,smul_eq_mul,mul_div_assoc]; rfl
end YM.CF.Taxi
