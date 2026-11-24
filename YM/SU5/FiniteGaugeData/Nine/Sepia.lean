import YM.SU5.FiniteGaugeData.Nine.Mindi
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot
variable (o:Cover) {N:Side}
local notation "Μ"=> Single N
open Fock Fock.Brique
local notation "H₀"=> (polarQ o)
open Nacre
section combine
variable (k:ℕ)(M:Tulip.Male)(σ:Window.Family)(Q: Finset (Site N))(T:Support (More N))(n:ℕ)
local notation "Σ"=> ((volts (bossColor σ) Q).powerset)
local notation "x" S:max=> officeH o k M (bossColor σ) Q T S -- office. avoid x var
abbrev raysAbove := (Σ).filter (fun S=> n ≤ S.card)
abbrev raysBelow := (Σ).filter (fun S=> ¬ n ≤ S.card)
local notation "b_"=> raysBelow σ Q n
local notation "a_"=> raysAbove σ Q n
local notation "λ₁"=> (2:ℂ)^(Q.card)
abbrev averageP (C:Finset (Finset (Single N)))(x₀:Finset (Single N)→FC (Single N)) : FC (Single N):= λ₁ ⁻¹ • ∑ i∈C,x₀ i
local notation "J_"=> averageP Q
lemma united (p:1≤k)(e:Aptitude k N): J_ (a_) (fun i=>x i)+ J_ (b_) (fun i=>x i)= (1:FC (Single N)):=by unfold averageP raysAbove raysBelow; rw [← smul_add, sum_filter_add_sum_filter_not]; rw [show (∑ i∈ (Σ), x i)= _ from sum_oasis (Tset N) (volts (bossColor σ) Q) (localP k M _ Q T) (localM o k M _ Q T) (same_dual o k M _ Q p e), ←bossPopulation,knob_size]; rw [inv_smul_smul₀ (by norm_num)] -- need nz Complex2^q using pow_ne
private abbrev cashLoan {I:Type*}[DecidableEq I] (t:Finset I)(b:I→ℂ):= λ₁ ⁻¹ • ∑ i ∈ t,b i
private lemma measureFee {b:Finset Μ→ℂ}{C:Finset (Finset Μ)}(h:C⊆ Σ)(t:∀ i ∈ C,‖b i‖ ≤ 1/8) : ‖cashLoan Q C b‖ ≤1/8:=by
 have he:(Σ).card=2^Q.card:= by rw [card_powerset,← bossPopulation, knob_size]
 unfold cashLoan; rw [norm_smul,norm_inv,norm_pow,(show ‖(2:ℂ)‖=(2:ℝ) from (by norm_num)), inv_mul_le_iff₀ (by positivity : 0<(2:ℝ)^Q.card)]; refine (norm_sum_le ..).trans ((sum_le_sum t).trans ?_); rw [sum_const, nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right ?_ (by positivity : (0:ℝ) ≤ 1/8); exact_mod_cast ((card_le_card h).trans (le_of_eq he)) -- tune he scope
-- choose only boost-nonGauge before averaging. cert COST norm for lifted `Ξafter`. Title X0 raysBelow*(F−1) ; Poe preserving.Visibility. 
def stains := J_ (b_) (fun i=> (x i-1))
section
variable {d c C e γ:ℝ}{W:Pane N→ℂ}{U R:Support (More N)} (F:Corset T R (wrap (More N) o)) (L:Mark N→ₗ[ℂ]ℂ) {w:ℕ}
local notation "X1"=> (stains o k M σ Q T n)
local notation "u"=> sapW o W
local notation "o'"=> (loadF F (sapW o W)).comp (centB N)
local notation "Y"=> (loadF F (sapW o W) (centB N X1))
private lemma Librarian (c:ℂ): ‖c-1‖ ≤ 1/4→ (3/4:ℝ) ≤ c.re:=by intro h; have hv:= Complex.abs_re_le_norm (c-1); rw [Complex.sub_re,Complex.one_re,abs_le] at hv; linarith only [hv.1,h]
private lemma pier (F:Corset T R (wrap (More N) o)): pageF o N (loadF F (sapW o W) (1:FC (Single N)))=loadF F (sapW o W) (1:FC (Single N)):= by
 rw [load_exact]; funext i; unfold cargo pageF castT imageQ rollR; simp_rw [flips_one, Prod.map_fst,twist_scalar,imageOne]; exact congrArg (fun x':ℂ=> x' • 1) (congrFun (sky_identity o (W:=W)) i.1)
def mastΨ (N:Side) : Mark N→ₗ[ℂ]Mark N where
 toFun f:=pageF o N f; map_add' f g := funext fun i=>map_add ..; map_smul' a f:= funext fun i=>twist_scalar ..
variable (w)(p:1≤k)(eV:Aptitude k N) (I':‖(emU k M (bossColor σ) Q)‖ ≤ 1-σFee/2) (q: Lattice.halo (2*w) (Q.image node)⊆ T)
include p I' q eV
lemma stain_pay : Barque σ Q (T \ Q.image node) (stains o k M σ Q T n):= by
 have he : ∀ g : Finset (Finset Μ), Barque σ Q (T\Q.image node) (∑ i∈g,(x i-1)):=by
    intro i; induction i using Finset.induction_on with
    | empty=> rw [sum_empty]; exact .zero
    | insert i s H ih=> rw [sum_insert H]; exact .add (yearning o k w σ Q T M p eV I' q i) ih
 exact .mul _ (he _)
variable (C_: Liquid w (funde k M N 1) (tailCost c C w))(xC:2*n=Q.card)
local notation "γ_"=>opt (tailCost c C w)*(σFee/2)⁻¹
local notation "P_"=> funde k M N 1
variable {Z:Peg N}{K:Loom N}(G:0≤ Z.e) (p0:Z.Ft false 1=funde k M N 1) (O:Casing N Z.e (Z.Ft false) c C d) (I:0≤ C)(sR:Earn o R)(sT: Earn o T)(sU:Earn o U)(hT: Lattice.halo w T⊆ U)(hR:U⊆R)(K_: CashMask F W U (d*γ) K)(B: opt (tailCost c C w)*(σFee/2)⁻¹+(2*tailCost c C w+γ*C)≤ e-tailCost c C w)
include C_ I xC G p0 O sR sT sU hT hR K_ B
lemma satin_sv (τ : Pay L n w (tableI Q.card) c C e Z R K) (h: ‖L (loadF F u (1:FC (Single N)))-1‖ ≤ 1/4) : 1/2 ≤ Complex.re (L (Y-pageF o N Y)):=by
 let A:= fun i :Finset Μ => x i; let W₀ : FC Μ→ₗ[ℂ] Mark N:=o'; let Hp':=L.comp W₀; let R':=mastΨ o N; let M':=L.comp (R'.comp W₀)
 have P'(i:Finset Μ)(t:i∈ (Σ)):(n ≤ i.card→ ‖Hp' (A i)‖ ≤1/8) ∧ (¬ n ≤ i.card → ‖M' (A i)‖ ≤ 1/8):=by
    obtain hk := pace_cost o k n w σ Q T M p eV I' q i C_ t xC
    have hf:Fine (Tset N) (modesIn N T) false (A i):= sub_add_cancel (A i) (1:FC Μ) ▸ Fine.add ((yearning o k w σ Q T M p eV I' q i).fines ((halo_subset ..).trans q) sdiff_subset) .one
    obtain hc:= dualCost o F L sR sT O I B sU K_ hR hT τ G hf (ampleCost o k σ Q T M p eV I' i)
    rw [p0] at hc; change (_→ ‖L (loadF F _ _)‖ ≤ _)∧ (_→ ‖L (R' (loadF F _ _))‖ ≤ _); rw [load_exact]; exact ⟨fun p=>hc.1 (hk.1 p),fun p=>hc.2 (hk.2 p)⟩ -- load canceled
 have ht := united o k M σ Q T n p eV; let J1:= averageP Q (a_) A; let J2:= averageP Q (b_) A; let s:=(a_); let r:=(b_); let hz(w:ℂ):‖w‖≤1/8→ w.re ≤1/8:=fun h' => (Complex.re_le_norm w).trans h'
 have he(GG:FC Μ→ₗ[ℂ]ℂ)(C: Finset (Finset Μ))(p:C⊆ Σ)(q:∀ i∈C, ‖GG (A i)‖ ≤ 1/8): (GG (averageP Q C A)).re ≤1/8:= by
    unfold averageP; rw [map_smul,map_sum]; exact hz _ (measureFee σ Q p q)
 have hS:=he Hp' s (filter_subset ..) (fun i v=> (P' i (mem_filter.mp v).1).1 (mem_filter.mp v).2); have hs:=he M' r (filter_subset ..) (fun i v=> (P' i (mem_filter.mp v).1).2 (mem_filter.mp v).2)
 have hJ : X1= J2- (λ₁ ⁻¹) • (r.card:ℂ) • (1:FC Μ):=by unfold J2 stains averageP; rw [sum_sub_distrib,smul_sub, sum_const,Nat.cast_smul_eq_nsmul] -- tune
 have hp : Hp' 1= M' 1:=by change L (loadF F _ (centB N 1))= L (pageF o N (loadF F _ (centB N 1))); rw [cent_one,pier]
 have hH: (3/4:ℝ) ≤ (Hp' 1).re:= by apply Librarian; change ‖L (loadF F _ (centB N 1)) -1‖ ≤ _; rw [cent_one]; exact h
 rw [map_sub]; change _ ≤ (Hp' X1-M' X1).re; rw [hJ,map_sub,map_sub]; rw [(show Hp' ((λ₁ ⁻¹) • (r.card:ℂ) • (1:FC Μ))= M' ((λ₁ ⁻¹) • (r.card:ℂ) • (1:FC Μ)) from by simp only [map_smul,hp]), sub_sub_sub_cancel_right]; rw [Complex.sub_re]; have hv:Hp' J1+Hp' J2=Hp' 1:= (map_add Hp' ..).symm.trans (congrArg Hp' ht); change (Hp' J1).re ≤ _ at hS; change (M' J2).re ≤ _ at hs; linarith only [hS,hs,hH,(show (Hp' J1).re+(Hp' J2).re=(Hp' 1).re from congrArg Complex.re hv)]
end
end combine
#print axioms satin_sv
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
