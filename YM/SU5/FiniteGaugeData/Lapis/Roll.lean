import YM.SU5.FiniteGaugeData.Lapis.Flood
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Precision Tree Pressure Laurent Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Gaussian
open Drachma Affiche Galope Avenue Galope.Press Wrist Poeme Haute Punch Affiche Lantern Lantern.Cup RouteM Rally Syl
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Dig
variable {n: Side}{G: Gauge}{Z: Finset (Site n)} {M w k:ℕ} {C κ K α L β a Δ μ g:ℝ} {p:BudgetPoint}{P:Bed}{u:Stage}{R:PathData G} {S:Arms G u} {A:Finset (Cell n)} {F:Portion n G→ℝ}{J':ChartRatio G}{ε:ℝ}
local notation "α'" => heightK p M
local notation "η" => bonusK p u β
local notation "I" => buy Z k
local notation "J" => Plush G (buy Z k)
variable (T: Attains S J' n p β α μ M k w)(hz:Z⊆ glow A M) (D:Floor P u.clip n a C)(w0:0<a)(W:R.Bounds u.clip u.width u.paths Δ)(B:Attached P R)(O:Ocean G (buy Z k))
local notation "r'"=> gross w u β α
local notation "ZK"=> zodiac P G (buy Z k)
local notation "H"=> heatC (billsC k w Z) W B
local notation "M'"=> primeShare w u
open Cold Recruit
open Drachma.Tame Drachma.Tokens
local notation "ρ₀" => Real.sqrt β/Real.sqrt r'
local notation "c'" => greatF S n w M p β α Δ
local notation "Vt" => ser n
local notation "Ψ" => High W B D F κ w0

open Drachma.Tame Drachma.Tokens Cold Sage CF.Window.Steve
private lemma tax_faces (Z:ℝ): ∑ i:Finset (Cell n), Real.exp (i.card*Z) ≤ Real.exp ((ser n) * Fintype.card PlaqAxes * Real.exp Z):=by
 have he(x:Finset (Cell n)): Real.exp (x.card*Z)=∏ i∈x,Real.exp Z:=by rw [Real.exp_nat_mul,prod_const]; -- tune
 have hp : ∑ i:Finset (Cell n), Real.exp (i.card*Z)=∏ i:Cell n,(Real.exp Z+1):=by simp_rw [he]; rw [Finset.prod_add_one]; congr
 rw [hp]; calc
    _ ≤ ∏ i:Cell n,Real.exp (Real.exp Z):= prod_le_prod (fun _ _=>by positivity) (fun _ _=>Real.add_one_le_exp _)
    _ = _:= by rw [← Real.exp_sum, sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul]; unfold ser; push_cast; rfl

-- Amount licensing across every reality chamber even on ORIENTED critical.Roll to BP16 color score.
abbrev cameoX (Q:Config G n→ℝ)(s:Signed)(U:Config G n):= Q (pull s⁻¹ 0 U)
structure SealX (K:ℝ) (p:BudgetPoint)(L:ℝ)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C)(w0:0<a)(Q:Config G n→ℝ)(β κ δ:ℝ)(w:ℕ): Prop where
 pay : Envelope Q
 stamp : ∀ s: Signed, ∃ F:Portion n G→ℝ, Opal L F ∧ High W A D F κ w0 ≤ K ∧ ∀ Y: Finset (Cell n), Boat (cameoX Q s) W A p F Y (glow Y (lic w)) (lic w) (coreN w) w κ β δ
lemma charter (S:Arms G u)(b:LocalRatio J')(pL:0≤ L)(g:0≤Δ)(e:0<ε)(C:ℝ):∀ᶠ x in atTop,∀ β:ℝ,x/2≤β→β≤2*x→ ∀ p:BudgetPoint,p.threshold=temp x→∀ n:Side, Intro n (radiusB x)→∀ R:PathData G,∀ W:R.Bounds u.clip u.width u.paths Δ,∀ (P:Bed)(a:ℝ)(D:Floor P u.clip n a C)(w0:0<a)(B:Attached P R)(κ:ℝ),|κ|≤2 → ∀ (r δ K:ℝ), r ≤ bonusK p u β /2 →∀ Q:Config G n→ℝ,SealX K p L W B D w0 Q β κ δ (radiusB x)→
 (∫ V:Config G n, Real.exp (Q V) * colored u R r β p V ∂prior G n) ≤ Real.exp (angular n J' P β+ K + (δ+ε+service L)*ser n):=by
 let d:= ε/2; have hd:0<d:=half_pos e; have hz:Tendsto (fun x => (Fintype.card PlaqAxes:ℝ) * Real.exp (-(frostM u x/4))) atTop (𝓝 0):= by
    have hr:= (frost_t u).atTop_div_const (r:=4) (by norm_num); simpa only [mul_zero] using! (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hr)).const_mul (Fintype.card PlaqAxes:ℝ) -- tune
 filter_upwards [official S b pL g hd C,eventually_gt_atTop (0:ℝ),hz.eventually (ge_mem_nhds hd)] with x H' h' y β t v p pp n p' R W P a D hi B κ hκ r δ K hv Q q
 let c:=angular n J' P β+ K + (δ+ service L)*ser n; let E(i:ℝ):=Real.exp (c+i*ser n); let μ:=prior G n; let k₁:=-(frostM u x /4); let e(s:Signed)(V:Config G n):= Real.exp (cameoX Q s V - R.principal u.clip p β V); let f(s:Signed)(V:Config G n):= Real.exp (tribute r p V)*e s V
 have he(s:Signed): Envelope (e s):=by have he: Envelope ((cameoX Q s)):= int_e Q q.pay _ (prior_pull s⁻¹ (0:Site n)).measurable; unfold e; simp_rw [sub_eq_add_neg]; exact (he.add (PathData.principal_env W p β).neg).exp -- tune names
 have hf(s: Signed): Envelope (f s):= covering p r (he s)
 have hr₀:= bonus_fit u x h' p pp t; have hsum(s:Signed) : (∫ V,f s V∂μ) ≤ E ε:= by
    obtain ⟨F,pF,hF,AF⟩:= q.stamp s; let U(A:Finset (Cell n)):=grains (e s) A p.threshold
    have hU(A:Finset (Cell n)):Envelope (U A):=protectedA A _ (he s)
    have ht(A:Finset (Cell n)): Real.exp (A.card*r)*(∫ v, U A v ∂μ) ≤ E d * Real.exp (A.card*k₁) :=by
       let a':ℝ:= A.card; have hz:0≤a':=Nat.cast_nonneg _; apply le_trans (mul_le_mul_of_nonneg_left (H' β t v p pp n p' R W P a D hi B κ hκ A δ (cameoX Q s) (U A) F (AF A) pF (hU A) ?_) (Real.exp_pos _).le) ?_
       · intro i b; by_cases ht:misses i p.threshold=A; · exact ⟨(commit i).mp ht,(Set.indicator_of_mem (show i∈closedM _ p.threshold A from ht) _).le⟩
         exact False.elim (b (Set.indicator_of_notMem (show i∉closedM _ p.threshold A from ht) _))
       unfold E; rw [← Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; unfold c k₁; linarith only [mul_le_mul_of_nonneg_left hv hz, mul_le_mul_of_nonneg_left hr₀ hz,hF]
    rw [show f s=(fun U:Config G n=> _) from eats r p (e s),integral_finsetSum]; swap; · exact fun A _=> ((hU A).integrable _).const_mul _
    simp_rw [integral_const_mul]; apply (sum_le_sum (fun i _=>ht i)).trans; rw [←mul_sum]; apply (mul_le_mul_of_nonneg_left (tax_faces k₁) (Real.exp_pos _).le).trans; unfold E; rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left (show (Fintype.card PlaqAxes:ℝ)*Real.exp k₁≤ε-d from (by unfold d; linarith only [show (Fintype.card PlaqAxes:ℝ)*Real.exp k₁≤ε/2 from y])) (show 0 ≤ ser n from Nat.cast_nonneg _)] -- tune
 let F(s:Signed)(V:Config G n):= f s (pull s 0 V); have hF(s: Signed): Envelope (F s):= int_e (f s) (hf s) _ (prior_pull s (0:Site n)).measurable -- tune
 have hu'(s:Signed):(∫ V,F s V∂μ)≤ E ε:=by
    have hm:= (prior_pull s (0:Site n) (G:=G)); have hi':= integral_map (μ:=μ) (f:=f s) hm.measurable.aemeasurable (hf s).meas.aestronglyMeasurable; rw [hm.map_eq] at hi'; exact (hsum s).trans' hi'.ge
 let X(V:Config G n):= Real.exp (Q V)*colored u R r β p V; have hX: Envelope X:= q.pay.exp.mul (color_cost r β p W)
 let t':=(Fintype.card Signed:ℝ)⁻¹; let Y:=fun V:Config G n=> t' * (∑ i:Signed,F i V); have hx(V:Config G n): X V≤Y V:=by
    let K(i:Signed):=R.principal u.clip p β (pull i 0 V); have he(i:Signed): F i V= (Real.exp (Q V)* Real.exp (tribute r p V)) * Real.exp (-K i):= by unfold F f e cameoX; rw [pull_pull, show affine i (0:Site n) 0=0 from (by simp [affine]),mul_inv_cancel,pull_id,tribute,match_miss]; unfold K tribute; rw [sub_eq_add_neg,Real.exp_add]; ring -- tune
    unfold X colored Y PathData.inChannels; simp_rw [he]; rw [← Finset.mul_sum, mul_left_comm t', ← _root_.mul_assoc (Real.exp (Q V))]; apply mul_le_mul_of_nonneg_left (air_stride (fun i=> K i)) (by positivity) -- tune
 apply (integral_mono (hX.integrable μ) ((integrable_finsetSum _ (fun i _=>(hF i).integrable μ)).const_mul t') hx).trans; change ∫ x,Y x∂μ ≤_ ; unfold Y; rw [integral_const_mul,integral_finsetSum]; swap; · exact fun i _=>(hF i).integrable _
 apply ((mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>hu' i)) (by unfold t'; positivity :0≤t'))).trans_eq; simp only [sum_const,card_univ,nsmul_eq_mul]; rw [←mul_assoc,show t'* ↑(Fintype.card Signed)=1 from inv_mul_cancel₀ (by exact_mod_cast Fintype.card_pos.ne'),one_mul]; unfold E c; congr 1; ring
end Dig
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Dig.charter
