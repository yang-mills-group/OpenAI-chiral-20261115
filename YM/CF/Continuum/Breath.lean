import YM.CF.Continuum.PayTax
import YM.CF.Continuum.Billhead

/-!
# Extensive absolute bounds in the SAME history

Integrate while retaining the small coupling Gaussian factor, and (separately)
using a lower bound on the flag cost. See `payLedger`. Missing constant factors
at handles are not in this cost and can be budgeted later for the volume growth
allowed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank Emu
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {α:Type*} {m B N L':Side} {a c v θ C L γ μ r w g h x e σ τ ρ vA y k : ℝ} {j n n':ℕ} {O:Odd L'.val}{Y:Pricing j L' O (Thread j)} {P:Grasp Y B e}

def rebate (O:HaarBudget group)(V:GramM N)(g:ℝ):= (O.big * ((2*g)/strength V.funds)^group.lieDim)^(3*Fintype.card (Site (More N))-3)
def fullRate (O:HaarBudget group)(V:GramM N)(C L g:ℝ):= Real.exp (taxY (More N) V.beta V.p.threshold C L+Fintype.card (Face (Per (More N)))/2)*rebate O V g -- choose /2 reboost using half primary + half basal without flag

def basal (V:GramM N)(g:ℝ)(U:Pane N):ℝ:= ∑ p: Face (Per (More N)), group.chord (faceValue U p)/((2*g)/strength V.funds)
lemma full_basal (V:GramM N)(U:Pane N) : 2*basal V g U=∑ p: Face (Per (More N)), group.chord (faceValue U p)/(g/strength V.funds):=by
 unfold basal; rw [mul_sum]; apply sum_congr rfl; intro i _; simp only [div_div_eq_mul_div]; rw [show (2:ℝ)*g=g*2 by ring,mul_div_assoc',div_mul_eq_div_div]; ring -- tune

lemma past_budget (V:GramM N)(p:V.path.Bounds V.funds μ C L)(t:0<g)(e:V.beta*g^2=1)(h:g≤V.p.threshold)(u:Pane N)(wX :0≤w) (Y: w≤V.funds.linear ∨ w=0)(a: flags V.p.threshold u≠∅ ∨ w=0) :
   Graph.past V u ≤ Real.exp (taxY (More N) V.beta V.p.threshold C L + Fintype.card (Face (Per (More N)))/2 - V.beta * (w*V.p.threshold^2)/2)*Real.exp (-basal V g u):=by
 rw [←Real.exp_add]; refine Real.exp_monotone ?_; have he:= per_channel p t e h u
 rw [←full_basal] at he; have hu:0≤ V.beta:= (variance_beta t e).le; have hf:kinetic (More N) V.p C L V.beta w≤ V.path.inChannels V.funds V.p V.beta u:=by
   rcases a with (a|a)
   · exact fullH p V.p u wX (Y.elim id fun e=> e ▸ V.funds.tail_pos.le) hu a
   subst w; unfold kinetic; rw [zero_mul,mul_zero,zero_sub]; exact energy_low V.p V.path V.funds p hu u
 unfold kinetic at hf; linarith only [hf,he]

lemma repays (O:HaarBudget group)(V:GramM N)(t:0<g):
   Integrable (fun i: Orbit N=> Real.exp (-basal V g i.1)) (city _) ∧ ∫ i : Orbit N, Real.exp (-basal V g i.1) ∂city N ≤ rebate O V g:=by
 let T:= (2*g)/strength V.funds; have hp : 0<T:= div_pos (by positivity) (strength_pos _)
 let G(u):= Real.exp (-(group.chord u/T)); have hg:Continuous G:= by unfold G; fun_prop
 let M:=More N; have hq(i:Pane N):Real.exp (-basal V g i)=∏ p:Face (Per M), G (faceValue i p):=by unfold G basal T M; rw [←sum_neg_distrib,Real.exp_sum]
 have hx: Integrable (fun U:Pane N=>Real.exp (-basal V g U)) (prior group M):= by
    simp_rw [hq]; exact (continuous_finsetProd _ fun i _ => hg.comp (continuous_travel _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 refine ⟨((measurePreserving_fst (μ:=prior group M) (ν:=depot N)).integrable_comp hx.aestronglyMeasurable).mpr hx,?_⟩
 rw [show (∫ i:Orbit N,Real.exp (-basal V g i.1) ∂city _)=_ from (usesPrior _ hx)]
 simp_rw [hq]; have hu:1<M.val:=by unfold M More; have he:=N.property; exact lt_of_lt_of_le (show (1:ℕ)<2 from (by decide)) (Nat.le_mul_of_pos_left _ he)
 exact (Next.Rank.Axial.elimination hu G hg (fun i=>(Real.exp_pos _).le) (fun i=>Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (group.chord_nonneg i) hp.le)))).trans (pow_le_pow_left₀ (integral_nonneg fun i=> (Real.exp_pos _).le) (O.high T hp) _)

section cost
local notation "Λ"=> mid m B
local notation "M"=> More (mid m B)
variable (A:HaarBudget group)(V:GramM (mid m B))(S:Loom (mid m B))(R:Ledger h v θ r C V)(p:V.path.Bounds V.funds μ γ L)(H:Roof (mid m B) x e n S)(t:0<g)(b:V.beta*g^2=1)(k':g ≤ V.p.threshold)(hu:P.roundZ ≤ (mid m B).val)(F:1 ≤ h)(u:0 ≤ r)(eA:0 ≤ C)
local notation "sA"=>flagBill Λ v θ C
include R H hu F u eA
private lemma wave_upper (x: Orbit Λ) : ‖Graph.beam V P S x‖ ≤ Real.exp (flagBill Λ v θ C) := by
 let A:=Graph.cab V P S x; exact (spentS _ _ A).trans (by rw [(sea_g hu (S x) (H.paid _) V.J.M).2, mul_one]; exact extensive_mile R x u F eA ((P.broadness _ hu _).projection _ (H.paid _)))
include p b k' t
private lemma billW (x:Orbit Λ) (wX:0≤w) (Y: w ≤ V.funds.linear ∨ w=0) (a:x∉Lace V∨w=0) :
  ‖recX P V S x‖ ≤ Real.exp (sA + taxY M V.beta V.p.threshold γ L + Fintype.card (Face (Per M))/2 - V.beta*(w*V.p.threshold^2)/2)* Real.exp (-basal V g x.1):=by
 let z:=wave_upper V S R H hu F u eA x; rw [porch,norm_smul, Real.norm_of_nonneg (show 0≤past V x.1 from (Real.exp_pos _).le)]
 apply le_trans (mul_le_mul (past_budget V p t b k' x.1 wX Y a) z (norm_nonneg _) ((Real.exp_pos _).le.trans (past_budget V p t b k' x.1 wX Y a)))
 apply le_of_eq; rw [mul_right_comm,←Real.exp_add]; congr 2; ring

/-- Core absolute-mass estimate of the history at this scale (NOTE right side
`fullRate` already has the factor from gauge integral). Use integrability with
available extra epoch grants/Fleet. -/
theorem payLedger (K: Integrable (recX P V S) (city Λ)) :
    (∫ x:Orbit Λ, ‖recX P V S x‖ ∂city _) ≤ Real.exp (flagBill Λ v θ C) * fullRate A V γ L g:= by
  let B0:=taxY M V.beta V.p.threshold γ L+ Fintype.card (Face (Per M))/2
  let X:=Real.exp (sA + B0); let W(i:Orbit Λ):=Real.exp (-basal V g i.1); obtain ⟨i0,Y0⟩:=repays A V t
  have hi: (∫ x:Orbit Λ, ‖recX P V S x‖ ∂city _) ≤ ∫ i:Orbit Λ,X*W i∂city _:=by
    apply integral_mono K.norm (i0.const_mul _) fun i=>?_ ; have he:=billW V S R p H t b k' hu F u eA i (w:=0) le_rfl (Or.inr rfl) (Or.inr rfl); rw [zero_mul,mul_zero,zero_div,sub_zero,add_assoc] at he; exact he
  rw [integral_const_mul] at hi; unfold fullRate; calc
    _ ≤ X*∫ i:Orbit Λ,W i∂city _:= hi
    _ ≤ X*rebate A V g := mul_le_mul_of_nonneg_left Y0 (Real.exp_pos _).le
    _ = _:=by unfold X; rw [Real.exp_add,mul_assoc]
theorem payAway (q:0≤w)(wX:w≤ V.funds.linear)(K: Integrable (recX P V S) (city Λ)) :
    (∫ x:Orbit Λ, ((Lace V)ᶜ.indicator (fun i=>‖recX P V S i‖) x) ∂city Λ) ≤ Real.exp (sA - V.beta*(w*V.p.threshold^2)/2) * fullRate A V γ L g:= by
  let D:=Lace V; let B0:=taxY M V.beta V.p.threshold γ L+ Fintype.card (Face (Per M))/2
  let U:=Real.exp (sA - V.beta*(w*V.p.threshold^2)/2+B0); let W(i:Orbit Λ):=Real.exp (-basal V g i.1); obtain ⟨i0,Y0⟩:=repays A V t
  apply le_trans (b:=∫ i:Orbit Λ, U*W i∂city Λ)
  · refine integral_mono (K.norm.indicator (lace_m V).compl) (i0.const_mul _) fun i=>?_; by_cases k:i∈Dᶜ; rw [Set.indicator_of_mem k]; have he:=billW V S R p H t b k' hu F u eA i q (Or.inl wX) (Or.inl k); exact he.trans_eq (by unfold U; congr 2; unfold B0; ring)
    rw [Set.indicator_of_notMem k]; unfold U W; positivity
  rw [integral_const_mul]; refine (mul_le_mul_of_nonneg_left Y0 (Real.exp_pos _).le).trans_eq ?_; unfold fullRate B0; rw [Real.exp_add,mul_assoc]
end cost
end YM.CF.Window
