import YM.SU5.FiniteGaugeData.Reliance.Lithic
import YM.SU5.FiniteGaugeData.Reliance.Converted
import YM.CF.Buffered.Transfer
/-! # Absolute part of the weighted high-scale estimate.

 Spend BOTH payoffs, including one examining rough plaquettes of this very Pane. Thus can
 pay for LOCAL rare-event statements with many disjoint copies of the mark, and give small bounds
 normalized on this same Course. Exponent LOBE uses `burnP` constant for the observing level
 independent of period/gate/heat-or-cap query. Precisely for evaluated f, not uniform in
 fundamental cutoff measured in changing terminal resolution. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Reliance
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Window Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova YM.Next.Rank Emu
open Advance Afterglow
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal NNReal Classical
attribute [local instance] opCStarAlgebra
variable {m B N L':Side}{a c v θ C L γ μ r w g h x e σ τ ρ vA y k zz: ℝ} {j n n':ℕ} {O:Odd L'.val}{Y:Pricing j L' O (Thread j)} {P:Grasp Y B e}

def fare (x:Clip)(g:ℝ):ℝ:= strength x/(2*g)
lemma fare_n (x:Clip) {g:ℝ}(p:0<g):0<fare x g:= div_pos (strength_pos _) (by positivity)
lemma wholeCup (V:GramM N)(g:ℝ)(U:Pane N): glow (fare V.funds g) univ U=basal V g U:=by
 rw [glows]; unfold basal; refine sum_congr rfl fun p _=>?_ ; unfold lobe fare; rw [div_div_eq_mul_div]; ring

section absolute
-- allow tags only indirectly. weighted bound at each published field; no continuity required.
def Apt (r c:ℝ)(S: Support (More N))(f : Mark N): Prop:= ∀ V:Fields N,‖f V‖ ≤ c*Real.exp (glow r S V.1)
lemma apt_pos {f:Mark N} {S:Support (More N)}(p:Apt r c S f):0 ≤ c:= nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (p (1,1))) (Real.exp_pos _)
lemma apt_base (S:Support (More N)){f:Mark N}(p:0 ≤ r)(h:0 ≤ c)(t:∀ x, ‖f x‖ ≤ c): Apt r c S f:=fun x=> (t x).trans (le_mul_of_one_le_right h (Real.one_le_exp (glow_n r p S x.1)))
lemma apt_cap {f:Mark N}{S:Support (More N)}(p:0 ≤ r)(t:Apt r c S f)(v :ℕ)(h:S.card≤v)(x:Fields N): ‖f x‖ ≤ c* Real.exp (posted r v):=(t x).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (glow_cap r p _ _ v h)) (apt_pos t))

local notation "Λ"=> mid m B
local notation "M"=> More (mid m B)
variable (A:HaarBudget SU.group)(V:GramM (mid m B))(S:Loom (mid m B))(R:Ledger h v θ r C V)(p:V.path.Bounds V.funds μ γ L)(H:Roof (mid m B) x e n S)(t:0<g)(b:V.beta*g^2=1)(k':g ≤ V.p.threshold)(hu:P.roundZ ≤ (mid m B).val)(F:1 ≤ h)(u:0 ≤ r)(eA:0 ≤ C)
local notation "TU"=> flagBill Λ v θ C
local notation "taxW"=> taxY M V.beta V.p.threshold γ L
local notation "faces" => (Fintype.card (Face (Per M)):ℝ)
local notation "rs"=> fare V.funds g
local notation "me"=> recX P V S
include R p H t b k' hu F u eA
lemma grantW (x:Orbit Λ):
    ‖recX P V S x‖ ≤ Real.exp (flagBill Λ v θ C+taxY M V.beta V.p.threshold γ L+ faces-2*basal V g x.1):=by
 have he :‖Graph.beam V P S x‖ ≤ Real.exp (flagBill Λ v θ C):=by
    let A:=Graph.cab V P S x; exact (spentS _ _ A).trans (by rw [(sea_g hu (S x) (H.paid _) V.J.M).2,mul_one]; exact extensive_mile R x u F eA ((P.broadness _ hu _).projection _ (H.paid _)))
 have hf :Graph.past V x.1≤ Real.exp (taxW+faces-2*basal V g x.1):=by
    have ht:= per_channel p t b k' x.1; rw [←full_basal] at ht; apply Real.exp_monotone; linarith only [ht]
 rw [porch,norm_smul,Real.norm_of_nonneg (show 0 ≤ Graph.past .. from (Real.exp_pos _).le)]; exact (mul_le_mul hf he (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add]; ring_nf)

-- full expense even with the weighted mask. p depends on V here; later price via common β lower & s.
theorem tariff {W:Support (More (mid m B))}(f: Mark (mid m B))(pA:Apt a c W f)(hA:0 ≤ a)(hV:a ≤ fare V.funds g):
    ‖num0 P V S f‖ ≤ c*Real.exp (flagBill Λ v θ C+faces/2) * fullRate A V γ L g:= by
 let F0:=TU+taxW+faces; let U0:=Real.exp F0; have he:0 ≤ c:= apt_pos pA; let B':= fun i:Orbit Λ=> Real.exp (-basal V g i.1)
 obtain ⟨hi,Y0⟩:= repays A V t
 unfold num0 markedRead; apply le_trans (norm_integral_le_integral_norm ..)
 apply le_trans (b:=∫ i,(c*U0)*B' i∂city _); swap
 · rw [integral_const_mul]; apply (mul_le_mul_of_nonneg_left Y0 (mul_nonneg he (Real.exp_pos _).le)).trans_eq; unfold F0 fullRate; rw [mul_assoc, mul_assoc c,←mul_assoc (Real.exp _),←Real.exp_add]; congr 3; ring
 refine integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (hi.const_mul _) (Eventually.of_forall fun i=>?_)
 let z:=drawn S i; let W:=basal V g i.1 -- shadow W
 have hp: ‖f z‖ ≤ c*Real.exp W:= (pA z).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (
    (fill_till a _ z.1 rs hA hV).trans ((glow_grows rs (fare_n V.funds t).le (Finset.subset_univ _) z.1).trans_eq (wholeCup V g i.1)))) he)
 apply le_trans (mark_bound (f z) _) -- tune
 refine (mul_le_mul hp (grantW V S R p H t b k' hu F u eA _) (norm_nonneg _) (mul_nonneg he (Real.exp_pos _).le)).trans_eq ?_
 unfold U0 F0 B'; dsimp only; rw [mul_assoc c, mul_assoc c,←Real.exp_add, ← Real.exp_add]; unfold W; ring_nf
end absolute
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.tariff
