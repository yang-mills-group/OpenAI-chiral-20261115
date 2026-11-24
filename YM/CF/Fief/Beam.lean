import YM.CF.Fief.Switch
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "Q"=>SU.group
local notation "μ_"=> (Fintype.card SU.group.ColorIndex:ℝ)
structure Tip (C a b c D:ℝ)(n l B H J:ℕ) (x:ℝ): Prop where
 rate: 0≤D
 pos_t :0≤C
 pos_b :0≤ b
 pos_c :0≤c
 act : 16*J*Real.exp (D*pathPay l)*μ_*2^n*(C*tipPay a x) ≤1/2
 mat : 16*J*Real.exp (D*pathPay l)*μ_*2^n*b ≤1/2
 cot : 16*J*Real.exp (D*pathPay l)*μ_*2^n*c ≤1/2
abbrev weight_p (l m k:ℕ):ℝ:= barkQ l k m
variable{C a b c d:ℝ}{n k l m f J:ℕ}{x:ℝ}(p:Tip C a b c d n l m f J x)
lemma yard_w(l m k:ℕ) : barkQ l (k+3) m ≤ barkQ l 3 m*16^k:=by
 have ht(v:ℕ):barkQ l (v+1) m ≤ 16*barkQ l v m:=by
   let F(q):= diameterW l q m+diameterW l q m+1; change F (v+1)^4≤ 16*F v^4; rw [show 16*F v^4=(2*F v)^4 by ring]; apply Nat.pow_le_pow_left; unfold F diameterW; rw [Nat.mul_succ, Nat.add_mul,Nat.add_mul l 70]; omega
 induction k with
 | zero => simp
 | succ k ih=> exact (ht (k+3)).trans ((Nat.mul_le_mul_left _ ih).trans (le_of_eq (by rw [pow_succ]; ac_rfl)))
include p
lemma major_w (k:ℕ): let Y(q:ℕ):= weight_p l m q * (f* J^(q+1):ℕ) *tapeQ l q d *fareI C a b c x n q; Y (k+3) ≤ Y 3*(1/2)^k := by
 intro Y; let X(l':ℕ):= (↑(f*J^(l'+1)):ℝ) * tapeQ l l' d; let p0:= p; obtain ⟨hx,hC,hb,hc,p,u,v⟩:=p0
 have hp(C D:ℝ) (hp:0≤C) (hu:0≤D) (q:16*J*Real.exp (d*pathPay l)*μ_*2^n*D ≤1/2) :weight_p l m (k+3)* (X (k+3)*Lich.Muster.quota n (k+3) C D)≤ weight_p l m 3*(X 3*Lich.Muster.quota n 3 C D)*(1/2)^k:=by
    calc
     _ ≤ weight_p l m 3 * 16^k* (X (k+3)*Lich.Muster.quota n (k+3) C D) := mul_le_mul_of_nonneg_right (by exact_mod_cast yard_w l m k) (by unfold Lich.Muster.quota X tapeQ; positivity)
     _ = weight_p l m 3*(X 3*Lich.Muster.quota n 3 C D)*(16*J*Real.exp (d*pathPay l)*μ_*2^n*D)^k := by unfold X tapeQ Lich.Muster.quota; push_cast; simp only [pow_add,mul_pow]; ring -- tune power indices
     _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) q _) (by unfold weight_p X Lich.Muster.quota tapeQ; positivity)
 let h1:= hp _ _ hC (mul_nonneg hC (Real.exp_pos _).le) p
 let h2:= hp _ _ hb hb u; let h3:=hp _ _ hc hc v
 unfold Y; simp_rw [fareI]; dsimp only [X] at h1 h2 h3
 linarith only [h1,h2,h3]
-- no Norm fancy.
variable {N P B:Side}{S:StepData (Domain N B) (Domain P B)} {G:Ratio (mid N B) (mid P B)}{e:ℝ}{T:Tube SU.group S}(A:Muster G S x e T)
def costL (A:Muster G S x e T)(n:ℕ)(C a b c:ℝ)(L:Palot.leaf (Site (Domain N B))):=∑' k:ℕ, note_g n A C a b c L (k+3)
local notation "Y"=> fun (k:ℕ)=> tribute (S:=S) (3*radiusB x) C a b c n A.post k (radiusB x) d x
omit p
local notation "J₀"=>ratioB S (3*radiusB x)
lemma gproof {g:ℝ}(p:0≤ d)(h:16*J₀*Real.exp (d*pathPay l)*μ_*2^n*g≤1/2)(v:0 ≤ g): J₀*μ_*2^n*g<1:=by
 calc
  _ ≤ 16*J₀*Real.exp (d*pathPay l)*μ_*2^n*g:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (?_) (by positivity)) (by positivity)) v
  _ < 1:= lt_of_le_of_lt h (by norm_num)
 have he:1≤ Real.exp (d*pathPay l):=Real.one_le_exp (by positivity); nlinarith only [he, Nat.cast_nonneg (α:=ℝ) J₀]
lemma reach_c (h:Tip C a b c d n A.post (radiusB x) (ratioB S 1) (ratioB S (3*radiusB x)) x) : let U:ℕ→ℝ:= (Y ·); Summable (fun k:ℕ=>U (k+3)) ∧ ∑' k:ℕ,U (k+3) ≤ 2*U 3:=by
 intro U; have hh :Summable (fun k:ℕ=> U 3*((1/2:ℝ)^k)):=((summable_geometric_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).mul_left _); have hv(k:ℕ): U (k+3) ≤ U 3*(1/2)^k:= major_w h k; have hX: Summable (fun k:ℕ=>U (k+3)):=Summable.of_norm_bounded hh fun i=> (Real.norm_of_nonneg (show 0 ≤ U (i+3) from ?_)).le.trans (hv i)
 swap
 · unfold U tribute; obtain ⟨hz,u,t,w,h1,h2,h3⟩:=h; unfold fareI tapeQ Lich.Muster.quota tipPay; positivity
 exact ⟨hX,(hX.tsum_le_tsum hv hh).trans_eq (by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring)⟩
lemma roof_s (h:Tip C a b c d n A.post (radiusB x) (ratioB S 1) J₀ x) (L:Palot.leaf (Site (Domain N B))) :Summable fun k:ℕ=> note_g n A C a b c L k:= since T n A h.pos_t h.pos_b h.pos_c (L:=L) (metro n _ _ h.pos_t h.pos_b h.pos_c (gproof h.rate h.act (mul_nonneg h.pos_t (Real.exp_pos _).le)) (gproof h.rate h.mat h.pos_b) (gproof h.rate h.cot h.pos_c)) -- tune unused gproof v
lemma roof_n (p:Tip C a b c d n A.post (radiusB x) (ratioB S 1) J₀ x) : ∀ i,0≤costL A n C a b c i:=by
 intro i; apply tsum_nonneg; intro k; obtain ⟨h,u,v,x,h1,h2,h3⟩:=p; refine sum_nonneg fun i _=>sum_nonneg fun j _=>?_ ; unfold fareI Lich.Muster.quota tipPay; positivity
lemma roof_l (p:Tip C a b c d n A.post (radiusB x) (ratioB S 1) (ratioB S (3*radiusB x)) x)(h:0<radiusB x) (u:Site (Domain N B)): (∑ i:Palot.leaf (Site (Domain N B)), tallyL u i d (radiusB x)*costL A n C a b c i) ≤ 2*Y 3:=by -- precedence
 obtain ⟨hg,hx⟩:=reach_c A p
 unfold costL; simp_rw [←tsum_mul_left]; have he(i:Palot.leaf (Site (Domain N B))): Summable fun k:ℕ=> tallyL u i d (radiusB x)*note_g n A C a b c i (k+3):=((summable_nat_add_iff 3).mpr (roof_s A p i)).mul_left _
 rw [←Summable.tsum_finsetSum (fun i _=>he i)]
 exact ((summable_sum (fun i _=>he i)).tsum_le_tsum (fun k=> rapid n A p.pos_t p.pos_b p.pos_c h d p.rate u (k+3)) hg).trans hx
end YM.CF.Fief
