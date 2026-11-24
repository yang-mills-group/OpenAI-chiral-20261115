import YM.SU5.FiniteGaugeData.Hierarchy.Marble
/-! # Multiple resolutions and Borel marks of all gauge-invariant products in the same hierarchy
 Finite recipe costs and explicit error envelopes. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
local notation "U" => W (tent Y h)
local notation "M" => Motif (tent Y h)
local notation "H₁"=> Theater (tent Y h)

variable (Z:ℕ→ Finset Cover)
local notation "Hᵣ" i:max => folio Λ l Z i
local notation "Wᵣ" i:max => GridStep Λ l (folio Λ l Z i)
local notation "Dₛ" i:max => salary Y h (folio Λ l Z i) i

def Spanned (P:Call Λ l) := ∀  i < s, ‖P (folio Λ l Z i) i‖≤ salary Y h (folio Λ l Z i) i
-- input norm (catalog sup character; ≤ native sample sup norm at any Hosp) used here for factors. No normalization of recipe data at alternate cutoffs.
def pulse (t:M) (p:Region Kₜ t Z): ℕ→ℝ
 | 0 => ‖reading Kₜ (Z 0) _ (p 0)‖
 | i+1=> duration (GridStep Λ l (folio Λ l Z i)) * duration (Z (i+1)) * ((salary Y h (folio Λ l Z i) i+1)*pulse t p i)*‖reading Kₜ (Z (i+1)) _ (p _)‖
local notation "C"=>pulse Y h Z
lemma pulse_nn (t:M)(p:Region Kₜ t Z):0≤ pulse Y h Z t p s:=by
  induction s with
  | zero=>exact norm_nonneg (reading Kₜ (Z 0) _ (p 0))
  | succ s ih=>rw [pulse]; have ht:= duration_pos (Wᵣ s); have he:= duration_pos (Z (s+1)); have hx:= salary_nn Y h (folio Λ l Z s) s; positivity
variable (A B: Call Λ l)(m:Motif (tent Y h))(p:Region (tent Y h) m Z)
def forArt (ε:ℝ) := ∀ i:ℕ, i < s → ‖A (folio Λ l Z i) i-B (folio Λ l Z i) i‖≤ ε

lemma budget_erupt (g:Spanned Y h s Z A): ‖erupt Y h Z m p A s‖ ≤ (C) m p s:=by
  induction s with
  | zero=> exact le_rfl
  | succ i ih=>
    specialize ih (fun j u=>g _ (by omega)); have ht:=g i i.lt_succ_self
    rw [pulse]; let T:= (timesQ Kₜ subset_union_left subset_union_right: Catalog (Wᵣ i) →L[ℂ] Catalog (Z (i+1))→L[ℂ] Catalog ((Wᵣ i)∪ Z (i+1))) -- colon
    let c:= A (Hᵣ i) i (erupt Y h Z m p A i); let d:= duration (Wᵣ i)*duration (Z (i+1)); let a:= reading Kₜ (Z (i+1)) _ (p _); let D:= Dₛ i; have hc:‖c‖≤ (D+1)*((C) m p i):= (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul (ht.trans (le_add_of_nonneg_right zero_le_one)) ih (norm_nonneg _) (by unfold D; have he:= salary_nn Y h (folio Λ l Z i) i; positivity))  -- salary_nn needed
    change ‖T c a‖ ≤ d*((D+1)*_)*_; exact (norm_timesL Kₜ _ _ c a).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by have h0:=duration_pos (Wᵣ i); have ht:=duration_pos (Z (i+1)); positivity)) (norm_nonneg _))


private lemma tally {X Y' Z W:Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y'] [NormedSpace ℂ Y'][NormedAddCommGroup Z][NormedSpace ℂ Z][NormedAddCommGroup W][NormedSpace ℂ W]
   (P Q:X→L[ℂ] Y')(x y:X)(w:Z)(T:Y'→L[ℂ] Z→L[ℂ] W){c d a ε:ℝ}(hx:‖x‖≤a)(hxy:‖x-y‖≤ε*a)(hpq:‖P-Q‖≤ε)(hd:‖Q‖≤d)(ht:‖T‖≤c): ‖T (P x) w - T (Q y) w‖ ≤ ε*(c*((d+1)*a)*‖w‖):=by
  have he:‖P x-Q y‖ ≤ ε*((d+1)*a):=by
    have h₁:‖P x-Q x‖≤ ε*a:=(ContinuousLinearMap.le_opNorm (P-Q) x).trans (mul_le_mul hpq hx (norm_nonneg _) ((norm_nonneg _).trans hpq))
    have h₂:‖Q x-Q y‖≤d*(ε*a):= by rw [←map_sub]; exact (Q.le_opNorm _).trans (mul_le_mul hd hxy (norm_nonneg _) ((norm_nonneg _).trans hd))
    rw [← sub_add_sub_cancel (P x) (Q x) (Q y)]; exact (norm_add_le ..).trans ((add_le_add h₁ h₂).trans_eq (by ring))
  rw [←_root_.sub_apply,← map_sub]; exact (ContinuousLinearMap.le_opNorm (T _) _).trans ((mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm T _).trans (mul_le_mul ht he (norm_nonneg _) ((norm_nonneg T).trans ht))) (norm_nonneg _)).trans_eq (by ring))

lemma budget_cost (g:Spanned Y h s Z A)(t: Spanned Y h s Z B){ε:ℝ} (u:0≤ε) (a:forArt (Λ:=Λ) (l:=l) s Z A B ε):
    ‖erupt Y h Z m p A s - erupt Y h Z m p B s‖ ≤ ε*((C) m p s):=by
  induction s with
  | zero=> change ‖reading Kₜ (Z 0) _ (p 0)-reading Kₜ (Z 0) _ (p 0)‖ ≤ _; rw [sub_self,norm_zero]; exact mul_nonneg u (pulse_nn ..)
  | succ i ih=> exact tally (A (Hᵣ i) i) (B (Hᵣ i) i) _ _ (reading Kₜ (Z (i+1)) _ (p _)) (timesQ Kₜ (D:=(Hᵣ (i+1))) subset_union_left subset_union_right) (budget_erupt Y h i Z A m p (fun j v=>g j (by omega))) (ih (fun j v=>g _ (by omega)) (fun j v=>t _ (by omega)) (fun j v=>a _ (by omega))) (a _ (by omega)) (t _ (by omega)) (timesQ_budget ..)

def playTime (x:Theater (tent Y h))(p:Contract Y h Z x):= ∑ i:x.coeff.support, ‖x.coeff i.val‖ *pulse Y h Z i.val (contract_song Y h Z x p i) s
lemma play_nn (x:H₁)(p:Contract Y h Z x) :0≤ playTime Y h s Z x p:= Finset.sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (pulse_nn ..)
lemma budget_major (x:H₁)(p:Contract Y h Z x)(g:Spanned Y h s Z A): ‖major Y h s Z x p A‖ ≤ playTime Y h s Z x p:=by
  unfold major; exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=> by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (budget_erupt Y h s Z A i.val _ g) (norm_nonneg _))
lemma budget_diff (g:Spanned Y h s Z A)(t:Spanned Y h s Z B){ε:ℝ}(u:0≤ε)(a:forArt (Λ:=Λ) (l:=l) s Z A B ε)(x:H₁)(p:Contract Y h Z x):
    ‖major Y h s Z x p A-major Y h s Z x p B‖ ≤ ε*playTime Y h s Z x p:=by
  unfold major playTime; rw [←sum_sub_distrib]; apply (norm_sum_le ..).trans; rw [mul_sum]; refine sum_le_sum fun i _=>?_; rw [←smul_sub (x.coeff i.val) (erupt Y h Z i.val (contract_song Y h Z x p i) A s) (erupt Y h Z i.val (contract_song Y h Z x p i) B s),norm_smul (x.coeff i.val) (erupt Y h Z i.val (contract_song Y h Z x p i) A s- erupt Y h Z i.val (contract_song Y h Z x p i) B s), mul_left_comm ε]; exact mul_le_mul_of_nonneg_left (budget_cost Y h s Z A B i.val _ g t u a) (norm_nonneg _)
#print axioms budget_diff
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
