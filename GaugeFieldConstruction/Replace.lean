import GaugeFieldConstruction.Breath
/-!
# No transformation from double. In (99) use angular or constant.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5000
noncomputable section
namespace YM.GaugeFieldConstruction.Flux.One
open Gap Cauchy Row Phys Function Wick MeasureTheory Calibration U1 Set Filter Complex
open Lamp
open YM.Maxwell (grad)
open scoped Topology BigOperators ContDiff
variable {α : Type*} {B : Dollars} {Y x y z : E4} {χ : E4→ℝ}

/-- Buy for (87) with vector charged either scale-invariant or angular. -/
structure Cadre (K : Dollars) (x : E4) extends Course K : Prop where
  scale : ∃ s : ℝ, (s=1 ∨ s=2) ∧ ∀ i z,K i (reach x z)=s*K i z

-- both JP*f and g accounted with same exact units.
lemma shirt (X : SymT) (q : divergence X=0) (j : Axis): ∑ i:Axis,press i (dress (shells _ (X.val (ordered i j))))=0 := by
  simp_rw [← likes]
  have ht:= component_div X j; rw [q] at ht; have hv := ht.symm; clear ht
  simp_rw [show ∀ x i, P i (shells Floor.four x)=shells Floor.five (deriv i x) from fun x i=>(LinearMap.congr_fun (scene i) x).symm]
  rw [← map_sum]; simp_rw [← map_sum (shells _)]
  rw [hv]; change dress (shells _ 0)=0; simp
lemma div_tee (ac V j): (∑ i : Axis, Phys.eyes i (gStress ac i j))=0 ∧ ∑ i : Axis, bones i (fStress V i j)=0 := by
  have H : ∑ i : Axis,press i (plain i j ac V)=0:= shirt (stress ac V) ((Calibration.pure_supply _).mpr ⟨_,_,rfl⟩) j
  constructor
  · have h := congr_arg (fun x : Book=>x.2.1) H; simp only [Prod.snd_sum,Prod.fst_sum,Prod.fst_zero,Prod.snd_zero,press,LinearMap.prodMap_apply,pinG] at h -- eyes tune
    exact h
  have h := congr_arg (fun x : Book=>x.2.2.1) H; simp only [Prod.snd_sum,Prod.fst_sum,Prod.fst_zero, Prod.snd_zero,press,LinearMap.prodMap_apply,pinF] at h; exact h
lemma g_sym (ac i j) : gStress ac i j=gStress ac j i:= by unfold gStress; rw [Gauge97.uniform]
lemma f_sym (V i j) : fStress V i j=fStress V j i:= by unfold fStress; rw [add_comm (L j _) (L i _)]
private lemma low (s : ℝ) (p : s=1 ∨ s=2) (n:ℕ) (h:7≤n) : 8*(s*half n) ≠ 1 := by
  have ht : 0 < half n := by unfold half; positivity
  have hh : half n≤half 7 := pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  norm_num [half] at hh; change half n ≤ _ at hh
  rcases p with p|p <;> rw [p] <;> intro E <;> linarith

variable {Pm : Axis→Module.End ℂ (J α)} (S : Axis→Axis→J α) (R : Wick.Bil α α) (h : ∀ (i j:Axis), S i j=S j i)
    (p : ∀ j,∑ i:Axis,Pm i (S i j)=0) (l : ∀ i a b, R (Pm i a) b= -Gap.step i (R a b))
def Duo (Y : E4) (V : J α) : Forms := fun i j x=>eye (Y-x) (R (S i j) V)
include h p l
lemma theory (B' : Course B) (V) (H : z≠Y) : sumD (currentZ B (Duo S R Y V)) z=0 := by
  let T:= Duo S R Y V
  have Hs : Suit ({Y} : Set E4)ᶜ T := fun i j z x=> propL _ x
  rw [submitting (T:=T) (show z∈({Y}:Set E4)ᶜ from H) B' Hs (fun i j=>by unfold T Duo; rw [h i j])]
  apply Finset.sum_eq_zero; intro i _; apply (congr_arg (fun w:ℂ=>B i z • w) (show YM.GaugeFieldConstruction.Flux.div T i z=0 from ?_)).trans (smul_zero _)
  unfold YM.GaugeFieldConstruction.Flux.div sumD T Duo; simp_rw [propL' _ _ H,← l,← map_sum]
  rw [show (∑ j:Axis, R (Pm j (S j i)) V)=(∑ j:Axis,R (Pm j (S j i))) V from (LinearMap.sum_apply ..).symm,← map_sum,p i,map_zero,LinearMap.zero_apply,map_zero]
omit h p l in
lemma looks (B' : Course B) (V) (H : z≠Y) (a : Axis): ContDiffAt ℝ ∞ (currentZ B (Duo S R Y V) a) z := daily B' _ (fun j=>propL _ H)

lemma easy (c : Chassis x Y χ) (B' : Course B) (v): Flux χ (currentZ B (Duo S R Y v))=0 := by
  apply concentric c.toCost (fun a z hz=>looks S R B' v (fun (e:z=Y)=> c.there (e ▸ hz)) a) (fun z hz=>theory S R h p l B' v (fun (e:z=Y)=> c.there (e ▸ hz)))

lemma silence_aux (u : α → ℕ) (g : ∀ i,7≤u i) (hp : ∀ v i j,big (R (S i j) (ket v)) (u v)) (c : Chassis Y y χ) (B' : Cadre B Y) (a : J α): Flux χ (currentZ B (Duo S R Y a))=0 := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp [Flux,currentZ,Duo,YM.Maxwell.Free.exportFlux]
  | add a b ha hb =>
    have H : currentZ B (Duo S R Y (a+b))=currentZ B (Duo S R Y a)+currentZ B (Duo S R Y b) := by
      ext1 i; ext1 j; simp only [currentZ,Duo,map_add,smul_add,Finset.sum_add_distrib,Pi.add_apply]
    rw [H,pulse c (J:=currentZ B (Duo S R Y a)) (J':=currentZ B (Duo S R Y b)) ?_ ?_,ha,hb,add_zero] <;>
      exact fun i z hz=> (looks S R B'.toCourse _ (c.gate hz).1.symm _).continuousAt
  | single i r =>
    have hs : Flux χ (currentZ B (Duo S R Y (ket i)))=0 := by
      obtain ⟨x,hx,Hx⟩:= B'.scale
      apply silence (x*half (u i)) c.toCost c.here (low _ hx _ (g i)) (fun i y h=> looks S R B'.toCourse _ h _) (fun y t=> theory S R h p l B'.toCourse _ t)
      intro a y hy; unfold currentZ Duo
      rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
      rw [Hx,show Y-reach Y y=(2:ℝ) • (Y-y) from by unfold reach; simp only [add_comm Y,sub_add_eq_sub_sub]; simp [smul_sub],hp i a j _]; simp only [smul_smul]; congr 1; ring
    rw [show Finsupp.single i r=r • ket i from by simp [ket]]
    rw [show currentZ B (Duo S R Y (r • ket i))=r • currentZ B (Duo S R Y (ket i)) from ?_,atlas,hs,mul_zero]
    ext1 a; ext1 z
    simp only [currentZ,Duo,map_smul, Pi.smul_apply,Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> smul_comm ..
end YM.GaugeFieldConstruction.Flux.One
