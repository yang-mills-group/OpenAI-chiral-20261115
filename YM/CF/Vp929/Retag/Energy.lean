import YM.Extra.WILSON_STARTUP.Funds
import YM.CF.Vale.Bob
import YM.CF.Mica.Slide
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.SplitFlag
open Lattice Wilson RG Function MeasureTheory Filter Finset
open PathData Reef Cube Skye WilsonStartup
open scoped Topology Matrix.Norms.Frobenius Classical
local notation "G"=> SU.group
variable {n:Side} (c : Clip) (b p : BudgetPoint) (β : ℝ) (D : Support (More n)) (U : Pane n)
private lemma pocket_charge {σ A : ℝ} (hs : 0 < σ) {k : ℕ} (F : ℕ→ Atom G k) (H : SumBudget (fun i↦ (F i).budget σ) A) (o : Seat n) :
    atomSeries (pocket k ∘ F) b U o = (atomSeries F b U o + atomSeries F b (echo U) o)/2 := by
  have ht (i : ℕ) : (pocket k (F i)).footprint o = (F i).footprint o:= rfl
  unfold atomSeries
  have h₁:= (atom_dominated F b o hs H).summable U; have h₂:= (atom_dominated F b o hs H).summable (echo U)
  rw [← h₁.tsum_add h₂, div_eq_mul_inv,← tsum_mul_right]; refine tsum_congr fun i=>?_
  unfold Atom.placed; simp only [comp_apply, ht]
  by_cases v : Healthy b.threshold ((F i).footprint o) U
  · rw [masked_eq _ _ _ _ v, masked_eq _ _ _ _ v,masked_eq _ _ _ _ (by rwa [Healthy, Beau.flags_l])]; unfold Atom.unmasked; simp_rw [tollSlot]; rw [←div_eq_mul_inv]; exact aqua_e ..
  rw [masked_ne _ _ _ _ v,masked_ne _ _ _ _ v,masked_ne _ _ _ _ (by rwa [Healthy, Beau.flags_l])]; simp
private lemma channels_echo (hc : c.direct ≤ 1) :
    let T:=Design.top G c; (solvent T).inChannels c b β U=(T.inChannels c b β U + T.inChannels c b β (echo U))/2:= by
  obtain ⟨v,hv,H⟩:= Design.bound_arbitrary c G hc 1 one_pos; intro T
  have hp := H v le_rfl 0 le_rfl
  have he(V:Pane n) : (solvent T).principal c b β V=(T.principal c b β V+T.principal c b β (echo V))/2:=by
    have h₁:=fun x=> pocket_charge (n:=n) b V one_pos T.cubic hp.three x; have h₂:= fun x=> pocket_charge (n:=n) b V one_pos T.quartic hp.four x
    unfold PathData.principal; rw [show (solvent T).baseTerm c b=T.baseTerm c b from rfl]; simp_rw [Beau.base_K b T hp,show (solvent T).cubic=_ from (rfl : _=pocket 3∘T.cubic),h₁, show (solvent T).quartic=pocket 4 ∘ T.quartic from rfl,h₂,show (solvent T).loop=T.loop from rfl, Beau.place_v b T.loop (fun i=>twoK _ (hp.invariant i).1),sum_add_distrib,←sum_div,sum_add_distrib]; ring
  unfold inChannels; simp_rw [he,echo_p, ← sum_div,sum_add_distrib]; ring

def widen : BudgetPoint:={ b with B:=2*b.B, B_pos:=by have:=b.B_pos; positivity }
abbrev tiles:=region (n:=More n) (widen b) D
lemma tiles_spec : tiles b D= halo (4*b.B) D := by ext x; simp [tiles,region,mem_pad,widen,halo_spec,←mul_assoc,show 2*2=4 from rfl]
-- residual subtraction. monotone mask makes this the Healthy-old, not Healthy-new subtraction.
def maskK (i : Key (More n)) := masked b.threshold i.skin (Key.accrual i : Config G (More n) → ℝ)
def debt (i : Key (More n)) : ℝ:= Key.owed c b i U - Design.bulk c * (maskK p i U-maskK b i U)
def book : ℝ:=share* ∑ i:Key (More n), if i.native∈ halo b.B D then debt c b p U i else 0
def tagEnergy:=(book c b p D U+book c b p D (echo U))/2
lemma older (t s : ℝ) (hs : t ≤ s) : flags s U ⊆ flags t U:=by intro i hi; obtain ⟨j,hj,h⟩:= (flags_spec ..).mp hi; exact (flags_spec ..).mpr ⟨j,hj,hs.trans_lt h⟩
lemma mask_le (h : b.threshold ≤ p.threshold) (X : Support (More n)) (he : Healthy b.threshold X U) : Healthy p.threshold X U:= he.mono_right (older U _ _ h)
lemma debt_zero (i : Key (More n)) (H : Decent c b) (h : b.threshold ≤ p.threshold) (hv : i.native ∉ halo b.B (flags b.threshold U)) : debt c b p U i=0:= by
  have ha : Healthy b.threshold i.skin U := Finset.disjoint_left.mpr fun j hj hu=> hv (halo_spec.mpr ⟨j,hu,(separation_comm _ _) ▸ (i.nearby hj).trans H.radius⟩)
  rw [debt, Key.owed_zero _ _ _ H hv,maskK,maskK,masked_eq _ _ _ _ ha, masked_eq _ _ _ _ (mask_le b p U h _ ha)]; ring
lemma book_sum (H : Decent c b) (P : Decent c p) (h : b.threshold ≤ p.threshold) (he : flags p.threshold U=∅) :
    let T:=Design.top G c; T.inChannels c p β U - T.inChannels c b β U = β * ∑ q∈ parts (widen b) (flags b.threshold U), book c b p q U := by
  let D := flags b.threshold U
  have hp (i: Key (More n)) : Key.owed c p i U=0:=Key.owed_zero _ _ _ P (by simp [he,halo_spec])
  have hm := channel_split c p U P.direct β; have hy:= channel_split c b U H.direct β
  simp only [hp,sum_const_zero,mul_zero,add_zero] at hm
  have hb(q : Support (More n)) : halo b.B q ⊆ region (widen b) q := by change halo _ _ ⊆ tiles b q; rw [tiles_spec]; exact Corona.halo_mono (by omega) (Subset.refl _)
  have ht (i : Key (More n)) : (∑ q∈parts (widen b) D, if i.native∈halo b.B q then debt c b p U i else 0) = debt c b p U i := by
    by_cases hx : i.native ∈ halo b.B D
    · obtain ⟨x,hx,hx'⟩ := halo_spec.mp hx; let Y := Ac.burst (pad (widen b)) D x
      have hY : Y∈parts (widen b) D := mem_image_of_mem _ hx
      have hy : i.native∈halo b.B Y := halo_spec.mpr ⟨x,(Ac.bright ..).mpr ⟨hx,.refl⟩,hx'⟩
      rw [sum_eq_single_of_mem Y hY _, if_pos hy]; intro z hz hn; rw [if_neg]; exact fun g=> Finset.disjoint_left.mp (Ac.separate _ D hz hY hn) (hb z g) (hb Y hy)
    simp [debt_zero c b p U i H h hx]
  intro T; unfold book; rw [←mul_sum,sum_comm]; change _=β*(share*∑ i:Key (More n),∑ q∈parts (widen b) D, _); simp_rw [ht,debt,maskK,sum_sub_distrib,←mul_sum,sum_sub_distrib]; dsimp only [T]; linarith only [hm,hy]
lemma energy_sum (H : Decent c b) (P : Decent c p) (h : b.threshold ≤ p.threshold) (he : flags p.threshold U=∅) :
    let T:=solvent (Design.top G c); T.inChannels c p β U - T.inChannels c b β U = β * ∑ q∈ parts (widen b) (flags b.threshold U), tagEnergy c b p q U := by
  intro T; have hf : echo U ∈ {x:Pane n | flags p.threshold x=∅}:= by change flags _ _=_; rwa [Beau.flags_l]
  have ht:= book_sum c b p β U H P h he; have hv:= book_sum c b p β (echo U) H P h hf; rw [Beau.flags_l] at hv; unfold tagEnergy; rw [←sum_div,sum_add_distrib]; dsimp only [T]; rw [channels_echo c p β U P.direct, channels_echo c b β U H.direct]; dsimp only at ht hv; linarith only [ht,hv]
end YM.CF.SplitFlag
