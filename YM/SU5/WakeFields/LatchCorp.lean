import YM.SU5.WakeFields.BurialMap

/-! # Salaries on a total tilted tape (BeatL lower–theta) -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson RG Scroll Fock Cadre Stax Mew Roots
open Push.AbsoluteSums Trees Ione MeasureTheory Finset
open Cube Lat Tulip Skye Scree Hake Jet Sault Vow Vow.TreasuryFog
open scoped Topology ContDiff BigOperators Classical YM.CF.Mew
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Palot Leaf
variable {n:Side} {P:BudgetPoint} {a b h:ℝ} {q : ℕ} {I : Type} [LinearOrder I] [Fintype I]

abbrev agenda (V : I → Bag n)(z:Key I) : Bag n:= ∑ i : I, z i • V i
-- full quota of new mark per physical root in old z-diagonal. variable
lemma tapeBuy {σ:I→ Seat n} {t:ℕ} (p:Force_M P.B σ t) (C : I→ Bag n) (r:ℝ) (u:∀ i, Barrage P q ({σ i}:Support (More n)) h (C i) (r+discount P.B) a b)
    (x:0 ≤ a)(y:0≤ b)(z:Key I)(w:z∈hill I) :
    ∃ (Y W:Aura n→ℝ), (∀ X,Flight P q X h (agenda C z X) (Y X) (W X)) ∧
       ∀ i:Seat n, Cadre.nook (Y*tact r P.B) i ≤ coastU P.B t*a ∧ Cadre.nook (W*tact r P.B) i≤ coastU P.B t*b := by
 have ha(i:I): Barrage P q ({σ i}:Support (More n)) h (z i • C i) (r+discount P.B) a b:=
    ((u i).swell (z i)).bigR (mul_le_of_le_one_left x (hill_i.mp w i)) (mul_le_of_le_one_left y (hill_i.mp w i))
 choose v l H Q G R using fun i=> (ha i).price
 let Y:= ∑ i,v i; let W:=∑ i,l i
 have hp(i j)(g:σ i∉j.val): v i j=0∧ l i j=0:= (Q i j (by simpa using g)).2
 have hv:0≤v:=fun i j=>(H i j).tube.price
 have hl:0≤l:=fun i j=>by obtain ⟨f,h,-⟩:=(H i j).forms; exact h.price
 have hx(j:Aura n): Flight P q j h (agenda C z j) (Y j) (W j) := by
    unfold agenda Y W; rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply]; exact Flight.whole _ _ _ _ fun i _=>H i j
 exact ⟨Y,W,hx,fun i=>⟨coastTransit P σ t p v hv (fun i j h=>not_not.mp (mt (fun w=> (hp i j w).1) h)) G x i, coastTransit P σ t p l hl (fun i j h=>not_not.mp (mt (fun w=>(hp i j w).2) h)) R y i⟩⟩
lemma bannerOil (Y W : Aura n→ℝ) (M : Bag n) (F : ∀ X,Flight P q X h (M X) (Y X) (W X)) : Bias (Rill.cipherK q) M P h Y := ⟨fun i x=>(F i).tube.body x,fun X=>(F X).tube.price,fun X X' D v _ p=>(F X').tube.offer X v D ‹D⊆X.val› p⟩
open scoped YM.CF.Mew
open Rill Spire Paige
attribute [local instance] loreM loreN
attribute [local instance] Rill.boreKSpace Rill.boreXN
-- earn first force from a Cauchy program: literal smaller account only at D=∅.
lemma birthIncome (Y W : Aura n→ℝ)(M : Bag n)(F : ∀ X,Flight P q X h (M X) (Y X) (W X))
    (p : Bias (cipherK q) M P h Y) (X:Aura n) (u:0≤h)(w:3 ≤ P.B) : Fray P h (cipherK q) X ∅ (Bias.payX p X ∅ X 1) (W X) := by
 have hx: halo (cipherK q) (∅:Support (More n)) ⊆ X.val:= by simp [Lattice.halo]
 let φ:= p.scope X X ∅ le_rfl (empty_subset _) hx; obtain ⟨A,qA,f⟩:=(F X).forms
 let R:= qA.offer X le_rfl ∅ (empty_subset _) hx; let V:= R.toCrate.motion 1
 have e: Fray P h (cipherK q) X ∅ 1 1:=⟨Medal.oneT,fun i w=> by simp [Lattice.halo]⟩
 have H : Fray P h (cipherK q) X ∅ V (W X):=by
    let t:= Marque.book R e w le_rfl u qA.price; simpa only [mul_one] using t
 have he : (Bias.payX p X ∅ X (1:Copy n)) = V := by
    funext i; apply Subtype.ext; rw [p.truth X ∅ X 1 ⟨le_rfl,empty_subset _,hx⟩]; change Sault.rind (coll_T _ X ∅ (M X) i*1)= Sault.rind (coll_T _ X ∅ A i*1)
    rw [mul_one,mul_one]; unfold coll_T; split
    next p=> let W:=gloss P X ∅ i; have hp:W.1∈σX P X ∅:= ((Rue.pillar X.val (Rue.open_l P.threshold X.val (∅:Support (More n)))).choose_spec.2 i.1).2 p; exact f X le_rfl W hp
    rfl
 rw [he]; exact H
lemma programTurf (Y W : Aura n→ℝ)(M : Bag n)(α : ∀ X,Flight P q X h (M X) (Y X) (W X))
    (p : Bias (cipherK q) M P h Y) (F:ForceBudget n)(u:ℕ) :
    Bake.Turf (fun X=> layerN (settleK F) p.payX u X ∅):=by
 intro X V U; unfold layerN; simp only [Finset.sum_apply]
 apply sum_congr rfl; intro i _
 exact clean_p _ Y V p (fun X _ t _=> (α X).tube.clean _ t _) U (fun X=>by rw [settle0]; rfl) X i

-- clock inequality at small margin, both allocations distinct. like Cadre.stallK.
-- slack requirement light $s*γ ≤ δ$. Shelf cost cap matches span proof at scale P.B.
namespace Ledger
variable (C:Occlus P)
local notation "η"=>C.η
local notation "Ξ"=> C.uΓ
local notation "Θ"=> C.w
local notation "Λ"=> Sour.spanV P.B
variable {Y W : Aura n→ℝ}
include C
lemma income (V:C.γ*Sour.spanV P.B ≤ C.η)(X:Aura n) (v:0≤Y) :
    Cadre.fog (Cadre.loom_v C.uΓ C.w (widthK n P.B) 0) Y C.γ X ≤ Y X*tact (C.uΓ+C.η) P.B X := by
 unfold Cadre.fog waveL Cadre.loom_v tact; rw [mul_zero, sub_zero, mul_assoc,←Real.exp_add]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (v X)
 let x := (widthK n P.B X)
 have hx:=mul_le_mul_of_nonneg_right (vigor n P.B|>.rate X) C.hγ.le
 have hy:=mul_le_mul_of_nonneg_right V (show 0≤ x from Nat.cast_nonneg _); change _ ≤ _; unfold x at hy; linarith only [hx,hy]
lemma fromDelay (Q : Vow.blazeK n) (V:0≤Y)(G:0≤W)(H:∀ X:Aura n,∀ D ⊆ X.val,0≤Q X D) (K:C.γ*Sour.spanV P.B≤C.η)
    (T:∀ x:Seat n,Cadre.nook (Y*tact (C.uΓ+C.η+C.η) P.B) x ≤ C.c ∧ Cadre.nook (W*tact (C.uΓ+C.η+C.η) P.B) x ≤ C.e)
    (D:Sour.spanV P.B * C.η⁻¹*C.c ≤ C.d)
    (M:C.κ=1) (w:Sour.spanV P.B * C.c ≤ C.w)(hv:0 ≤ C.c)
    (b:C.e+C.d*C.γ - (C.w-Sour.spanV P.B*C.c)*C.γ < 0)
    (J:∀ i:Seat n,Cadre.nook ((roofL Q C.κ)*Cadre.loom_v C.uΓ C.w (widthK n P.B) 0) i < C.γ) :
    Timer (uChip Y W Q) Y C.κ C.uΓ C.w (Sour.widthK n P.B) (Sour.spanV P.B) C.γ C.c C.d C.e 1 W := by
 let x:=tact (n:=n) (Ξ+η+η) P.B
 have ht : 0 ≤ Λ:= Nat.cast_nonneg _
 apply Cadre.uGears Y W Q V G H C.κ Ξ Θ Λ C.c C.d C.e C.γ _ (vigor n P.B)
 · exact fun i=> (sum_le_sum (g:=fun j:Aura n=> (Y*x) j) (fun j _=> (income C K j V).trans (mul_le_mul_of_nonneg_left (tact_para (le_add_of_nonneg_right C.hη.le) j) (V j)))).trans (T i).1
 · intro i; apply le_trans _ ((mul_le_mul_of_nonneg_left (T i).1 (show 0 ≤ Λ * η⁻¹ from mul_nonneg ht (inv_nonneg.mpr C.hη.le))).trans D); unfold shelfR nook; rw [mul_sum]; apply sum_le_sum; intro j _; apply (mul_le_mul_of_nonneg_right (income C K j V) (Nat.cast_nonneg _)).trans; have hv:=mul_le_mul_of_nonneg_left (shelf_pay (k:=P.B) (s:=Ξ+η) C.hη j) (V j); change Y j*_* _ ≤ _*(Y j*_); linarith only [hv] -- may require ring data first
 · exact fun i=>(sum_le_sum (g:=fun j:Aura n=> (W*x) j) (fun j _=> mul_le_mul_of_nonneg_left (show Cadre.loom_v _ _ _ _ _ ≤x j from by rw [Cadre.loom_v,mul_zero,sub_zero]; exact tact_para (le_trans (le_add_of_nonneg_right C.hη.le) (le_add_of_nonneg_right C.hη.le)) _) (G j))).trans (T i).2
 all_goals first| exact J | exact w | exact b | exact ht | exact C.hγ.le | exact hv | exact (mul_nonneg ht hv).trans w | rw [mul_one]; linarith only [P.exponent_pos, C.hw, C.hη] | rw [M]
end Ledger
end YM.CF.Sour
#print axioms YM.CF.Sour.programTurf
#print axioms YM.CF.Sour.Ledger.fromDelay
#print axioms YM.CF.Sour.birthIncome
#print axioms YM.CF.Sour.tapeBuy
