import YM.SU5.Reconstruction.AllGrades.ReachMarket
import YM.SU5.Reconstruction.AllGrades.Carriages
/-! # Unconditional procurement at the chosen character. Takes leads on even ROOT only, costs on both grades. -/
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical

attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
open Garret NorthTapes
open _root_.YM.Hilbert.Freight
variable (D:Invitation Y H G)
local notation "l₀" b:max s:max t:max F:max => launch Y H G D b s t F
variable (a:Axis)(b:Bool)(s:ℕ)
local notation "S"=>studio (tent Y H) a 0 b
variable (P: Inspector Y H G)
local notation "Ω"=> P.pulse
local notation "Bp" s:max => badge Y H V G D a b s P
local notation "hP" p:max f:max=> homePlane Y H V G D a b _ _ p f
local notation "W"=> poleForm (tent Y H) a 0 b
local notation "C₀"=> chime (tent Y H)
local notation "Θ"=> mirror (tent Y H)
local notation "L"=> Λ.R.L.val
open Heat
local notation "Ct"=> cart Y H a b
noncomputable def walkC (n:ℕ): S →ₗ[ℂ] S:= Ct a (2*(n:ℤ)) (fun _=>by positivity)
local notation "Wq" n:max=> walkC Y H a b n
lemma walk_plus (x:S)(n m:ℕ): (Wq n) ((Wq m) x)= (Wq (n+m)) x:=by
 unfold walkC; rw [cart_sums, cart_eq Y H a b (show (2:ℤ)*n+2*m=2*((n+m:ℕ):ℤ) by push_cast; ring)] -- q infer?
lemma walk_root (x:S): (Wq 0) x=x:=by
 exact ((congrArg (fun A:S →ₗ[ℂ] S=> A x) (cart_eq Y H a b (q:=fun (_:a=a)=>le_refl 0) (e:=show 2*((0:ℕ):ℤ)=0 by norm_num))).trans (cart_zero Y H a b x a)) -- p infer after notation
lemma level_walk {s t:ℕ}(p:s≤ t)(g:S)(n:ℕ): hP p ((Wq n) g)=(Wq (L^(t-s)*n)) (hP p g):=by
 unfold walkC; rw [cart_up,cart_eq Y H a b (show (L:ℤ)^(t-s)*(2*n)=2*((L^(t-s)*n:ℕ):ℤ) by push_cast; ring)]
lemma walk_herm (x y:S)(n:ℕ) : inner ℂ ((Bp s) ((Wq n) x)) ((Bp s) y)=inner ℂ ((Bp s) x) ((Bp s) ((Wq n) y)):= (lectern Y H V G D a b s P x y (n:ℤ) (by positivity)).symm -- binder order
variable (n:ℕ) (x:studio (tent Y H) a 0 b)
local notation "A₀"=> atlasAt Y H V G
local notation "u" r:max=> badge Y H V G D a b s (atlasAt Y H V G) r
lemma walkPaid : ∃ C:ℝ, ∀ t:ℕ,‖u ((Wq t) x)‖ ≤ C:=by
 obtain ⟨T,v,h⟩:= atSouth Y H a b x
 obtain ⟨w,z⟩:= valuation Y H v; change pay x.val w at z
 obtain ⟨q,r⟩:=Tower.sizes T
 let B:= Grip Y H s q*(w*w); refine ⟨B+1,fun t=>?_⟩; let y:S:= (Wq t) x; let i:= (2*(t:ℤ)); let V':=reflectedBox a i (reflectedBox a 0 T)
 have H':CompactArc V' q:= (r.reflBox T a 0).reflBox _ a _; have Z:InTest (tent Y H) true V' b y.val:= axial (tent Y H) a i (axial K a 0 v)
 have hv:pay y.val w:= chime_pay (tent Y H) a i w z
 let m:=(u y); have hm:‖m‖^2 ≤ B:=by
    rw [show ‖m‖^2=‖inner ℂ (u y) (u y)‖ from by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖m‖:ℝ):ℂ)‖^2; simp]
    rw [measures_here]; change ‖E s (W y.val y.val)‖ ≤ _
    let Z₀:= axial K a 0 Z
    have H₁:= InTest.mul (Z₀.mono (Finset.subset_union_left (s₂:=V'))) (Z.mono Finset.subset_union_right)
    rw [Bool.xor_self] at H₁; unfold poleForm; rw [E_scale Y H V s (aux_test H₁),norm_mul,show ‖Reflect.chord b‖=1 from by cases b <;> simp [Reflect.chord],one_mul]
    exact root_budget Y H V s b q Z₀ Z (H'.reflBox V' a 0) H' w w (pay_flips _ hv a 0) hv
 change ‖m‖≤ _; nlinarith

-- ROOT pacing.
lemma root_walk_time : ‖u ((Wq n) x)‖ ≤ ‖u x‖ :=by
 let X(i:ℕ):= u ((Wq i) x)
 obtain ⟨d,v⟩:= walkPaid Y H V G D a b s x
 let T:Set ℝ:= Set.range fun (i:ℕ)=> ‖X i‖
 have hS(x:ℕ): ‖X x‖∈ T:=Set.mem_range_self x
 have p: BddAbove T:= ⟨d, by rintro _ ⟨i,rfl⟩; exact v i⟩
 let B:= sSup T; have he(i):‖X i‖≤ B:=le_csSup p (hS i)
 have hB:0≤ B:=(norm_nonneg _).trans (he n)
 let c:=‖u x‖; have hc:0≤c:=norm_nonneg _
 have h(i:ℕ):‖X i‖^2≤ c*B:=by
    have ht:‖X i‖^2= ‖inner ℂ (X i) (X i)‖:=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖X i‖:ℝ):ℂ)‖^2; simp
    rw [ht, show inner ℂ (X i) (X i)=inner ℂ (u x) (X (i+i)) from (walk_herm Y H V G D a b s A₀ x ((Wq i) x) i).trans (congrArg _ (congrArg (badge ..) (walk_plus Y H a b x i i)))]
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he (i+i)) hc)
 refine (he n).trans ?_
 have ht:B ≤ Real.sqrt (c*B):=csSup_le ⟨_,hS n⟩ (by rintro _ ⟨i,rfl⟩; exact Real.le_sqrt_of_sq_le (h i))
 have h':= Real.sq_sqrt (mul_nonneg hc hB); change B ≤ c; nlinarith [Real.sqrt_nonneg (c*B)]

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.root_walk_time
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.QuantaFields.level_walk
