import YM.SU5.Reconstruction.Anvil.Haven
import YM.SU5.Reconstruction.Seams.BoundSpeed
import YM.SU5.Reconstruction.Anvil.Council
import YM.SU5.Reconstruction.Anvil.Concert
import YM.SU5.Reconstruction.Anvil.Post
import YM.SU5.Reconstruction.Trap.Castle
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open Anvil
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
variable (j:Axis) (Δ:Finset Axis) (p:j∉Δ) (F:BoostBacking Y H V G C a χ)
def taxableLens (d e f g:↥Δ→ marks (timeMesh Λ)) (v:↥Δ→ Bool) : Terrain j Δ := { P:=fun i=>horizonPrice (0:Gt) (d i) (e i) (f i) (g i), first:=v,enough:=fun i hi=> p (hi ▸ i.property)} -- p participates? include
-- weak anchors for this theorem
structure Slip (x : ℕ→Sky (tent Y H)) (h:ℕ→marks (timeMesh Λ)) (T:ℕ→ (indoor Y H V G.history G.clipped j false (C j) (w j)).Op) (A:(fort Y H V G.history G.clipped j false (C j) (w j)).Op) : Prop where
  stays (n:ℕ) : Follows Y H V G j (C j) (w j) (x n) (h n) (T n)
  phase (n:ℕ) : 0< (h n:ℝ)
  short : Tendsto (fun n=>(h n:ℝ)) atTop (𝓝 0)
  propitious : Limited atTop (fun n=> opCarries Y H V G j (C j) (w j) (T n)) A
variable {A B:(fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable {X W: ℕ → (indoor Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))).Op}
variable {x y:ℕ→Sky (tent Y H)} {u v:ℕ→marks (timeMesh Λ)}
variable (X₀: Slip Y H V G C a χ j x u X A) (Y₀: Slip Y H V G C a χ j y v W B)
-- all observers in lens must pay their own norm rent, self.
variable (d e f g:↥Δ→ marks (timeMesh Λ)) (q:↥Δ→ Bool) (b:ℝ)(t:Anvil.Meter)(h:t j=0)
variable {X' Y': (k:↥Δ) → ℕ →(indoor Y H V G.history G.clipped k.val false (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val))).Op}
variable (Z:∀ k:↥Δ, Perpendicular Y H V G k.val (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val)) (e k) (d k) x (X' k))
  (Z':∀ k:↥Δ,Perpendicular Y H V G k.val (C k.val) (displacement Y H V G.history G.clipped a false (C a) χ k.val (C k.val)) (g k) (f k) y (Y' k))
local notation "T'"=> taxableLens j Δ p d e f g q
local notation "Q" i:max=>opCarries Y H V G i (C i) (w i)
local notation "Φ"=> sunny (S₀ j) t b
local notation "Dj"=> Domain Y H G false (flank j 0)
-- prepares both in all budgets, Lens extended appropriately.
include X₀ Y₀ p Z Z' h F
set_option maxHeartbeats 900000 in
lemma crevice (r s c:ℝ) (hr:0≤r)(Vu:∀ i, (u i:ℝ)≤r)(Vv:∀ i,(v i:ℝ)≤r) (T:Gt) (Ft:Umbrella j t b (T:ℝ) s r c (T')) (L R: Dj)
   (hp:∀ i:↥Δ,L.val∈ D (lowland i.val (-(T:ℝ))))(hr':∀ i:↥Δ,R.val∈ D (flank i.val (T:ℝ))) :
    let E₀:= (S₀ j).E (ℜ (T:ℝ)); inner ℂ (E₀ ((Vo j) L)) (A (Φ B (E₀ ((Vo j) R)))) = inner ℂ (E₀ ((Vo j) L)) (Φ B (A (E₀ ((Vo j) R)))):=by
  have le (i:↥Δ):i.val≠j:= (T').enough i
  choose U p' using fun (i:↥Δ)=> leftGate Y H V G j i (le i).symm L (-T) T (hp i) -- negative T coercion
  choose Kp q' using fun (i:↥Δ)=> rightGate Y H V G j i (le i).symm R T T (hr' i)
  let S(i:↥Δ):=(S₀ i.val); let N(n:ℕ) (i:↥Δ):= (Q i.val) (X' i n); let M(m:ℕ) (i:↥Δ):= (Q i.val) (Y' i m); -- binder i implicit type tune
  let L' (i:↥Δ):=(Vo i.val) (U i); let R'(i:↥Δ):= (Vo i.val) (Kp i)
  have ht (i i'): (osValue Y H V G i (C i) (w i)) = osValue Y H V G i' (C i') (w i'):= (os_across Y H V G a (C a) χ i (C i)).trans (os_across Y H V G a (C a) χ i' (C i')).symm
  let U'(i:↥Δ):= ((T').P i).extend T
  let YL(n m:ℕ)(i:↥Δ):= (U' i).sale ((T').first i) (S i) (N n i) (M m i) (L' i) (R' i)
  let Q₀(i:↥Δ):=(U' i).permeates i.val ((T').first i)
  have hv (n m:ℕ)(i i':↥Δ)(z:Wage)(h:Q₀ i z)(c:Q₀ i' z): YL n m i z= YL n m i' z := council Y H V G i _ _ (F.present i.val) (F.forward i.val) _ _ _ (F.present i'.val) (F.forward i'.val) (ht _ _) (U i) (Kp i) (U i') (Kp i') T ((p' i).symm.trans (p' i')) ((q' i).symm.trans (q' i')) (d i) (e i) (f i) (g i) (d i') (e i') (f i') (g i') _ _ _ _ ((Z i).beyond n) ((Z' i).beyond m) ((Z i').beyond n) ((Z' i').beyond m) _ _ z h c -- Lean implicit proof
  let Bz(n m:ℕ):= vertical (T:ℝ) (u n:ℝ) (v m:ℝ); let Yz(n m:ℕ)(y:Bool):= (Bz n m).sale y (S₀ j) ((Q j) (X n)) ((Q j) (W m)) ((Vo j) L) ((Vo j) R)
  have hg(n m:ℕ)(i:↥Δ)(w':Bool)(z:Wage)(p:Q₀ i z)(e₀:(Bz n m).permeates j w' z) : YL n m i z = Yz n m w' z := by
     let he₁(n:ℕ)(s:Sky (tent Y H)): move (tent Y H) (eject j (-(0:Gt))) s=s:=by simp
     exact council Y H V G i _ _ (F.present i.val) (F.forward i.val) _ _ _ (F.present j) (F.forward j) (ht _ _) (U i) (Kp i) L R T (p' i).symm (q' i).symm (d i) (e i) (f i) (g i) 0 (u n) 0 (v m) _ _ _ _ ((Z i).beyond n) ((Z' i).beyond m) (by rw [he₁ n]; exact X₀.stays n) (by rw [he₁ m]; exact Y₀.stays m) _ _ z p e₀
  let D' (n m:ℕ):= Ft.overture S (N n) (M m) L' R'
  choose U Ut using fun i:↥Δ=> (Z i).bounded; choose H' H't using fun i:↥Δ=> (Z' i).bounded
  have V'(n i): ‖N n i‖ ≤ U i := Ut i n; have Ev(m i): ‖M m i‖≤ H' i:=H't i m
  intro E₀; refine Ft.pure_time h (S₀ j) ((Vo j) L) ((Vo j) R) X₀.propitious X₀.short Y₀.propitious Y₀.short hr Vu Vv D' (Anvil.Umbrella.limitFare («D»:=fun i:↥Δ=> (G₀ i.val)) L' R' U H') (fun n m=> ?_) (fun w' n m z e=> ?_) (F.forward j)
  · exact ⟨Ft.overture_hol S (N n) (M m) L' R' (hv n m) U H' (V' n) (Ev m), Ft.costs S (N n) (M m) L' R' (hv n m) U H' (V' n) (Ev m)⟩
  have hv':=(Ft.verdict S (N n) (M m) L' R' (hv n m) _ _ _ _ _ (hg n m) (z:ℂ) (Sail.slit_ground _ Ft.costly z) (Vu n) (Vv m)); cases w'; exact hv'.2 (Ioo_subset_Icc_self e); exact hv'.1 (Ioo_subset_Icc_self e)
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
