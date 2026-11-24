import SatinFixedContrastNovember4

import SatinThinSymphony

/-! # CP12 Bilateral: crossing plus and minus at separated real positions. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid Aria Casting Six OS.Semigroup.Balloon
open MacroGrid
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "E"=> P.Ellis 3 x
local notation "ξ"=> P.advocate 3 x j
local notation "H"=> P.ManyF j ξ
local notation "N"=> ([false,true]:List Bool)
local notation "Χ"=> P.commonWell 3 x
local notation "G"=> P.physicalEnergy j ξ
local notation "S"=> P.seasons j ξ
local notation "Γ"=> P.cartage j ξ
local notation "U"=> (S).E
local notation "κ"=> P.wealth j ξ
-- build K for both axes. Either sequence (also rank-alone sector article). phase labels
variable (J:P.Ellis 3 x)
local notation "K" C:max D:max x:max y:max=> Χ (usher C D) (usher x y) N
local notation "w" A:max=> Apron.realWidth P A j
private lemma glare_kiss (A:P.Apron): glareY x A j=flashY x (A.kiss P j) j:=by
 unfold glareY flashY; rw [P.lives_twin,P.tableMaps,show mirrorΩ j (0:Vantage)=0 from (by funext i; by_cases h:i=j<;> simp [mirrorΩ,h]), P.cart_zero]; rfl
include J
-- ordinary gap estimate directly on commonWell. free of width-accumulation cost
lemma bilateral_plus (A B:P.Apron)(p q:Vantage)(h:w A<(q-p) j/2)(v:w B<(q-p) j/2): K A B p q=inner ℂ (P.beam j x (A.kiss P j) ((q-p) j/2)) (Γ (q-p) (P.beam j x B ((q-p) j/2))):=by
 let F:= usher A B; let a:=usher (0:Vantage) (q-p); let y:= (q-p) j; let t₀:= w A; let t₁:= w B
 have hz: w A+w B < y:=by linarith only [h,v]
 have he: usher p q= settler a p:=by funext i; cases i; exact (add_zero _).symm; exact (show q=p+(q-p) by abel)
 rw [he,(P.common_shift 3 x F a N J ⟨j,N,List.Perm.refl _, List.pairwise_pair.mpr (show 0+(w A) < y-w B from by linarith only [hz])⟩ p).2] -- tune
 have hu:(y-(t₀+t₁)).toNNReal= (y/2-t₀).toNNReal+(y/2-t₁).toNNReal:=by ext; rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hz.le), Real.coe_toNNReal _ (sub_nonneg.mpr h.le), Real.coe_toNNReal _ (sub_nonneg.mpr v.le)]; ring
 rw [avail_cross x A B j (q-p) J hz,P.glare_kiss]; unfold beam; rw [Apron.kiss_width,(S).swing]; change inner ℂ _ (U ((y-(t₀+t₁)).toNNReal) (Γ (q-p) (flashY x B j)))=inner ℂ _ _; rw [P.warm_drive j ξ (q-p) ((y-(t₀+t₁)).toNNReal), hu]; nth_rw 1 [(S).time]; rw [P.warm_drive]; rfl -- second occurrence maybe rewrites first?
lemma bilateral_minus (A B:P.Apron)(p q:Vantage)(h:w B<(p-q) j/2)(v:w A <(p-q) j/2): K A B p q=K B A q p:=by
 let F:=usher A B; let Q:=usher B A; let P':= usher p q; let R:=usher q p; let d:=([true,false]:List Bool)
 have hx:q j+(w B)<p j-w A:=by simp_rw [Pi.sub_apply] at v h; linarith only [h,v]
 rw [P.common_cult 3 x F _ N J (show List.Perm N d from List.Perm.swap ..) (show P.Turnstile j F d P' from List.pairwise_pair.mpr hx), P.common_cult 3 x Q _ N J (List.Perm.refl _) (show P.Turnstile j Q N R from List.pairwise_pair.mpr hx)]; rfl
-- sequentially locally uniform
variable {C D:ℕ→ P.Apron} {Y Z:∀ j:Axis,List Axis → ℝ→ P.ColorHil j (P.advocate 3 x j)}
    (T:Radiates P x C Y)(T':Radiates P x D Z)
local notation "r" W:max L:max v:max => (κ) (W j L v)
def railKernel (Y Z:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(l k:List Axis)(p:Vantage): ℂ:= inner ℂ (κ (Y j (j::l) (p j/2))) (Γ p (κ (Z j k (p j/2))))
omit J
include T
lemma kinetic (l:List Axis)(t:ℝ)(p:0<t): κ (Y j (j::j::l) t)=κ (Y j l t):=by
 have he:= T.port j l p (u:=fun _=>t) tendsto_const_nhds; refine tendsto_nhds_unique (T.port j (j::j::l) p (u:=fun _=>t) tendsto_const_nhds) (he.congr fun i=>?_)
 rw [Apron.pivot_cons,Apron.pivot_cons,beam,beam,Apron.kiss_width,Apron.kiss_width,← P.glare_kiss,flashY_glare] -- glare_kiss has include J? no
include T' J
local notation "C'" i:max l:max=> (C i).pivot P l
local notation "D'" i:max k:max=> (D i).pivot P k
lemma scenic_right {p q:ℕ→ Vantage}{u v:Vantage}(l k:List Axis)(p₀:Tendsto p atTop (𝓝 u))(q₀:Tendsto q atTop (𝓝 v))(h:0<(v-u) j): Tendsto (fun i=> K (C' i l) (D' i k) (p i) (q i)) atTop (𝓝 (P.railKernel x j Y Z l k (v-u))):=by
 let y:=v-u; let d(n):=q n-p n; let f(i):=d i j/2; have hp:0<y j/2:=half_pos h; have hv:Tendsto d atTop (𝓝 y):=q₀.sub p₀; have hg:Tendsto f atTop (𝓝 (y j/2)):= ((continuous_apply j).continuousAt.tendsto.comp hv).div_const _
 have KZ:Tendsto (fun i=> Γ (d i) (P.beam j x (D' i k) (f i))) atTop (𝓝 (Γ y (κ (Z j k (y j/2))))) := firmly (Γ ∘ d) zero_le_one (Eventually.of_forall fun i=> P.cart_pay j ξ _) ((P.cart_cont ..|>.tendsto y).comp hv) (T'.port j k hp hg)
 let F₁:=fun i=>P.beam j x ((C i).pivot P (j::l)) (f i); let F₂:=fun i=> Γ (d i) (P.beam j x ((D i).pivot P k) (f i)); have hj:Tendsto (fun i=>inner ℂ (F₁ i) (F₂ i)) atTop (𝓝 (inner ℂ (κ (Y j (j::l) (y j/2))) (Γ y (κ (Z j k (y j/2)))))):= (T.port j (j::l) hp hg).inner KZ; change Tendsto _ _ (𝓝 (inner ℂ (κ (Y j (j::l) (y j/2))) (Γ y (κ (Z j k (y j/2)))))); apply hj.congr'
 filter_upwards [ (T.kiss j l).eventually_lt hg hp,(T'.kiss j k).eventually_lt hg hp] with i hp hw -- name
 change inner ℂ (F₁ i) (F₂ i)=_; unfold F₁; rw [Apron.pivot_cons P (C i) j l]; exact Eq.symm (P.bilateral_plus x j J (C' i l) (D' i k) (p i) (q i) hp hw)
lemma scenic_left {p q:ℕ→ Vantage}{u v:Vantage}(l k:List Axis)(p₀:Tendsto p atTop (𝓝 u))(q₀:Tendsto q atTop (𝓝 v))(h:0<(u-v) j): Tendsto (fun i=> K (C' i l) (D' i k) (p i) (q i)) atTop (𝓝 (P.railKernel x j Z Y k l (u-v))):=by
 let y:=u-v; let d(n):=p n-q n; let f(i):=d i j/2; have hp:0<y j/2:=half_pos h; have hv:Tendsto d atTop (𝓝 y):=p₀.sub q₀; have hg:Tendsto f atTop (𝓝 (y j/2)):= ((continuous_apply j).continuousAt.tendsto.comp hv).div_const _
 refine (P.scenic_right x j J T' T k l q₀ p₀ h).congr' ?_; filter_upwards [(T.kiss j l).eventually_lt hg hp,(T'.kiss j k).eventually_lt hg hp] with i u v; exact (P.bilateral_minus x j J _ _ (p i) (q i) v u).symm
lemma scenic_eq (u:Axis)(l k:List Axis)(y:Vantage)(p:0<y j)(q:0<y u): P.railKernel x j Y Z l k y=P.railKernel x u Y Z l k y:=by
 have g(c:Axis)(e:0<y c): Tendsto (fun i=>K (C' i l) (D' i k) (0:Vantage) y) atTop (𝓝 (P.railKernel x c Y Z l k y)):=by
    let d₀:ℕ→ Vantage:= Function.const _ 0; let d₁:= Function.const ℕ y; have t:= P.scenic_right x c J T T' l k (u:=(0:Vantage)) (p:=d₀) (q:=d₁) tendsto_const_nhds tendsto_const_nhds (show 0<(y-0) c from by simp only [sub_zero,e]); rw [sub_zero] at t; exact t
 exact tendsto_nhds_unique (g j p) (g u q)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.scenic_right
