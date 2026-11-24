import YM.SU5.Reconstruction.Sleet.Yak
import YM.SU5.Reconstruction.Chambers.AllHorizons
/-! # Sending a calibration shutter across huge complex width. In use at this character. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5200
set_option synthInstance.maxSize 33000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers LightBudget Storm
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
local notation "W" => placement Λ
local notation "L" j:max=> lowland j 0
local notation "N" j:max=> flank j 0
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "wk" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (wk i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (wk i)
local notation "U₀" i:max=> mainsea Y H V G.history G.clipped i false (C i) (wk i)
local notation "A₀" i:max=> ride Y H V G.history G.clipped i false (C i) (wk i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (wk i)
local notation "Os" i:max=> OSvector Y H V G i (C i) (wk i)
local notation "θ" i:max=> flipMark i (tent Y H)
local notation "ℜ" t:max=> Real.toNNReal (t:ℝ)
variable (j b:Axis)(p:b≠j)
variable {x y: Sky (tent Y H)}{U R:Set RSpace}

def allLift (U R:Set RSpace)(δ:ℝ): Prop:= ∀ i:Axis,∀ x∈U,∀ y∈R,x i + δ ≤ y i
local notation "Pm" => terrainK j b
variable {δ:ℝ}(k_pp:allLift U R δ)
include k_pp p
lemma lessSnow (s:Shard Gt)(e:thermal s<δ)(t:Gt)(v:|(t:ℝ)|≤ thermal s): allLift U (slides (coordinates Λ (terrainK j b t (-t))) R) (δ-thermal s):=by
 intro i a z q y; obtain ⟨c,g,rfl⟩:=y; change a i+_ ≤ c i+((Pm t (-t) i):ℝ); have hp:= k_pp i a z c g; obtain ⟨he,hu⟩:= abs_le.mp v; by_cases h:i=j; subst i; rw [terrain_time p]; linarith
 by_cases hg:i=b; subst i; rw [terrain_space,AddSubgroup.coe_neg]; linarith
 rw [terrain_other _ _ i _ _ h hg]; rw [AddSubgroup.coe_zero]; linarith [thermal_pos s]
omit p k_pp in
lemma atAngles (v:Shard Gt)(h:allLift U R (thermal v)): Disjoint U R := Set.disjoint_left.mpr fun x p q=> by linarith [thermal_pos v,h 0 x p x q]
include V in
lemma fronts {q:Bool}(s:Shard Gt)(e:thermal s<δ)(t:Gt)(v:|(t:ℝ)|≤ thermal s)(a:x∈Domain Y H G q U)(h:y∈Domain Y H G q R):ridgeLine Y H j b x y t (-t)∈Domain Y H G q (U∪ slides (coordinates Λ (Pm t (-t))) R):= domain_mult Y H G a (moving Y H V G _ y h) (Set.disjoint_left.mpr fun u i l=> by linarith [lessSnow j b p k_pp s e t v j u i u l])

variable (hU:IsCompact U)(hR:IsCompact R)
local notation "G'"=> Schedule.choose_grip
include hU hR
private lemma biLayout (s:Shard Gt) (e:thermal s<δ):
    ∃ t q:Gt, (∀ x∈U,x j+(t:ℝ)≤ 0 ∧ x b+(q:ℝ)≤0) ∧ ∀ y∈R, 0≤ y j+((↑(t-s.val)):ℝ) ∧ 0≤ y b+((↑(q-s.val)):ℝ):=by
 let f:placement Λ:=terrainK j b (-s.val) (-s.val)
 let R':=slides (coordinates Λ f) R; have u: IsCompact R':=hR.image (show Continuous _ from (continuous_id.add continuous_const))
 have hf(i:Axis)(g:(f i:ℝ)=-thermal s): ∃ t:↥Gt,(∀ y∈U,y i+(t:ℝ) ≤0) ∧ ∀ v∈R,0≤ v i+((↑(t-s.val)):ℝ):=by
    obtain ⟨a,c,w,l,_,h,_,B,C⟩:= Schedule.choose_grip (daylight (timeMesh Λ)) i hU u (by rintro y e' _ ⟨z,p,rfl⟩; change _< z i+ (f i:ℝ); linarith [k_pp i y e' z p]); refine ⟨-c, ?_,?_⟩
    · intro y Hy;rw [AddSubgroup.coe_neg]; linarith [(B y Hy).2]
    intro v p; rw [AddSubgroup.coe_sub,AddSubgroup.coe_neg]; have he:= (C _ (show v+coordinates Λ f ∈ R' from Set.mem_image_of_mem _ p)).1
    change (w:ℝ) < v i + (f i:ℝ) at he
    linarith [show thermal s = ↑s.val from rfl]
 obtain ⟨t,h,j'⟩:=hf j (by unfold f; rw [terrain_time p]; rfl); obtain ⟨v,k_pp,u⟩:=hf b (by unfold f; rw [terrain_space]; rfl); exact ⟨t,v,fun x p=>⟨h _ p,k_pp _ p⟩,fun x p=>⟨j' _ p,u _ p⟩⟩
omit k_pp hU hR in
private lemma terrain_home : terrainK j b (0:marks (timeMesh Λ)) 0= (0:placement Λ):=by
 funext z; by_cases h:z=j; · subst z; simp [p]
 by_cases h':z=b; subst z; rw [terrain_space]; rfl
 exact terrain_other _ _ z _ _ h h'
omit k_pp hU hR in
lemma centre_zero :ridgeLine Y H j b x y (0:marks (timeMesh Λ)) 0=x*y:=by rw [ridgeLine,terrain_home j b p,move_by_zero]

-- Cost at THIS physical pair, not general labels or shortened poses now.
structure Soaring (j b:Axis)(x y:Sky (tent Y H))(r:Shard (marks (timeMesh Λ)))(f:ℂ→ℂ):Prop where
   analytic: AnalyticOnNhd ℂ f (Metric.ball 0 (thermal r))
   horizon : ∃ C':ℝ,∀ z∈Metric.ball 0 (thermal r),‖f z‖≤ C'
   honours: ∀ t:marks (timeMesh Λ), |(t:ℝ)|< thermal r→ f (↑(t:ℝ))=whiff Y H V G C a χ (ridgeLine Y H j b x y t (-t))
omit k_pp hU hR in
lemma Soaring.origin {r:Shard Gt}{f:ℂ→ℂ}(u:Soaring Y H V G C a χ j b x y r f): f 0=whiff Y H V G C a χ (x*y):=by
 have ht:= u.honours 0 (by simpa using thermal_pos r); rw [neg_zero,centre_zero Y H j b p,AddSubgroup.coe_zero,Complex.ofReal_zero] at ht; exact ht
lemma full_power (s:Shard Gt)(e:thermal s<δ)(h:x∈ D U)(g:y∈ D R):∃ f:ℂ→ℂ, Soaring Y H V G C a χ j b x y s f:=by
 obtain ⟨t,q,Hx,Hy⟩:= biLayout j b p k_pp hU hR s e
 let a':=terrainK j b t q; let b':=terrainK j b (t-s.val) (q-s.val); let f':=move K a' x; let Y':=move K b' y
 have hz : Thermal Y H G j f' Y':= ⟨lowering Y H V G j h a' (fun i p'=> by unfold a'; rw [terrain_time p]; exact (Hx i p').1), heightening Y H V G j g b' (fun i p'=>by unfold b'; rw [terrain_time p]; exact (Hy i p').1)⟩
 have hg : Thermal Y H G b f' Y':= ⟨lowering Y H V G b h a' (fun i p'=> by unfold a'; rw [terrain_space]; exact (Hx i p').2), heightening Y H V G b g b' (fun i p'=>by unfold b'; rw [terrain_space]; exact (Hy i p').2)⟩
 obtain ⟨f,B,q',r⟩:= snow_circle Y H V G C a χ j b p hz hg s
 refine ⟨f,B,⟨_,q'⟩,fun i w=>?_⟩
 rw [r i w,← whiff_move Y H V G C a χ (domain_mono Y H G (subset_univ _) (fronts Y H V G j b p k_pp s e i w.le h g)) a']; unfold ridgeLine
 change whiff Y H V G C a χ ((move K a' x)*move K _ (move K b' y))=_; rw [move_prod,move_sum,move_sum]
 unfold b' a'; rw [terrain_sum p,terrain_sum p, show (s.val+i)+(t-s.val)=t+i from by abel, show s.val-i+(q-s.val)= q+ -i from by abel]
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Stormwatch
