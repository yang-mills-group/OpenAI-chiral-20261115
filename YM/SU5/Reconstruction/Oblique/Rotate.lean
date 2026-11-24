import YM.SU5.Reconstruction.Oblique.Precard
/-!
# Genuine reconstruction symmetry from angular funding on these field labels
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
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
local notation "D" => Domain Y H G
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
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "Ω" =>whiff Y H V G C a χ
local notation "au"=>move K
-- local geometry on ANY region, compact later. Need BOTH incoming and exporting.
structure Pave (p:Signed) where
 shift : Sky (tent Y H) ≃ₗ[ℂ] Sky (tent Y H)
 shifts (q:Bool)(U:Set RSpace)(x:Sky (tent Y H)): x∈ Domain Y H G q U ↔ shift x ∈ D q (p.act '' U)
 muls(x y:Sky (tent Y H)): shift (x*y) = shift x * shift y
 fuel(x:Sky (tent Y H)) (h:x∈µ) : Ω (shift x)= Ω x
 unit: shift 1=1
 strips (u:placement Λ)(x:Sky (tent Y H)): shift (au u x)=au (p.act u) (shift x)
 mirror(j:Axis)(x:Sky (tent Y H)): shift ((θ j) x)=(θ (p.perm j)) (shift x)
local notation "Pv" => Pave Y H V G C a χ
namespace Pave
variable {p:Signed}(v:Pave Y H V G C a χ p)
local notation "B" => v.shift
lemma pulseAct(q:Bool)(T:Set RSpace)(x:Sky (tent Y H)): (B).symm x∈ D q (p⁻¹.act '' T) ↔ x∈D q T:= by
 rw [v.shifts,LinearEquiv.apply_symm_apply, image_image]; simp only [Signed.act_inv, Set.image_id']
lemma arcMark(f:Sky K)(x:f∈ Domain Y H G false univ): v.shift f∈ Domain Y H G false univ:= domain_mono Y H G (subset_univ _) ((v.shifts _ _ _).1 x)
lemma cancelB(f:Sky K)(x:f∈ Domain Y H G false univ): (B).symm f∈ Domain Y H G false univ:= domain_mono Y H G (subset_univ _) ((pulseAct Y H V G C a χ v false _ _).2 x)
noncomputable def reflected : Pv p⁻¹ := by
 refine ⟨v.shift.symm,fun q U x=>(pulseAct Y H V G C a χ v q U x).symm,?_,?_,?_,?_,?_⟩
 · intro x y; apply v.shift.injective; rw [v.muls]; simp
 · intro x h; rw [← v.fuel _ (cancelB Y H V G C a χ v _ h),LinearEquiv.apply_symm_apply]
 · apply v.shift.injective; rw [v.unit]; simp -- maybe rewrites B 1
 · intro u x; apply v.shift.injective; rw [v.strips,Signed.act_inv]; simp
 intro j x; apply v.shift.injective; rw [v.mirror]; simp
lemma inverse_def : (reflected Y H V G C a χ v).shift=(B).symm:=rfl
variable {q:Signed}(t:Pave Y H V G C a χ q)
-- pay compositions
noncomputable def relay: Pv (q * p) where
 shift:= v.shift.trans t.shift
 shifts g U x:=by rw [v.shifts,t.shifts,image_image, show Signed.act (q*p) (R:=ℝ)= fun v:RSpace=> q.act (p.act v) from funext (Signed.act_mul q p)]; rfl
 muls _ _:=by simp only [LinearEquiv.trans_apply, t.muls,v.muls]
 fuel x h:= by simp only [LinearEquiv.trans_apply]; rw [t.fuel _ (arcMark Y H V G C a χ v _ h),v.fuel _ h]
 unit:=by rw [LinearEquiv.trans_apply,v.unit,t.unit]
 strips u x:=by simp only [LinearEquiv.trans_apply,v.strips,t.strips,Signed.act_mul]
 mirror i x:=by simp only [LinearEquiv.trans_apply,v.mirror,t.mirror,Signed.mul_perm_apply]
end Pave

-- generators use the actual anti reflection of the tower, also now off-axis for PI/2 Eu rotations of their CLOCKS
structure Blush(s:Signed) where
 flip : Sky (tent Y H) →ₗ⋆[ℂ] Sky (tent Y H)
 self : Involutive flip
 shelf (q:Bool)(U:Set RSpace)(x:Sky (tent Y H)) (h:x∈D q U): flip x ∈ D q (s.act '' U)
 raised:s*s=1
 unit: flip 1=1
 product(x y:Sky (tent Y H)): flip (x*y)=flip x*flip y
 sparks (u:placement Λ)(x:Sky (tent Y H)): flip (au u x) = au (s.act u) (flip x)
 turn (i:Axis)(x:Sky (tent Y H)):flip (flipMark i (tent Y H) x)=(θ (s.perm i)) (flip x)
 fuel(x:Sky (tent Y H))(h:x∈µ) : Ω (flip x)=star (Ω x)
local notation "Bp"=> Blush Y H V G C a χ
namespace Blush
variable {p:Signed}(v: Blush Y H V G C a χ p)
lemma alive(q:Bool)(U:Set RSpace)(x:Sky (tent Y H)): x ∈ D q U ↔ v.flip x ∈ D q (p.act '' U):= by
 refine ⟨v.shelf q U x,fun u=>?_⟩; have h:=v.shelf _ _ _ u; rw [v.self,image_image] at h; simpa only [← Signed.act_mul _ _ _,v.raised,Signed.act_one,Set.image_id'] using h
variable {p':Signed}(w: Blush Y H V G C a χ p')
noncomputable def properMem: Pave Y H V G C a χ (p'*p):= by
 let e: Sky (tent Y H) ≃ₗ[ℂ] Sky (tent Y H):=
  { w.flip.comp v.flip with
    invFun:=fun x=> v.flip (w.flip x)
    left_inv:= fun x=>by change v.flip (w.flip (w.flip (v.flip x)))=_; rw [w.self,v.self]
    right_inv:= fun x=> by change w.flip (v.flip (v.flip (w.flip x)))=_; rw [v.self,w.self] }
 refine ⟨e,?_,?_,?_,?_,?_,?_⟩
 · intro q U x; rw [alive Y H V G C a χ v,alive Y H V G C a χ w q (p.act '' U), image_image, show Signed.act (p' *p) (R:=ℝ)=fun i:RSpace=> _ from funext (Signed.act_mul p' p)]; rfl -- alive accidental rw
 · intro x y; change w.flip (v.flip (x*y))=_; rw [v.product,w.product]; rfl
 · intro x h; change Ω (w.flip (v.flip x))=_; rw [w.fuel _ (domain_mono Y H G (subset_univ _) (v.shelf false univ x h)),v.fuel _ h,star_star] -- invalid .. h
 · change w.flip (v.flip 1)=_; rw [v.unit,w.unit]
 · intro u x; change w.flip (v.flip (au u x))=_; rw [v.sparks,w.sparks, Signed.act_mul]; rfl
 intro j x; change w.flip (v.flip ((θ j) x))=_; rw [v.turn,w.turn]; rfl
lemma arrives(x:Sky (tent Y H)) : (properMem Y H V G C a χ v w).shift x=w.flip (v.flip x):=rfl
end Blush
lemma map_returns {p:Axis}{R:Type*}[AddGroup R](x:Four R): (Signed.mirror p).act x= reverseOne p x:=by funext i; by_cases e:i=p <;> simp [Signed.mirror, Signed.act, reverseOne,e,Ne.symm] -- tune
lemma wind_pin (j:Axis): mirrorE j 0=(Signed.mirror j).act:=by funext x i; by_cases e:i=j<;>simp [mirrorE,map_returns,e,reverseOne]
noncomputable def plain (j:Axis): Bp (Signed.mirror j) where
 flip:= flipMark j K
 self:= mirror_twice j
 shelf _ _ x h:= (wind_pin j) ▸ mirror_support Y H G j x h
 raised:= (show (Signed.mirror j)⁻¹ * Signed.mirror j=1 from inv_mul_cancel _) -- tune inv def
 unit:= flipMark_unit ..
 product:= flipMark_mul j
 sparks u x:= (map_returns u).symm ▸ flipped_moves Y H j u x
 turn i x:= mirror_commuting Y H j i x -- tune orientation sym
 fuel x h:= by
    let g: (θ j) x∈µ:= domain_mono Y H G (subset_univ _) (mirror_support Y H G j x h); rw [funds_stamp Y H V G C a χ g, funds_stamp Y H V G C a χ h]; exact reflected_read Y H V G j a (C a) χ h g
-- functor support preserving for any purchased tilted directly
variable (P:Ramp)
noncomputable def tipped (e:RPos Y H V G P C a χ):Blush Y H V G C a χ P.s:=
 ⟨gust P K, gust_square P,fun _ _ _ h=> shelters Y H V G P h,P.swing,gust_unit ..,gust_mul P,zone_gust Y H P,gust_mirror P,fun _ h=> frees Y H V G P C a χ e h⟩
noncomputable def SpinOn (e:RPos Y H V G P C a χ): Pv (P.s*Signed.mirror P.a) := Blush.properMem Y H V G C a χ (plain Y H V G C a χ P.a) (tipped Y H V G C a χ P e) -- order
variable (e:RPos Y H V G P C a χ)
lemma SpinsOn(x:Sky (tent Y H)): (SpinOn Y H V G C a χ P e).shift x = gust P (tent Y H) (flipMark P.a K x):= rfl
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.WindRose
