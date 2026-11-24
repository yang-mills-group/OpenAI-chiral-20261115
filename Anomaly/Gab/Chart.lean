import Anomaly.Hop.Pages
import YM.CF.Brood.Harp
/-! Uniform shape interpretation in the engineering color spawn. We expose concrete
 projection matrices for caps. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function Module NormedSpace Filter Metric Finset
open Moto Hove Oath Haro Bake Fock Roots Rive Neon
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I E:Type}[Fintype I][NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E]
local notation "DΩ"=> (Sum I Unit)
abbrev ρZee {I:Type}[Fintype I]{E:Type}[NormedAddCommGroup E][NormedSpace ℂ E](B: Basis I ℂ E): Basis (Sum I Unit) ℂ (E × ℂ):= B.prod (Basis.singleton Unit ℂ)
lemma zee₀ (B: Basis I ℂ E)(i:I):ρZee B (Sum.inl i)=(B i,0):=by simp only [ρZee,Basis.prod_apply]; rfl
lemma zee₁ (B: Basis I ℂ E)(i:Unit):ρZee B (Sum.inr i)=(0,1):=by simp [ρZee,Basis.prod_apply]
def Reap (S:Submodule ℂ E): E→ₗ[ℂ] S:= (LinearMap.exists_leftInverse_of_injective S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose
lemma reaps (S:Submodule ℂ E)(V:S): Reap S V.val=V:= DFunLike.congr_fun (LinearMap.exists_leftInverse_of_injective S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose_spec V -- tune map
lemma ripe (S:Submodule ℂ E)(x:E)(t:x∈S): Reap S x= ⟨x,t⟩:=reaps S ⟨x,t⟩
def dreamℂ(h:ℝ):ArcΦ→ₗ[ℂ] BadgeΦ:= ( ((h:ℂ)^2 • Reap mind_B).comp ((LinearMap.fst ..).comp (LinearMap.snd ..))).prod (((Reap mind_A).comp (LinearMap.fst ..)).prod (((h:ℂ)^2 • Reap mind_C).comp ((LinearMap.snd ..).comp (LinearMap.snd ..))))
def ρDream(h:ℝ): ArcΦ→ₗ[ℂ] ↑mind_B:= (LinearMap.fst ..).comp (dreamℂ h)
lemma sluice (h q:ℝ)(x:ArcΦ)(p:InΦ x):(q:ℂ)⁻¹ • dreamℂ h x=recolor x h q p:=by
 refine Prod.ext ?_ (Prod.ext ?_ ?_)
 · change (q:ℂ)⁻¹ • ((h:ℂ)^2 • Reap mind_B x.2.1)=_; rw [ripe _ _ p.2.1,smul_smul]; rfl
 · change (q:ℂ)⁻¹ • Reap mind_A x.1=_; rw [ripe _ _ p.1]; rfl
 change (q:ℂ)⁻¹ • ((h:ℂ)^2 • Reap mind_C x.2.2)=_; rw [ripe _ _ p.2.2,smul_smul]; rfl
lemma ripeTune (h:ℝ)(p:h>0)(B:BadgeΦ)(Q:ℝ) : dreamℂ h (tune_Φ Q h B)=(Q:ℂ) • B:=by
 let R:= (↑(Q/h^2):ℂ); have hz:((h:ℂ)^2)*R=(Q:ℂ):=by unfold R; push_cast; have hp:(h:ℂ) ≠ 0:= Complex.ofReal_ne_zero.mpr p.ne'; field_simp
 refine Prod.ext ?_ (Prod.ext ?_ ?_)
 · change (h:ℂ)^2 • Reap mind_B (R • B.1.val)=_; rw [map_smul,reaps,smul_smul,hz]; rfl
 · change Reap mind_A ((Q:ℂ) • B.2.1.val)=_; rw [map_smul,reaps]; rfl
 change (h:ℂ)^2 • Reap mind_C (R • B.2.2.val)=_; rw [map_smul,reaps,smul_smul,hz]; rfl
lemma bite_Φ (h:ℝ)(p:h>0) (X Y:ArcΦ)(u:InΦ X)(v:InΦ Y)(k:dreamℂ h X=dreamℂ h Y): X=Y:=by
 have ht: recolor X h 1 u= recolor Y h 1 v:=by rw [←sluice,←sluice,k]; -- available.
 rw [← release_h Y h 1 p zero_lt_one v,←ht,release_h _ _ _ p zero_lt_one]
lemma tote_Φ (h:ℝ)(p:0<h)(X Y:ArcΦ)(u:InΦ X)(v:InΦ Y)(k:ρDream h X=ρDream h Y): X.2.1=Y.2.1:=by
 let D:= tune_Φ 1 h; have hz(B C:BadgeΦ)(p:B.1=C.1):(D B).2.1=(D C).2.1:=by change (↑((1:ℝ)/h^2):ℂ) • B.1.val=(↑((1:ℝ)/h^2):ℂ) • C.1.val; rw [p]
 have hp: (recolor X h 1 u).1= (recolor Y h 1 v).1:=by rw [←sluice,←sluice]; change (↑(1:ℝ):ℂ)⁻¹ • ρDream h X=(↑(1:ℝ):ℂ)⁻¹ • ρDream h Y; rw [k]
 have ht:=hz _ _ hp; unfold D at ht; rwa [release_h _ _ _ p zero_lt_one,release_h _ _ _ p zero_lt_one] at ht
lemma ηDay(h:ℝ)(p:0<h)(X:ArcΦ)(k:InΦ X)(a b f x:ℝ)(ha:‖X.1‖≤a)(hφ:‖X.2‖*h^2≤b*f)(v:a ≤ x)(u:b*f≤x) : ‖dreamℂ h X‖ ≤ x:=by
 let Z:=dreamℂ h X; have he:Z= recolor X h 1 k:= Eq.trans (by unfold Z; rw [show (↑(1:ℝ):ℂ)=(1:ℂ) from by norm_num,inv_one,one_smul]) (sluice ..)
 obtain ⟨t,z,h⟩:=norms_t (recolor X h 1 k) 1 h zero_lt_one p; rw [release_h _ _ _ p zero_lt_one,one_mul] at t z h
 rw [show dreamℂ _ _=_ from he,Prod.norm_def]; refine max_le ?_ ?_; · rw [←t]; exact ((mul_le_mul_of_nonneg_right (norm_fst_le _) (sq_nonneg _)).trans hφ).trans u
 rw [Prod.norm_def,←z,←h]; exact max_le (ha.trans v) (((mul_le_mul_of_nonneg_right (norm_snd_le _) (sq_nonneg _)).trans hφ).trans u)
-- one cap; use with $B3$ or norm $B4$.
structure SketchA (B: Basis I ℂ E)(m:ℕ) where
  space : ℝ→ ArcΦ→ₗ[ℂ] E
  color : I→ Ξθ
  grades(i:I): let a:=color i; a.isLeft ∨ m ≥ 4
  age :3 ≤ m
  yoga : ∀ h q:ℝ, h>0 →∀ i,space h (cue_Φ q h (color i))=(q:ℂ) • B i
  pace : ∀ h x,‖space h x‖≤ ‖dreamℂ h x‖
def ιBuild4 :SketchA Gior 4 where
 space:= dreamℂ
 color:=id
 grades _:=Or.inr le_rfl
 age:=by decide
 yoga h q u i:= ripeTune h u (Gior i) q
 pace _ _:=le_rfl
def ιBuild3 : SketchA Bθ 3 where
 space:=ρDream
 color:=Sum.inl
 grades _:= Or.inl rfl
 age:=le_rfl
 yoga h q u i:=by change (dreamℂ h (tune_Φ q h (Gior _))).1=_; rw [ripeTune h u,Bθ_i]; rfl
 pace _ _:= norm_fst_le _
end YM.CF.Py
