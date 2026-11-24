import YM.SU5.FiniteGaugeData.KernelP.Harbor
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
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
-- extensions.common.Template.Reuse Scaler build argument on Harbor
local notation "ℋ" => Harbor Y h W' R Φ a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> H.leaf i
variable (F:ℕ→ Decko Y h a →ₗ[ℂ] Decko Y h a)(B:ℝ)
structure Codec : Prop where
  tall(n:ℕ)(t:s ≤ n)(x:Decko Y h a) : F (n+1) (nectar Y h n W' R a x) = nectar Y h n W' R a (F n x)
  fit(n:ℕ)(t:s ≤ n)(x:Decko Y h a): ‖(H.leaf n) (F n x)‖ ≤ B*‖H.leaf n x‖
local notation "Λ0"=> Codec Y h s W' R a H F B
private abbrev dressing (n:ℕ) := (H.leaf n).comp ((F n).comp (days Y h n W' R a))
local notation "δ" n:max => dressing Y h W' R a H F n
variable (P':Codec Y h s W' R a H F B)
include P'
lemma view (p:s ≤ i)(t:i ≤ k)(c:Arrive Y h w.val i) : (δ k) w=(δ i) w:=by
 induction k,t using Nat.le_induction with
 | base=> rfl
 | succ k t ih=> rw [← ih]; change H.leaf (k+1) (F _ (days Y h (k+1) W' R a w))= _; rw [nectar_next Y h k W' R a w (arriving Y h i k a w c t), P'.tall k (p.trans t), H.up Y h k W' R a]; rfl
private lemma habit : ∃ y:H.space, ∀ᶠ i:ℕ in atTop,(δ i) w=y:=by obtain ⟨n,t,v⟩:= ((eventually_ge_atTop s).and (arrived Y h w.val)).exists; exact ⟨_,(eventually_ge_atTop n).mono fun i p=> view Y h s n i W' R a H w F B P' t p v⟩
private abbrev look :H.space:= (habit Y h s W' R a H w F B P').choose
local notation "Φ" w:max=> look Y h s W' R a H w F B P'
private lemma hairpin (p:s ≤ i)(t:Arrive Y h w.val i): (δ i) w= Φ w:=by
 obtain ⟨k,g,q⟩:= ((eventually_ge_atTop i).and ((habit Y h s W' R a H w F B P').choose_spec)).exists; exact (view Y h s i k W' R a H w F B P' p g t).symm.trans q
private def quip : Vect Y h a 0 →ₗ[ℂ] H.space where
 toFun w:= look Y h s W' R a H w F B P'
 map_add' u v:= by
    obtain ⟨n,p,q,g,t⟩:= ((eventually_ge_atTop s).and (((arrived Y h u.val).and ((arrived Y h v.val).and (arrived Y h (u+v).val))))).exists
    rw [←hairpin Y h s n W' R a H _ F B P' p t,←hairpin Y h s n W' R a H _ F B P' p q,←hairpin Y h s n W' R a H _ F B P' p g,map_add]
 map_smul' c v:=by
    obtain ⟨n,p,g,t⟩:= ((eventually_ge_atTop s).and ((arrived Y h v.val).and (arrived Y h (c • v).val))).exists
    rw [←hairpin Y h s n W' R a H _ F B P' p t,←hairpin Y h s n W' R a H _ F B P' p g,map_smul]; rfl
lemma quip_norm : ‖(quip Y h s W' R a H F B P') w‖ ≤ B*‖H.value w‖:=by
 obtain ⟨n,t,c⟩:= ((eventually_ge_atTop s).and (arrived Y h w.val)).exists
 rw [←H.docks n w c, show (quip Y h s W' R a H F B P') w =_ from (hairpin Y h s n W' R a H w F B P' t c).symm]; exact P'.fit n t _

def criterion : H.space.Op:= (quip Y h s W' R a H F B P').extendOfNorm H.value
lemma criterion_norm (p:0≤B): ‖criterion Y h s W' R a H F B P'‖ ≤ B:= LinearMap.opNorm_extendOfNorm_le H.varied p fun x=>quip_norm Y h s W' R a H x F B P'
lemma criterion_seed (p:s ≤ i): criterion Y h s W' R a H F B P' ((G i) x)=(G i) (F i x):=by
 have h': Arrive Y h (seedling Y h i a x).val i:= pulse_arr Y h i x.val
 rw [H.fleets i x]; unfold criterion; rw [LinearMap.extendOfNorm_eq H.varied ⟨B,fun i=>quip_norm Y h s W' R a H i F B P'⟩]
 refine (hairpin Y h s i W' R a H (seedling Y h i a x) F B P' p h').symm.trans ?_; unfold dressing; simp_rw [LinearMap.comp_apply,fullDay]

#print axioms criterion
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
