import YM.SU5.Reconstruction.PolarArchives.Panorama
import YM.SU5.Reconstruction.PolarArchives.Morning
-- Header
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
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
open WindRose
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (j:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped j false (C j) →⋆ₐ[ℂ] ℂ)
local notation "Mirror" i:max=> flipMark i (tent Y H)
open Stormwatch ConePrice Germ SelectionAnalysis CrossedFrame
open YM.ConePrice.Storm
local notation "µ" => Domain Y H G false Set.univ
local notation "Gt" => marks (timeMesh Λ)
local notation "au"=>move K
variable (P:Ramp)
local notation "H₀"=> Ark.Ht Y H G.history.circuit P.a 0 false (C P.a)
local notation "A"=>Aurora Y H V G.history P.a false (C P.a)
local notation "Pc"=>album Y H V G C P.a
local notation "pay"=> LightBudget.prepaid Y H V G P.a (C P.a)
local notation "vc"=>seat0 Y H V G.history P.a false (C P.a)
local notation "px"=> (A).orthogonalProjectionOnto
local notation "Nₐ"=> Domain Y H G false (flank P.a 0)
local notation "τ" => gust P (tent Y H)
open Chambers
local notation "μₜ" t:max=>move (tent Y H) (eject P.a t)
variable {q:Bool}{U:Set RSpace}
local notation "K₀"=>displayAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Hₛ"=> groundRoom Y H V G.history P.a false (C P.a)
local notation "Ωχ"=> courseValue Y H V G
local notation "Kw"=>driveAlgebra Y H V G.history G.clipped P.a false (C P.a)
local notation "Rs"=> reduceToDisplay Y H V G.history G.clipped P.a false (C P.a)
local notation "RX"=>rotateQ P K
local notation "α"=> orbit Y H V G C P
local notation "VR"=> Veer Y H V G P
local notation "FZ" p:max=> (Pc p).val vc
local notation "Lt"=> helm Y H V G C P
variable (gap:ℝ≥0)(h:Rectitude Y H V G P gap)
local notation "zone" q:max=> Domain Y H G q (Acres P gap)
lemma proxy (v:Domain Y H G false Set.univ): ∃ w:Domain Y H G false Set.univ, w.val ∈ Domain Y H G true univ∧ Pc w=Pc v:=by
 obtain ⟨s,x,rfl⟩ := (eventually_enclosed Y H G v).exists; let f:=asLoose K x.val
 obtain ⟨u,z,h⟩:= cap_in_common Y H V s G.history G.clipped f ((marksSpec false f).1.paid.choose_spec)
 let b:Dome K:=⟨u.val,(marksSpec true u).1⟩; refine ⟨⟨ticket Y H G (s+1) b,ticket_loose ..⟩,ticket_mem Y H G ?_, ?_⟩
 · rw [insideAt_univ_singlet]; exact (enclave_spec K).2 ((marksSpec true u).2 rfl)
 change Pc _ = Pc (⟨ticket Y H G s x.val,ticket_loose ..⟩)
 rw [atStamp,atStamp]; exact h P.a (C P.a) -- tune
noncomputable def TerrainOf (x:Domain Y H G true (Acres P gap)) : Domain Y H G false Set.univ :=
 ⟨τ x.val * x.val,domain_loose Y H G univ (pay_your Y H V G P gap x.property x.property)⟩
local notation "πχ"=> TerrainOf Y H V G P gap
private lemma signForm {J:Calibration}(w x:Sky J): gust P J w * (gust P J x*x) * w= gust P J (x*w) * (x*w):=by
 rw [gust_mul]; ac_rfl

omit h in
private lemma dismissal (x:zone true): ∃ z:ℝ, ∀ d:ℝ,z<d→∀ w:Sky (tent Y H),w∈ D true (carton P d) → x.val*w ∈ Domain Y H G true (Acres P gap):=by
 obtain ⟨u,p,c,q⟩:=(compact_domain Y H G).1 x.property
 obtain ⟨z,hx⟩:=(p.image (continuous_apply P.a)).bddAbove
 refine ⟨max z (gap:ℝ),fun d t w h=> domain_mult_to Y H G q h (Set.disjoint_left.mpr fun u v a=> not_le.mpr (lt_of_le_of_lt (hx (mem_image_of_mem _ v)) (lt_of_le_of_lt (le_max_left ..) t)) a.1) c fun y a=>?_⟩
 change (gap:ℝ)<y P.a+y P.b; linarith [gap.property,le_max_right z (gap:ℝ), (show d≤ y P.a from a.1), (show d≤ y P.b from a.2)]
include h
private lemma boom (x:zone true)(f:Domain Y H G false univ)(m:marks (timeMesh Λ)) (y:ℕ→Domain Y H G true (carton P (m:ℝ)))(t:Gatemark Y H V G C P m true f y){B:Kw}(hb:DotPrice Y H V G C P m (πχ x) B)
    (u:∀ i, x.val*(y i).val ∈ Domain Y H G true (Acres P gap)): 0 ≤ inner ℂ (Lt (FZ f)) ((Pc (πχ x)).val (FZ f)):=by
 rw [dispatched]
 refine ge_of_tendsto (moment Y H V G C P m f (πχ x) f hb t t) ?_; apply Eventually.of_forall; intro i
 let f':zone true:= ⟨_,u i⟩; have e: τ (y i).val * (πχ x).val * (y i).val=(πχ f').val:=signForm P (y i).val x.val
 have h': (⟨_,hb.has _ _ (y i) (y i)⟩:Domain Y H G false univ)=πχ f':= Subtype.ext e
 change 0 ≤ Ωχ ⟨_,hb.has _ _ (y i) (y i)⟩; rw [h']; exact h f' (πχ f').property
set_option maxHeartbeats 650000 in
lemma leaseCost (x:Domain Y H G true (Acres P gap))(f: Domain Y H G false univ): 0 ≤ inner ℂ (Lt (FZ f)) ((Pc (πχ x)).val (FZ f)):=by
 obtain ⟨u,q,k⟩:= proxy Y H V G C P f; rw [←k]
 obtain ⟨d,t⟩:= dismissal Y H G P gap x; obtain ⟨D₁,e⟩:= resolve_path Y H G P (πχ x).val (πχ x).property -- notation D!!
 obtain ⟨m,v⟩:= anywhere Λ (max 0 (max d D₁))
 let Bx:= atDot Y H V G C P m (show 0 < m from (show 0 < (m:ℝ) from lt_of_le_of_lt (le_max_left ..) v)) (πχ x) (e _ ((le_max_right d D₁).trans ((le_max_right ..).trans v.le)))
 let y:= fullMark Y H V G C P m true u q
 exact boom Y H V G C P gap h x u m _ y.choose_spec (B:=Bx.choose) Bx.choose_spec fun i=> t _ (lt_of_le_of_lt ((le_max_left d D₁).trans (le_max_right ..)) v) _ (y.choose i).property
lemma beyond(x: Domain Y H G true (Acres P gap))(p:Hₛ): 0 ≤ inner ℂ (Lt p) ((Pc (πχ x)).val p):=
  closure_minimal (s:= Set.range (fun v:Domain Y H G false univ=> FZ v)) (t:={y:Hₛ|0≤ inner ℂ (Lt y) ((Pc (πχ x)).val y)}) (by rintro _ ⟨v,rfl⟩; exact leaseCost Y H V G C P gap h x v) (isClosed_le continuous_const ((Lt).continuous.inner (Pc (πχ x)).val.continuous)) (archives Y H V G C P p)
lemma rotor_funded (p:Hₛ): Lt p=p:=by
 let q:= Lt p-p; let x: zone true:= ⟨1,domain_one ..⟩; have hx:= beyond Y H V G C P gap h x q; rw [show πχ x=unity Y H G from Subtype.ext (show gust P K 1*1=1 from by rw [gust_unit,mul_one]), unit_archive,show Lt q= -q from (by rw [show q=Lt p-p from rfl, map_sub, returner,neg_sub])] at hx
 change 0 ≤ inner ℂ (-q) q at hx; rw [inner_neg_left] at hx; exact sub_eq_zero.mp (inner_self_eq_zero (𝕜:=ℂ) |>.mp (le_antisymm (neg_nonneg.mp hx) (by rw [inner_self_eq_norm_sq_to_K]; positivity))) -- linarith ℂ invalid! replace
lemma state_root (p: displayAlgebra Y H V G.history G.clipped P.a false (C P.a)): orbit Y H V G C P p=p:=by
 apply Subtype.ext; ext1 x; change Lt (p.val ((Lt).symm x))= _; rw [rotor_funded _ _ _ _ _ _ _ h,show (Lt).symm x=x from (Lt).injective (by rw [LinearIsometryEquiv.apply_symm_apply,rotor_funded Y H V G C P gap h])]
lemma voting (x: Domain Y H G true (Acres P gap)): 0≤ Pc (TerrainOf Y H V G P gap x):=by
 let B: (Hₛ).Op:= (Pc (πχ x)).val -- notation tune!
 change (0:(Hₛ).Op) ≤ B -- tune
 apply (ContinuousLinearMap.nonneg_iff_isPositive B).mpr
 apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp ∘ (LinearMap.isPositive_iff_complex B.toLinearMap).2
 intro u
 have e:=beyond Y H V G C P gap h x u; rw [rotor_funded _ _ _ _ _ _ _ h] at e; have ht:0≤ inner ℂ (B u) u:=by rw [← inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using e
 exact ⟨Complex.ext rfl ht.2, ht.1⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
