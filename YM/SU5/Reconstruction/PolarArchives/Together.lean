import YM.SU5.Reconstruction.PolarArchives.Sailing
import YM.SU5.Reconstruction.PolarArchives.Terrain
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
noncomputable def Tango(P:Ramp): Domain Y H G false Set.univ →ₗ⋆[ℂ] Domain Y H G false Set.univ :=
 ((gust P K).comp (µ).subtype).codRestrict µ fun x=> domain_le_lawDomain _ _ _ _ (shelters Y H V G P x.property)
local notation "TT"=> Tango Y H V G P
noncomputable def Veer(P:Ramp): Domain Y H G false Set.univ →ₗ[ℂ] Domain Y H G false Set.univ :=
 ((rotateQ P K).comp (µ).subtype).codRestrict µ fun x=> domain_le_lawDomain _ _ _ _ (panels Y H V G P x.property)
local notation "VR"=> Veer Y H V G P
lemma newsTags (w:Domain Y H G false Set.univ): Pc (TT w)=star (Pc (VR w)) ∧ Pc (VR (VR w))=Pc w:=
 ⟨((congrArg star (mirror_tone Y H V G C P.a P.a (TT w).property (show flipMark P.a K (TT w).val∈µ from (VR w).property))).trans (star_star _)).symm, comp_amount Y H V G C P w.property _⟩ -- tune
lemma resolve_path (f:Sky (tent Y H))(h:f∈Domain Y H G q Set.univ):∃ d:ℝ,∀ m:ℝ, d ≤ m→f∈ Domain Y H G q (strip P.a (-m) m):=by
 obtain ⟨u,c,_,p⟩:=(compact_domain Y H G).1 h; obtain ⟨b,h⟩:=(c.image (continuous_apply P.a)).bddAbove; obtain ⟨a,t⟩:=(c.image (continuous_apply P.a)).bddBelow; refine ⟨max b (-a),fun m u₀=> domain_mono Y H G ?_ p⟩; intro y r; have hx:y P.a ≤ b:= h ⟨y,r,rfl⟩; have hy:a≤ y P.a:=t ⟨y,r,rfl⟩; exact ⟨by linarith [le_max_right b (-a)], hx.trans ((le_max_left ..).trans u₀)⟩
local notation "FZ" p:max=> (Pc p).val vc
lemma moment (m:marks (timeMesh Λ)){q r:Bool}(p w z:Domain Y H G false Set.univ){B: driveAlgebra Y H V G.history G.clipped P.a false (C P.a)} (b:DotPrice Y H V G C P m w B){u v}(t:Gatemark Y H V G C P m q p u)(h:Gatemark Y H V G C P m r z v):
   Tendsto (fun n=> courseValue Y H V G ⟨(τ (u n).val)*w.val*(v n).val,b.has _ _ (u n) (v n)⟩) atTop
   (𝓝 (inner ℂ (FZ (VR p)) ((Pc w).val (FZ z)))):=by
 rw [←b.views,reduce_val]
 change Tendsto _ _ (𝓝 (inner ℂ (FZ (VR p)) (px (B.val (FZ z).val))))
 rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
 simp_rw [b.knows]; exact (t.right (VR p).property).inner ((B.val.continuous.tendsto (FZ z).val).comp h.left)
private lemma turnPrices {J:Calibration}(f g w:Sky J) : gust P J f*w*g= gust P J (gust P J g*gust P J w*f):=by
 rw [gust_mul,gust_mul,gust_square,gust_square]; rw [mul_comm (gust P J f*w),mul_comm (gust P J f) w,mul_assoc]
private lemma record_swap(w f g:Sky (tent Y H))(x:gust P K f*w*g∈µ)(y:gust P K g*gust P K w*f∈µ): Ωχ ⟨gust P K f*w*g,x⟩ = star (Ωχ ⟨gust P K g*gust P K w*f,y⟩):=by
 let a:= turnPrices P f g w; have h: gust P K (gust P K g*gust P K w*f)∈µ:= a ▸ x
 exact (congrArg Ωχ (Subtype.ext a)).trans (staff Y H V G P y h)
set_option maxHeartbeats 770000 in
private lemma twoIn (x y w:Domain Y H G false Set.univ) (m:MeshClock.marks (timeMesh Λ)) (u v:ℕ→Domain Y H G false (carton P (m:ℝ)))
    (hx:Gatemark Y H V G C P m false x u)(hy:Gatemark Y H V G C P m false y v){B E':driveAlgebra Y H V G.history G.clipped P.a false (C P.a)}(hb:DotPrice Y H V G C P m w B)(hc:DotPrice Y H V G C P m (TT w) E'): inner ℂ (FZ (VR x)) ((Pc w).val (FZ y))=
    star (inner ℂ (FZ (VR y)) ((Pc (TT w)).val (FZ x))):=by
 have a:= moment Y H V G C P m x w y hb hx hy
 let f(t:ℕ):= Ωχ ⟨τ (u t).val*w.val*(v t).val, hb.has _ _ (u t) (v t)⟩
 let g(t:ℕ):= Ωχ ⟨τ (v t).val*(TT w).val*(u t).val, hc.has _ _ (v t) (u t)⟩
 have b:Tendsto (fun i=>star (g i)) atTop (𝓝 (star (inner ℂ (FZ (VR y)) ((Pc (TT w)).val (FZ x))))) := (moment Y H V G C P m y (TT w) x hc hy hx).star
 have h(t:ℕ): f t=star (g t):= record_swap Y H V G P w.val (u t).val (v t).val (hb.has _ _ (u t) (v t)) (hc.has _ _ (v t) (u t))
 exact tendsto_nhds_unique_of_eventuallyEq (show Tendsto f atTop _ from a) (b) (Eventually.of_forall h)
set_option maxHeartbeats 560000 in
private lemma at_station (x y w:Domain Y H G false Set.univ) (m:MeshClock.marks (timeMesh Λ))(hm:0 < m)(g:w.val ∈ D false (strip P.a (-(m:ℝ)) (m:ℝ)))(f:(TT w).val∈ D false (strip P.a (-(m:ℝ)) (m:ℝ))): inner ℂ (FZ (VR x)) ((Pc w).val (FZ y))=
    star (inner ℂ (FZ (VR y)) ((Pc (TT w)).val (FZ x))):=by
 let hb: DotPrice Y H V G C P m w _ := (atDot Y H V G C P m hm w g).choose_spec
 let hc: DotPrice Y H V G C P m (TT w) _:=(atDot Y H V G C P m hm (TT w) f).choose_spec
 have hx:= (fullMark Y H V G C P m false x x.property).choose_spec; have hy:= (fullMark Y H V G C P m false y y.property).choose_spec
 exact twoIn Y H V G C P x y w m _ _ hx hy hb hc

set_option maxHeartbeats 600000 in
lemma partner (x y w:Domain Y H G false Set.univ): inner ℂ (FZ (VR x)) ((Pc w).val (FZ y))=
    star (inner ℂ (FZ (VR y)) ((Pc (TT w)).val (FZ x))):=by
 obtain ⟨d,B⟩:= resolve_path Y H G P w.val w.property; obtain ⟨a,Bx⟩:= resolve_path Y H G P (TT w).val (TT w).property
 obtain ⟨m,h⟩:= anywhere Λ (max 0 (max d a))
 have hm:0 < m:=(show 0 < (m:ℝ) from lt_of_le_of_lt (le_max_left ..) h)
 exact at_station Y H V G C P x y w m hm (B _ ((le_max_left d a).trans ((le_max_right ..).trans h.le))) (Bx _ ((le_max_right d a).trans ((le_max_right ..).trans h.le)))

end YM.CF.Buffered.Afterglow.Tower.FirstWindows.PolarArchives
