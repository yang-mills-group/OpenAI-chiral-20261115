import YM.SU5.Selected.Prag.Book
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (C : ∀ j:Axis, Arena Y H Q.circuit j 0 false)
namespace Summer
open Germ
open Tapestry CF.Pannier.Chancel.Attic.Cairn
open Spectral Spectral.Alps Germ.Alliance
open Fern Fern.Curtain Fern.Planet
open CF.Pannier.Chancel.Attic.Cairn.Giant CF.Pannier.Chancel.Attic.Cairn.Giant.Voice
namespace Mills
variable (s:ℕ)(j:Axis)(X:Giant){W:Window.Family} (F G:X.SpireBook (tent Y H) W) -- fix
local notation "R"=> X.Broad
variable (χ:CapCharacter Y H V Q Qc 3 false (C 3))
local notation "Θ"=> escort Y H V Q Qc 3 false (C 3)
local notation "B₁" v:max=> (Θ v (C v) χ)
variable (U: Birthplace Y H V Q Qc 3 false (C 3) (escort Y H V Q Qc 3 false (C 3) 3 (C 3) χ))
variable (x₀: Voice.Tonic X) {c:ℝ}(p: Planet.Saturn Y H V Q Qc C s X F G χ x₀ c)
local notation "ℓ"=> declination' Y H X
local notation "L"=> (3:Axis)
local notation "y₀"=> (Voice.ink X K F x₀).val
local notation "y₁"=> (Voice.burnish X K F G x₀).val
local notation "y₂"=> (Voice.flame X K F x₀).val
local notation "V₀"=> Summer.Polaris Y H V Q Qc L false (C L) U
local notation "Γ₀"=> Summer.terse Y H V Q Qc C L χ U
local notation "S"=> Summer.skyline Y H V Q Qc C L χ U
local notation "Σ"=> Diary.jetTime Y H V Q Qc L false (C L) U
local notation "κ"=> markedActor Y H V Q Qc L false (C L) U s
local notation "K₁" x:max=> Γ₀ (κ x)
local notation "Δ"=> whenly (timeMesh Λ) s 1
local notation "Ω"=> terse Y H V Q Qc C L χ U (vacuum Y H V Q Qc L false (C L) U)
local notation "Ξ"=> Actress.Label Y H L false
local notation "Φ"=> (V₀).Realm (look L)
local notation "F₊"=> (Tower.Field Y H s L 0 false)
local notation "ρ"=> Torrent.fare
local notation "τ"=> relocate (tent Y H) L
local notation "W'"=> Summer.worldShelf Y H V Q Qc C L χ U
-- prove both strict evolution & cast. actual Burn, not theoretical before anywhere.
local notation "ν" y:max z:max f:max=> Library Y H V Q Qc C L s χ U y z (declination' Y H X) y₀ f X.ascY X.ascX
variable (x y z:Tower.Field Y H s 3 0 false)(tX: Library Y H V Q Qc C 3 s χ U x y (declination' Y H X) (Voice.ink X (tent Y H) F x₀).val (Voice.burnish X (tent Y H) F G x₀).val X.ascY X.ascX) -- goal term syntax notation variable? x uses F₊ bug! use explicit
    (tZ: Library Y H V Q Qc C 3 s χ U x z (declination' Y H X) (Voice.ink X (tent Y H) F x₀).val (Voice.flame X (tent Y H) F x₀).val X.ascY X.ascX)
private lemma sub_relocate(Zz:Calibration)(j:Axis)(a:ℤ)(x y:Family Zz): relocate Zz j a (x-y)=relocate Zz j a x-relocate Zz j a y := by rw [sub_eq_add_neg,←neg_one_smul ℂ y]; unfold relocate; rw [chime_plus,chime_scale, neg_one_smul,←sub_eq_add_neg]
private lemma scales_take(Z:Calibration)(H P: Family Z)(x:ℤ) (t:H=P-relocate Z 3 1 P)(f g: Family Z)(b:f=relocate Z 3 x H)(q:g=relocate Z 3 x P)(p:relocate Z 3 x (relocate Z 3 1 P) = relocate Z 3 1 (relocate Z 3 x P)): f = g-relocate Z 3 1 g:= by rw [b,q,t,sub_relocate,p]
include tX tZ p
lemma scales : y=z- tick Y H s L 0 false 2 z :=by
 let q:= (p.lairs 3); have h:(y₁)= (y₂)- relocate K L 1 (y₂) := q.realign; let c:= -(declination' Y H X 3)-1; let D':= y₂; let R':= q.there.renteds.1.widen
 have hv: τ c (τ 1 D')= τ 1 (τ c D'):= by rw [relocate_sums K _ _ _ (aux_test R'), relocate_sums K _ _ _ (aux_test R'),add_comm]
 have he : y.val=z.val- τ 1 z.val:= scales_take K (y₁) D' c h y.val z.val tX.heir.bore.1 tZ.heir.bore.1 hv
 apply Subtype.ext; change y.val=z.val - ((tick Y H s L 0 false 2 z).val); rw [show (tick Y H s L 0 false 2 z).val=_ from (show _ =τ 1 z.val from timed_apply Y H L false s 1 z)]; exact he
omit p tZ tX in
private lemma descendSub {A:Hilbert} {Γ:AddSubgroup ℝ}{j:Axis} (P:Alliance (Trans j) Γ A)(dp:Dense (Γ:Set ℝ))(B:OS.Semigroup A j)(q: ∀ i v t,Commute ((P.crew i).play v) (B.E t))(x y:A)(t:ℝ≥0)(e:x=y-B.E t y) : prism P x=prism P y-(P.Frog dp B q).E t (prism P y):= by rw [←Alliance.prism_early,e,← descends, ←descends, ←descends,map_sub]

lemma esprit : K₁ y= K₁ z - ((S).E Δ) (K₁ z):=by
 let d := Δ; let f : Φ:= K₁ z; let c := Σ; let L':= S; let Φ':= descendH V₀
 have hp:(S).E d f=Γ₀ ((c.E d) (κ z)):= (Alliance.prism_early V₀ (daylight (timeMesh Λ)) Σ (source_heat Y H V Q Qc L false (C L) U) d (κ z)).symm
 have hx : κ y= (κ z)-c.E d (κ z):=(congrArg κ (scales Y H V Q Qc C s X F G χ U x₀ p x y z tX tZ)).trans ((map_sub (κ) z _).trans (congrArg ((κ z)-·) (Curtain.when_clock Y H V Q Qc L (C L) s U z 1).symm)) -- markedActor linearMap?
 exact descendSub (V₀) (daylight (timeMesh Λ)) (Σ) (source_heat Y H V Q Qc L false (C L) U) (κ y) (κ z) d hx
omit tZ
lemma puissant : (ρ)< ‖inner ℂ (K₁ x) ((S).E Δ (K₁ y))‖:=by
 have hx:= (p.lairs 3).here.renteds.1.widen; let f:= phaseRead Y H V Q Qc 3 (C 3) (B₁ 3) s; have he: inner ℂ (K₁ x) ((S).E Δ (K₁ y))= f (y₀*y₁):= (tX.moon 0).trans (congrArg (fun v=> f (y₀*v)) (relocate_zero K L (aux_test hx))); exact (p.selection_ 3).trans_eq (congrArg norm he).symm
omit p tX
-- kernel helpers
private lemma pur {H:Hilbert}{j:Axis}(S':OS.Semigroup H j)(x y:H)(t:ℝ≥0)(p:x=y-S'.E t y): S'.orth x=0:=by rw [p,map_sub ,Spectral.Alps.powerS,sub_self]
#print pur
lemma prizeRide {H:Hilbert}{j:Axis}(S':OS.Semigroup H j)(x y:H)(t:ℝ≥0)(q:ℝ)(d:0<q)(e:0<t)(p:S'.orth y=0)(w:q< ‖inner ℂ x (S'.E t y)‖) :∃ v:ℝ≥0,Curtain.Switch H S' x y t v q:=by
 have hv:Tendsto (fun k:ℝ≥0=> ‖inner ℂ x (S'.E t y)- inner ℂ x (S'.E k y)‖) atTop (𝓝 ‖inner ℂ x (S'.E t y)‖) := by simpa only [p,inner_zero_right,sub_zero] using (tendsto_const_nhds (x:=inner ℂ x (S'.E t y))|>.sub (tendsto_const_nhds (x:=x)|>.inner (S'.emerges y))|>.norm)
 obtain ⟨v,h,g⟩:= (eventually_gt_atTop t|>.and (hv.eventually (lt_mem_nhds w))).exists; exact ⟨v,Curtain.departure H S' x y t v q d e h (by rw [ContinuousLinearMap.sub_apply,inner_sub_right]; exact g)⟩
variable {D0 D1:Actress.Label Y H 3 false}
local notation "kTw" x:max=> (worldShelf Y H V Q Qc C L χ U (x,0))
structure Fierce (Ax A':Ξ) : Prop where
 folio : Library Y H V Q Qc C L s χ U x z (declination' Y H X) (y₀) (y₂) X.ascY X.ascX
 campus : Manuscript Y H V Q Qc C L s χ U x y Ax A' (declination' Y H X) y₀ y₁ X.ascY X.ascX
 neve: Torrent.fare < ‖inner ℂ (K₁ x) ((S).E Δ (K₁ y))‖
 energy : K₁ y= K₁ z- (S).E Δ (K₁ z)
 polar: (S).orth (K₁ y)=0∧ inner ℂ Ω (K₁ y) =0 -- centered true.
 rising: ∃ v:ℝ≥0,Curtain.Switch Φ (S) (K₁ x) (K₁ y) (Δ) v (ρ)
 realArc (i:ℝ) : ∃ t:ℝ,t≠i ∧ Torrent.fare/2 < ‖Alps.fare S Ω (kTw Ax) (kTw A') t-Alps.fare S Ω (kTw Ax) (kTw A') i‖
 crossedD (t:ℝ≥0)(p:t>0): ¬ Commute ((S).E t) (kTw Ax)
#print Fierce.mk
private lemma centering {H:Hilbert}{j:Axis}(S':OS.Semigroup H j)(ω₀ x:H)(p:ω₀∈S'.ground)(t:S'.orth x=0): inner ℂ ω₀ x=0:=by calc
 _=inner ℂ (S'.orth ω₀) x:=congrArg (fun u:H=>inner ℂ u x) (Submodule.starProjection_eq_self_iff.mpr p).symm
 _= _:=by rw [←ContinuousLinearMap.adjoint_inner_right S'.orth,Spectral.Alps.engaged,t,inner_zero_right]
private lemma rewardsB {H:Hilbert}{j:Axis}(S':OS.Semigroup H j)(ω₀ x y:H)(p:ω₀∈S'.ground)(v w:ℝ≥0)(c:ℝ)(A B:H.Op)(q:A ω₀=x)(h:B ω₀=y)(t:Curtain.Switch H S' x y v w c) : (∀ t₀:ℝ,∃ t':ℝ,t'≠t₀ ∧ c/2< ‖Alps.fare S' ω₀ A B t'-Alps.fare S' ω₀ A B t₀‖) ∧ ∀ d':ℝ≥0,d'>0→ ¬Commute (S'.E d') A:=by
 refine ⟨fun b=>?_,fun i p' => ?_⟩; · obtain ⟨a,u,t,v⟩:= t.epoch b; exact ⟨a,u,by rw [Alps.utc S' ω₀ p A B x y q h a,Alps.utc S' ω₀ p A B x y q h b,←inner_sub_right,←ContinuousLinearMap.sub_apply]; exact t⟩
 have he:= t.north 0; exact Alps.veto S' i A p p' (by rw [q]; exact (show S'.E 0 x=x from DFunLike.congr_fun S'.eZero x) ▸ he.1)
include tX tZ p
lemma earths (d:Manuscript Y H V Q Qc C 3 s χ U x y D0 D1 (declination' Y H X) (Voice.ink X K F x₀).val (Voice.burnish X K F G x₀).val X.ascY X.ascX): Fierce Y H V Q Qc C s X F G χ U x₀ x y z D0 D1:=by
 let i:= K₁ y; have he:=esprit Y H V Q Qc C s X F G χ U x₀ p x y z tX tZ; have hx:=pur (S) _ _ Δ he; have hu:=puissant Y H V Q Qc C s X F G χ U x₀ p x y tX
 let P:=prizeRide (S) _ _ _ (ρ) Torrent.fare_p (when_pos _ _ 1 zero_lt_one) hx hu; let f:=P.choose; have hf:=P.choose_spec; let T:= Summer.wHeat Y H V Q Qc C L χ U; have hv:= rewardsB (S) (Ω) (K₁ x) (K₁ y) T _ f _ (kTw D0) (kTw D1) d.fly.2.2.1 d.sail_.2.2.1 hf; exact ⟨tZ,d, hu,he, ⟨hx,centering (S) _ _ T hx⟩,P,hv.1,hv.2⟩
end Mills
end Summer
end YM.CF.Buffered.Afterglow.Tower.Selection
open YM.CF.Buffered.Afterglow.Tower.Selection.Summer.Mills
#print axioms scales
#print axioms esprit
#print axioms Fierce
#print axioms earths
#check @earths
