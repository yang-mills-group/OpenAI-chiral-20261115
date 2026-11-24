import YM.SU5.LoomForce.Sails
import YM.SU5.LoomForce.SpinReaches

/-! Exact colour and pair Wick tally, on actual finite regulator comparator.
 Can call even on any sparse table of true Staff costs, Moment paths with the
 support licences, and at any fixed arity before room payments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
open Function Filter Metric Fock Finset Lat Lattice Laurent Next.Free Cube Tulip Scroll Spire Pastry RP Branch
  Wilson Phase SU Rush Mir Reflect Lifted Window Skye Dial Analysis MeasureTheory
open Lamour Lamour.Bridge Celeste Clock Hookah Hiro RG Girt
open Py Py.Rate Py.Rate.LocalLimit Preparation Yoke Papal Tapestry Journey
open Ballad EmberWind CF.Pannier.Chancel WakeInvestment Gleam Gleam.Wake
open Jewel Regis Regis.Head Regis.Head.Brecht Regis.Circuit Regis.Resonance Exterior ProbabilityTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
     ContDiff Classical
variable {I : Type*} [Fintype I]
variable {P:Preparation} {j:ℕ} (Y : P.Course (VolumeCape.Dream.Nimbus j)) (s i k:ℕ)

omit [Fintype I] in
private lemma gauss_tally {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H][MeasurableSpace H][BorelSpace H]
    (Q : Chart (loomZ I))(tag : I → Sewer)(P : List I)(U : loomG I → H) :
    (∫ x, fullPay (fun i=> inner ℝ (U i) x) Q tag P ∂stdGaussian H) =
      quoted tag P Q (fun i j=> WickG.grainG (U i) (U j)) := by
  let μ := stdGaussian H; let G(z : H) (t:loomG I):= inner ℝ (U t) z
  let φ (r:Route I) (z:H) := routePay (G z) Q r; let L(r:Route I) := ((paperF r).map U)
  have he (D : List (loomG I))(y:H) : (D.map (G y)).prod=Regis.Resonance.payday (D.map U) y := by induction D with|nil=> rfl|cons d D ih=> exact congrArg (G y d * ·) ih
  have hw(r:Route I):φ r=fun z:H=> quoteSpin r Q * (Regis.Resonance.payday (L r) z:ℂ):= by
    unfold φ routePay L colorGram; simp_rw [he]
  have ht(r:Route I):Integrable (φ r) μ := hw r ▸ ((payday_val (L r)).accepted.ofReal.const_mul _)
  let f(P:List (Route I))(z:H):= Chain.tally P (fun r=> φ r z)
  have hp(l:List (Route I)): Integrable (f l) μ:=by induction l with|nil=>exact integrable_zero ..|cons i l ih=>exact (ht i).add ih
  unfold fullPay quoted; generalize booths tag P = B
  induction B with
  | nil => simp [Chain.tally]
  | cons i l ih=>
    -- generalize w?
    simp_rw [Chain.tally_more]; rw [integral_add (ht i) (hp l)]; congr 1; change (∫ x,φ i x∂μ)=_ ; rw [hw, integral_const_mul, integral_complex_ofReal]; unfold quote; rw [WickG.census]

section finite
local notation "N₁" => side Y i s
local notation "χ" => Y.uv k-s
local notation "Ξ" => P.V.L.H (Y.uv k - s)
local notation "Ω" => stamen (P.V.L.mood (Y.uv k - s)) (P.V.L.tied (Y.uv k - s)) (More (side Y i s))
local notation "ψ" => P.K.top.clip

variable (W:I→ Staff)(ρ q:ℝ)
abbrev faceBody (W:Staff)(n:Side): Body 2 (More n) := ((W.localFace n).1,plaquette W.face.2)
def pieceColor (a : loomG I): Ω := q • plar (P.V.L.mood (Y.uv k - s)) (P.V.L.tied (Y.uv k - s)) (faceBody (W a.1) N₁)
  (reachCost Y s i k ρ) a.2
noncomputable def hueCost : Chart (loomG I) := fun a b=>
  (q*reachCost Y s i k ρ:ℂ)^2 * ↑(sch (G:=SU.group) a.2 b.2) *
    rimble (More N₁) Ξ (faceBody (W a.1) N₁) (faceBody (W b.1) N₁)

lemma hueCost_collect (Q : Chart (loomZ I)) (tag : I → Sewer) (L : List I) :
    seatT Y s i k (scout W N₁) (lensPay Q tag L q) ρ = quoted tag L Q (hueCost Y s i k W ρ q) := by
  let d:= Y.uv k - s; let R:=P.V.L; let t:=reachCost Y s i k ρ
  let A:= R.mood d; let B:=R.tied d; let M:= More N₁; let G:= SU.group; let H:= hueCost Y s i k W ρ q
  let U:= pieceColor Y s i k W ρ q; let I':=scout W N₁
  let u:= R.roof d; have v: Even M.val := ⟨(N₁).val, show (N₁).val*2=_ from mul_two _⟩
  have Hs : H=fun i j=> WickG.grainG (U i) (U j):=by
    funext i' j'; let a:= faceBody (W i'.1) N₁; let b:= faceBody (W j'.1) N₁
    have hp:= chimes A B (u.2.1 M) u.1 P.K.width i'.2 j'.2 a b v
    simp_rw [←joy,appraisal] at hp
    change _=((↑(inner ℝ (q • plar A B a t i'.2) (q • plar A B b t j'.2)):ℂ))
    unfold plar; rw [smul_smul,smul_smul,real_inner_smul_left _ _ (q*t),real_inner_smul_right _ _ (q*t)]
    push_cast; rw [hp]; unfold H hueCost; unfold t -- tune
    ring
  change seatT _ _ _ _ I' _ _= quoted tag L Q H
  rw [Hs, ← gauss_tally]
  let F:= lensPay Q tag L q; have hp(x:Ω): I'.basin t F ψ x.val= fullPay (fun i=> inner ℝ (U i) x) Q tag L:=by
    let f:= tiler A B (n:=M)
    obtain ⟨k,rfl⟩:= (f.surjective_rangeRestrict x)
    rw [show (f.rangeRestrict k).val=f k from rfl,Vessel.belly]
    change fullPay _ Q tag L=_
    apply congrArg (fun p:loomG I→ℝ => fullPay p Q tag L); funext i'
    let n' := (W i'.1).localFace N₁; let a':= i'.2; let z:=f k
    have hw: Etch.river ψ n' z=Work.F03.faceCurl n' k:= Etch.river_now _ A B n' k
    let k' : stamen A B (More (side Y i s)) := (tiler A B).rangeRestrict k; let g := (n'.1,plaquette n'.2)
    change q * (t * (Work.F03.faceCurl n' k a')) = inner ℝ (q • t • trill A B a' g) k'
    rw [real_inner_smul_left (t • trill A B a' g) k' q, real_inner_smul_left _ k' t, joy,show g=(n'.1, plaquette n'.2) from rfl, inspire]; rw [show Etch.river ψ (n'.1,n'.2) k'.val=Work.F03.faceCurl n' k from hw]
  exact integral_congr_ae (Eventually.of_forall hp)

#print axioms hueCost_collect
end finite
section collected
variable (P' : Spine)
open Vale Onyx
open YM.Stationary (Gaia)
local notation "Γ" => P'.run
local notation "Λ" => P'.par
variable {f :ℕ→ℕ} {β : ℕ →ℝ}{A : ℝ} (z : Pooling P'.run (takenVolume P') (takenCutoff P') f β)
  (p:0<A)
local notation "Iξ" => takenVolume P'
local notation "Kξ" => takenCutoff P'

def wakeG (y : I→ Gaia) (F:I→ PlaqAxes) : Chart (loomG I) := fun i j=>
  (sch (G:=SU.group) i.2 j.2 : ℂ)*specter (F i.1) (F j.1) (y i.1-y j.1)

def offerG (A:ℝ)(s n:ℕ)(β:ℕ→ℝ) (W:I→Staff) :=
  hueCost P'.run s (takenVolume P' n) (takenCutoff P' n) W (κFix β s) (glow P'.par A s)
include z p
omit [Fintype I] in
lemma reachingG {W : ℕ→I→Staff}(i' j':loomG I) {y:I→ Gaia}{F:I→PlaqAxes}
   (t : ∀ m,Tendsto (fun n=> riseX (sPow P'.par n A) (W n m).face.1) atTop (𝓝 (y m)))
   (hf : ∀ n m, (W n m).face.2 = F m) (h : y i'.1≠y j'.1) :
    Tendsto (fun c : ℕ × ℕ => offerG P' A c.1 (f c.2) β (W c.1) i' j') successive
      (𝓝 (wakeG y F i' j')) := by
  let a := fun n=> W n i'.1; let b:= fun n=> W n j'.1; let g(κ):= sPow P'.par κ A
  have hv := gauge_fee P' p z.up (W:=a) (V:=b) (fun s => hf s i'.1) (fun s => hf s j'.1)
    (((t i'.1).sub (t j'.1)).congr (fun n=> rise_sub (g n) _ _)) (sub_ne_zero.mpr h)
  have v:= reachesSucc P' β z
  let c:ℂ:= sch (G:=SU.group) i'.2 j'.2
  let C:ℂ:= Fintype.card SU.group.ColorIndex
  haveI:Nontrivial SU.group.Color:=Thera.yet_one.nontrivial_color
  have ht:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
  have hC:C≠0:= by unfold C; change (↑(Fintype.card (Fin SU.group.lieDim)):ℂ)≠0; rw [Fintype.card_fin]; exact Nat.cast_ne_zero.mpr ht.ne'
  let w :ℂ:=specter (F i'.1) (F j'.1) (y i'.1-y j'.1)
  have ht:= ((hv.mul (v.pow 2)).const_mul (c/C))
  rw [one_pow,mul_one,show c/C*speckleV (F i'.1) (F j'.1) group _=c*w from ?_] at ht
  · refine ht.congr fun n=>?_ ; unfold gaugeAt gaugeCoupon
    let x:= faceBody (a n.1) (matterSide P' n.1 (f n.2)); let Y:=faceBody (b n.1) (matterSide P' n.1 (f n.2)); let M:= (P'.par.V.L.H ((Γ).uv (takenCutoff P' (f n.2))-n.1)); let S:= rimble _ M x Y
    let l:=reachCost Γ n.1 (takenVolume P' (f n.2)) (takenCutoff P' (f n.2)) (κFix β n.1); change c/C* ( (g n.1:ℂ)^4 * (C*S)*(l:ℂ)^2)= (((↑((g n.1)^2):ℂ)*(l:ℂ))^2*c*S); push_cast; field_simp
  change c/C*(C*w)=_; field_simp
#print axioms reachingG
end collected
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.LoomForce.Palette
