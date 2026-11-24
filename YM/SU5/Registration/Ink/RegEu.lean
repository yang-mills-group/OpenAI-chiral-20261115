import YM.SU5.Registration.Ink.Closet

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 700000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open SatinRegistration
-- Seld valise etc.
open scoped CF.Buffered.Afterglow.Hierarchy.Seld
variable (P : Spine) (x : P.Spectrum0 3)
local notation "ξ" => P.advocate 3 x 3
local notation "H" => P.ManyF 3 ξ
local notation "S" => P.seasons 3 ξ
local notation "D" => radial (P.seasons 3 ξ)
local notation "G" => bands (P.seasons 3 ξ)
local notation "Ω" => P.vacuumEntry x
local notation "ζ" => P.heaven 3 ξ
local notation "κ" => Lead.Clan
open Swatch SatinWFixed
open _root_.YM.Boundary.Probe

open _root_.YM.SatinWFixed Carton
open Seld (optx)
open Seld.Poin (Each Film Rail dress pitch Film_step twists)
section prices
-- All Strict-Time questions on this module reference. Even if not all components of these stamps at SAME height.
variable {J:Type*} {V₀:Type*}[AddCommGroup V₀][Module ℂ V₀]
variable (B: Carton (P.seasons 3 (P.advocate 3 x 3)) V₀)
variable {n:ℕ}(R:InkWaves V₀)(W:WView V₀)(p:InkPort B R W)
open Aria Casting
local notation "L"=> Each n
abbrev qua (q:Points n)(i:Fin n): Vantage:= (q i).ofLp
abbrev flightTimes (q:Points n)(i:Fin n):= YM.time (q i)
abbrev mon (q:Points n)(h : ℝ) := place (Boundary.trace q) (fun _=>h) -- name check local
noncomputable abbrev axisSweep (R:InkWaves V₀)(v:Fin n→V₀)(q:Points n):ℂ:= R.restricted v (flightTimes q) (mon q 0)
private lemma map_head (q:Points n)(i:Fin n): polarBase (qua q i)= mon q 0 i:= rfl
private lemma polar_neg (v:Vantage) : polarBase (-v)= -polarBase v:= by
 apply Mink.ext_by <;> simp [polarBase, Cheer.shore, spacePart,spatial, YM.position, YM.time]; try rfl
private lemma cane_r (q:Points n)(i:Fin n)(A:(H).Op): optx (S) A (mon q 0 i) = P.cane x 3 A (qua q i):=by
 have he(u:Vantage): P.cartage 3 ξ u=Seld.M (S) (polarBase u):=(P.cart_plank x u).symm
 unfold optx cane; rw [he,he,polar_neg,map_head]
-- Modify telescope. use clip * inner. conditions for adjacent cuts only.
private lemma convertCons {I':Type*}(A X Y:I'→(H).Op) (C:I'→I'→(H).Op) (v:(H).space) (U:∀ i,Y i v=v) (i:I') (w:List I') (u:∀ j k c l,i::w=c++j::k::l→ C j k= Y j*X k):
 (( (i::w).map fun j=> X j * A j * Y j).prod) v=X i (Film A C (i::w) v):=by
 induction w generalizing i with
 | nil=> simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Seld.Poin.solitary]; change X i (A i (Y i v))=_; rw [U]
 | cons j l h=>
   simp only [List.map_cons,List.prod_cons]; -- expands BOTH A and Y; rest use convert `change`
   change X i (A i (Y i ((( (j::l).map (fun j=> X j * A j * Y j)).prod) v)))=
    X i (A i (C i j (Film A C (j::l) v)))
   rw [h j (fun j' k c d p=> u j' k (i::c) d (by rw [List.cons_append, p])), u i j [] l rfl]; rfl
private lemma convertAll {I':Type*}(A X Y:I'→(H).Op) (C:I'→I'→(H).Op) (v:(H).space)(U:∀ i,Y i v=v)(h:∀ i (y:H),inner ℂ v (X i y)=inner ℂ v y)(l:List I')(u:∀ i j c d,l=c++i::j::d→ C i j=Y i*X j) :
 inner ℂ v (((l.map fun j=> X j * A j * Y j).prod) v)= inner ℂ v ((Film A C l) v):=by
 cases l with
 | nil=> rfl
 | cons i l=> rw [convertCons P x A X Y C v U i l u,h]
private lemma glyph_clk (q:Points n)(t:flightTimes q ∈ east n) : Spine.LightsCross 3 (Each n) (qua q) := (List.pairwise_lt_finRange n).imp (fun i=> t i)
variable (v:Fin n→V₀) (q:Points n)
local notation "B!"=> (fun (i:Fin n) (s:ℝ≥0)=> B.bar s (v i))
-- field B over X; holds even at arbitrary cuts, not hence changing rotation order.
include p
lemma cut_wick (x0:B.omega= ζ) (t:flightTimes q ∈ east n) (f g:Fin n→ℝ)(u:Dressing 3 (Each n) (qua q) f g) :
 P.ChartPrice x 3 (Each n) (fun i s=> B.bar s (v i)) (qua q) f g= axisSweep R v q:=by
 let y:= flightTimes q; let F(i):= (y i-f i).toNNReal; let Tm(i):= (g i-y i).toNNReal; let Tk:= (S).E;
 have h₁(i:Fin n):0<F i:= Real.toNNReal_pos.mpr (sub_pos.mpr (u.1 i (List.mem_finRange _)).1)
 have h₂(i:Fin n):0<Tm i:= Real.toNNReal_pos.mpr (sub_pos.mpr (u.1 i (List.mem_finRange _)).2)
 obtain ⟨r, hr⟩ : ∃ r:ℝ≥0, Small.enough y r:= by
    have he: Boundary.shift (0:Points n) y ∈ strict n:=by simpa using on_profile (0:Points n) y 1 zero_lt_one t
    obtain ⟨r,h⟩:=Work.C03.exists_lit he; refine ⟨r,?_⟩; simpa [Small.lit, Boundary.shift] using h
 let ρ:= 𝓝[>] (0:ℝ≥0); have hρ:ρ.NeBot:=inferInstanceAs (𝓝[>] (0:ℝ≥0)).NeBot
 have hh:∀ᶠ s in ρ, 0<s ∧ s≤r ∧ ∀ i,s ≤ F i ∧ s≤ Tm i:=by
    refine Eventually.and self_mem_nhdsWithin (Eventually.and ((ge_mem_nhds hr.1).filter_mono nhdsWithin_le_nhds) ?_); simp only [eventually_all]; intro i; exact Eventually.and ((ge_mem_nhds (h₁ i)).filter_mono nhdsWithin_le_nhds) ((ge_mem_nhds (h₂ i)).filter_mono nhdsWithin_le_nhds)
 obtain ⟨s,hs,d,u'⟩:=hh.exists; have ts:Small.enough y s:= ⟨hs,d.trans_lt hr.2.1,fun i j k=> lt_of_le_of_lt (mul_le_mul_of_nonneg_left (show (s:ℝ) ≤ _ from d) (by norm_num : (0:ℝ)≤4)) (hr.2.2 _ _ k)⟩
 unfold axisSweep; rw [B.sees_wave p.strict_mat s v y ts (mon q 0)];
 let X(i):= Tk (F i-s); let Y(i):= Tk (Tm i - s);
 let A(i):= P.cane x 3 (B.bar s (v i)) (qua q i); let Z:= (fun i:Fin n=> B.bar s (v i)); let K(i j:Fin n):=Tk (fareGap y s i j); let Vantage_r(i) := P.orbitCut x 3 ((B!) i) (f i) (g i) (qua q i)
 change inner ℂ ζ ((((Each n).map Vantage_r).prod) ζ) = inner ℂ B.omega (Film (dress (S) Z (mon q 0)) K (Each n) B.omega)
 rw [show dress (S) Z (mon q 0)= A from funext fun i=> cane_r P x q i (Z i), show Vantage_r=(fun i=> X i * A i * Y i) from funext fun i=> P.orbitCut_precise x 3 ((B!) i) (B.coherent (v i)) (f i) (g i) (qua q i) s hs (u' i).1 (u' i).2, x0]
 apply convertAll P x A X Y K ζ (fun i=> P.heaven_hot ..) (fun i x'=> ?_) (Each n);
 · intro i j c d p;
   have he:=u.2 i j c d p; have ht:Tm i-s+(F j-s)=fareGap y s i j:=by
      have hq(s t:ℝ≥0)(h:s≤t): ((t-s:ℝ≥0):ℝ)=(t:ℝ)-(s:ℝ):=NNReal.coe_sub h
      have hg:((F j:ℝ≥0):ℝ)=y j-f j:=Real.coe_toNNReal _ (Real.toNNReal_pos.mp (h₁ j)).le; have hy:(Tm i:ℝ)=g i-y i:=Real.coe_toNNReal _ (Real.toNNReal_pos.mp (h₂ i)).le
      unfold fareGap; apply NNReal.eq;
      rw [NNReal.coe_add,hq s _ (u' i).2,hq s _ (u' j).1,hg,hy,NNReal.coe_add s,Real.coe_toNNReal]; swap
      · linarith [show (s:ℝ)≤(Tm i:ℝ) from (u' i).2,show (s:ℝ)≤(F j:ℝ) from (u' j).1]
      linarith
   exact (congrArg Tk ht.symm).trans ((S).time ..)
 change inner ℂ ζ ((S).E _ x')=_; rw [← (S).swing,P.heaven_hot]
-- actual moments over v of that carton
lemma Eu_wick (x0:B.omega= ζ)(t:flightTimes q ∈ east n) : P.EuCost x 3 (Each n) (B!) (qua q)= axisSweep R v q:=by
 classical
 let h:=glyph_clk q t; unfold EuCost; rw [dif_pos h]; exact cut_wick P x B R W p v q x0 t _ _ (sews 3 (Each n) (qua q) h).choose_spec.choose_spec
omit p
section pos
variable (Rz:InkWaves (epaulets J))(Wm:WView (epaulets J)) (Q:J→P.Swatch)(u:∀ i,(Q i).WPermit x 3) (pz:InkPort (P.store x Q u) Rz Wm)
variable (A:Fin n→ J× Bool)
local notation "W!"=> (fun i=>(P.praise x Q (A i) u).atHeat)
include Wm u pz
lemma actual_wick (t:flightTimes q ∈ east n) : P.EuCost x 3 (Each n) W! (qua q)=axisSweep Rz (pupil ∘ A) q:=by
 refine Eq.trans ?_ (P.Eu_wick x (P.store x Q u) Rz Wm pz (pupil ∘ A) q rfl t)
 rw [show (fun i s=>(P.store x Q u).bar s ((pupil ∘ A) i)) = W! from (funext fun i=>funext fun s=> P.scroll_pupil x Q u (A i) s)]
local notation "QZ"=> (fun i=>P.school Q (A i))
lemma stencil_wick (T₁:P.Ellis 3 x)(t:flightTimes q ∈ east n)(pz':StarCluster L (qua q)) {σ:ℕ→Fin n→ℕ}(h:∀ i,Tendsto (fun k=>σ k i) atTop atTop) {r:ℕ→Fin n→ Cover}{w:ℕ→ℕ}(b : ∀ i,Tendsto (fun k=> P.laysM (P.vtile (w k) (r k i))) atTop (𝓝 (qua q i))) (d:∀ᶠ k in atTop, ∀ i,((P.school Q (A i)).fieldA (σ k i)).s ≤ w k) : Tendsto (fun k=>P.singleState 3 (w k) x (P.fullVisit L QZ (σ k) (r k) (w k))) atTop (𝓝 (axisSweep Rz (pupil ∘ A) q)):=by
 rw [← actual_wick P x (q:=q) (Wm:=Wm) (u:=u) (pz:=pz) (Q:=Q) (Rz:=Rz) (A:=A) t]; exact P.full_visit_limit x 3 (Each n) (qua q) QZ _ T₁ (glyph_clk q t) pz' (fun i _=>h i) (fun i _=> b i) (d.mono (fun i pz j _=>pz j))
end pos
end prices
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.actual_wick
#print axioms Spine.stencil_wick
