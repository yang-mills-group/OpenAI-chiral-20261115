import GaugeFieldConstruction.StencilHalos
import GaugeFieldConstruction.FancyLightL
import GaugeFieldConstruction.ChasmLightYL
import GaugeFieldConstruction.StencilContour
import GaugeFieldConstruction.AuldΘJ
/-!
# Supply the strict field-price for the Carton on those actual SAT labels, over the neutral-timeslice space
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace Discipline
open RosterJ BoonsθJ Shower SelectionAnalysis
open OS.Semigroup MacroGrid
open NSF.Boundary
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric
open _root_.YM.SatinWFixed
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ν" => P.advocate 3 x (3:Axis)
local notation "H"=> P.ColorHil 3 ν
local notation "B"=> P.ManyF 3 ν
local notation "Jγst"=> P.gnsIn 3 ν
local notation "Cγst"=> P.privateH x 3
local notation "D"=> (Cγst).DegreeHab
local notation "S"=> P.seasons 3 ν
local notation "T"=> (Cγst).BrightHab
local notation "Κ"=> (Cγst).canopy.track
local notation "μ"=> marks (timeMesh P.par)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable (R:ΧiMars→ₗ[ℂ] ScreensJ P)(A:AllocatedL P)(X:CloudsL){F:CloudsL}(W:SurfCheckL F)
variable (h:CheckΩL R) (g:∀ (v:ΧiMars) (j:Axis) (σ τ:PermWallJ P), R v j σ τ ∈ P.neutralSlabs j)
local notation "Qρυθ" => SmallRimL (P.privateH x 3) R A X W
local notation "SY" => (SurfRimL F).Union
local notation "Ζ" => projectLine P 3 x
noncomputable def StampShelf (p:ℝ≥0): SY →ₗ[ℂ] (B).Op:={ toFun v:= if 0<p then _root_.YM.OS.Semigroup.sand (S) ( (Ζ) (R (W.TinCanL.symm v) 3 (A.pad p) (A.pad p))) ((slitL A p):ℝ) ((slitL A p):ℝ) else 0, map_add' a b:=by split_ifs <;> simp [sand,Pi.add_apply,mul_add,add_mul], map_smul' a b:=by split_ifs <;> simp [sand,Pi.smul_apply,mul_smul_comm,smul_mul_assoc] }
-- use allocation coherence through *below* wall. Sovereign since each Φ is attention of actual family.
lemma attainment_tax (P:Spine)(j:Axis)(F: ScreensJ P)(h: AttainedR 0 F) (σ τ a b:PermWallJ P)(p:StallJ P σ≤ StallJ P a)(g:StallJ P τ≤ StallJ P b):
   F j a b=HeatTaxJ P j (StallJ P a-StallJ P σ) (StallJ P b-StallJ P τ) (F j σ τ):=by
 obtain ⟨u,h⟩:=h; obtain ⟨A,r,e⟩:=h j σ τ; obtain ⟨B₁,q,b₁⟩:=h j a b
 let J(x):= HeatTaxJ P j (StallJ P a-StallJ P σ) (StallJ P b-StallJ P τ) x; have hz:Continuous J:=by unfold J HeatTaxJ; fun_prop
 exact tendsto_nhds_unique_of_eventuallyEq q ((hz.tendsto _).comp r) ((b₁.and e).mono (fun i t=> t.1.same (offWallP _ _ _ _ _ _ t.2 p g))) -- tune
local notation "Λ" => StampShelf P x R A W -- omits X
local notation "Ψ" => passFrame P 3 x
lemma stamp_part (t:ℝ≥0)(v:SY)(ht:0<t) : (Λ t v) =(S).sand ((Ζ) (R (W.TinCanL.symm v) 3 (A.pad t) (A.pad t))) ((t:ℝ)-StallJ P (A.pad t)) ((t:ℝ)-StallJ P (A.pad t)):=by
 rw[← slotPayL A ht]; exact if_pos ht
include h g
lemma coin_value (v: ΧiMars) (ε:ℝ≥0) (u:0< ε) (σ:PermWallJ P)(h': StallJ P σ≤ StallJ P (A.pad ε)):
   Λ ε (W.TinCanL v)=(S).sand ((Ζ) (R v 3 σ σ)) ((ε:ℝ)-StallJ P σ) ((ε:ℝ)-StallJ P σ):=by
 let t:= (ε:ℝ); let a:= StallJ P σ; let b:=StallJ P (A.pad ε); have hx: b ≤ t:=(A.cent u).le
 rw [stamp_part _ _ _ _ _ _ _ u,W.TinCanL.symm_apply_apply, attainment_tax P 3 (R v) (h.showL v) σ σ _ _ h' h']; change (S).sand (projectPrice P 3 x (HeatTaxJ P 3 (b-a) (b-a) (R v 3 σ σ))) _ _=_
 rw [projectTax P 3 x (R v 3 σ σ) (g v 3 σ σ),(S).sand_join (sub_nonneg.mpr h') (sub_nonneg.mpr h') (sub_nonneg.mpr hx) (sub_nonneg.mpr hx)] -- hx reducible
 rw [show b-a+((ε:ℝ)-StallJ P (A.pad ε))=t-a from by change b-a+(t-b)=t-a; ring]; rfl

lemma preserves_cart: PreservesSmall S (Λ) (P.heaven 3 ν) LinearMap.id Ψ (SmallRimL (P.privateH x 3) R A X W) :=by
 refine ⟨(fun t=>frameHeat P 3 x t), (fun p=>frameSpace P 3 x _), frameHeavenL P 3 x, ?_⟩
 intro t ht v; let a:=A.pad t; let F:=R (W.TinCanL.symm v) 3 a a; let B':P.Physical 3:=⟨F,g _ 3 a a⟩; let k:= slitL A t; let Q:= P.reprise 3 ν (P.colorSpace 3 ν B')
 have hz: Λ t v= (S).E k*Q*(S).E k:=by rw [stamp_part _ _ _ _ _ _ _ ht, ←slotPayL A ht,sand,wax,Real.toNNReal_coe]; exact congrArg (fun z:(B).Op=> (S).E k*z*(S).E k) (notLoss P 3 x B') -- tune binder `local notation B.Op` invalid fix
 ext1 i; rw [hz]; change Ψ ((S).E k (Q ((S).E k i))) = (T).E k (LadderRackMars (Cγst) F ((T).E k (Ψ i))); have hc(x₁:B): Ψ ((S).E k x₁)= (T).E k (Ψ x₁):=DFunLike.congr_fun (frameHeat P 3 x k) _; rw [hc (Q ((S).E k i)),←hc i]; exact congrArg (fun x0 : (D) => ((T).E k) x0) (projected_symSt P 3 x B' ((S).E k i))
lemma stamp_coherent (v:SY): ∀ p:ℝ≥0,0<p→∀ u:ℝ≥0,Λ (p+u) v=(S).E u*(Λ p v)*(S).E u:=by
 intro t ht u; obtain ⟨v,rfl⟩:=W.TinCanL.surjective v; let a:= A.pad t; let b:=A.pad (t+u)
 have he: ∃ k:PermWallJ P, StallJ P k≤ StallJ P a∧ StallJ P k≤ StallJ P b:= by
    rcases le_total (StallJ P a) (StallJ P b) with h|h
    · exact ⟨a,le_rfl,h⟩
    exact ⟨b,h,le_rfl⟩ -- formatting fix
 obtain ⟨k,p,o⟩:=he
 have hu:0<t+u:=by positivity
 let l:=StallJ P k
 let y:=(t:ℝ)-l
 have h':0≤ y:= sub_nonneg.mpr (p.trans (A.cent ht).le)
 rw [coin_value P x R A W h g v _ ht k p,coin_value P x R A W h g v _ hu k o]; let T':=(Ζ) (R v 3 k k)
 change (S).sand T' ((t+(u:ℝ))-l) ((t+(u:ℝ))-l)= _
 rw[show (t+(u:ℝ))-l=y+u from (by unfold y; ring)]; apply Eq.trans ((S).sand_join h' h' (show 0≤(u:ℝ) from u.property) (show 0≤(u:ℝ) from u.property) T').symm; have he:(S).wax u=(S).E u:= congrArg (S).E (Real.toNNReal_coe); change (S).wax u*_*(S).wax u=_; rw[he]
variable {W':Waves (SurfRimL F)}(p:NSF.Bid.Direct (SmallRimL (P.privateH x 3) R A X W) W')
-- rate from the larger space
include p X
lemma stamp_enjoy (v:SY): ∃ (k:ℕ)(C:ℝ),0≤C∧∀ a:ℝ≥0,0<a→a≤1→ (↑a:ℝ)^k * ‖Λ a v‖≤ C:=by
 let L:= Ψ; let t:= (Qρυθ); let g'(x:ℝ≥0):= Λ x v; let u:=(Qρυθ).bar; let B₁:= ‖g' 1‖; have y(t:ℝ≥0)(u:0<t):‖g' t‖≤ ‖((Qρυθ).bar t v)‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro l; rw [← L.norm_map]; refine Eq.trans_le (congrArg norm (DFunLike.congr_fun ((preserves_cart P x R A X W h g).links t u v) l)) ?_
    change ‖((Qρυθ).bar t v) (Ψ l)‖ ≤ _; apply (((Qρυθ).bar t v).le_opNorm (Ψ l)).trans_eq; exact congrArg (‖((Qρυθ).bar t v)‖ *·) ((Ψ).norm_map _)
 obtain ⟨D0,x0,m,hp⟩:=p.linked.stature.price v
 refine ⟨x0,max D0 B₁,m.le.trans (le_max_left ..),fun a ht p'=>?_⟩; rcases eq_or_lt_of_le p' with rfl|hy; · rw [NNReal.coe_one,one_pow,one_mul]; exact le_max_right ..
 have w := y a ht |>.trans (hp a ⟨ht,hy⟩); rw [inv_pow,← div_eq_mul_inv] at w; rw [mul_comm]; exact ((le_div_iff₀ (pow_pos (show (0:ℝ)<a from ht) _)).1 w).trans (le_max_left ..)
#print axioms stamp_enjoy
#print axioms stamp_coherent
end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
