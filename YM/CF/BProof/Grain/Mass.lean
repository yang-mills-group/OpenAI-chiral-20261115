import YM.CF.BProof.Grain.Pole
import YM.CF.Reed.Uinta
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Footprint Jade Py
open YM.CF.Floral Ione Haro Beau Oise Larch Lilt Vow
open scoped YM.CF.Mew
namespace Grain
open Bake Cupboard Cupboard.BasisSt Sour Tap Glyph Digit BondL Axial
open scoped YM.CF.Sour.Axial
variable {R:Patch} (P_:BudgetPoint){x:ℝ}(F G D H:ℝ→ℝ)(h A a b c d:ℝ)
local notation "Pz"=>hall_P P_ -- .B vs .radius
local notation "cnt" => cQ
variable (n k:ℕ)(q w:ℝ) {J:ℕ}
local notation "Λ"=> (R.L.val:ℝ)
abbrev CprepD (n k:ℕ)(Pav a hQ:ℝ):=8*(|ray_T n k Pav a hQ 1|+1)
lemma CprepD_pos : 0 < CprepD n k a b q:=by unfold CprepD; positivity
lemma covers (v:1≤h)(t:0 < a)(hg:sizeK R.L 2 G)(hf:Litt R 2 F)(hv:Litt R 2 H)(p:∀ᶠ x in atTop, dleaf R.L x≤ G x):∀ᶠ x in atTop, let s:= CprepD n k A w q/Λ; beam_U n k R G F (fun x=>2*H x) A w b a q h h x ≤ s* G x/8 ∧ reserveT n k (radiusB x) 1*(6*H x)≤ s/2*dleaf R.L x:=by
 obtain ⟨_,E,e,u⟩:=rise_Χ R n k G F (fun x=>2*H x) A w b a q h h v t hg hf (hv.scale_l _); let Z:= CprepD n k A w q; let f:= fun x=>reserveT n k (radiusB x) 1*(6*H x); let L:=Λ; have hz:0< Z:= CprepD_pos A w n k q -- order
 have tf: Litt R 2 f:=SupportP.beam_v (Nor.vale_u ..) (hv.scale_l _); have ht:0<L := by unfold L; positivity
 filter_upwards [u,p,tenor_Q (1/L) E e (by positivity),tenor_Q (Z/L/2) f tf (div_pos (div_pos hz ht) (by norm_num)),spice_R (R:=R),eventually_gt_atTop (0:ℝ)] with x u p h kf i t
 have he:0 < G x:= lt_of_lt_of_le (mul_pos i.2.2 (Work.E09.temp_pos t)) p; refine ⟨(u he.le).trans ?_,kf⟩
 let W:= ray_T n k A w q 1; change ray_T n k A w q (1/L*G x)+E x ≤ _; rw [show ray_T n k A w q (1/L*G x)=W*(1/L*G x) from by unfold W ray_T; ring]
 exact (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self W) (by positivity)) (h.trans (mul_le_mul_of_nonneg_left p (by positivity)))).trans_eq (show |W| *(1/L*G x)+(1/L*G x) = 8*(|W|+1)/L*G x/8 from by ring)
variable {t' Aχ Γχ zσ s:ℝ}{B:Side}{L:ChartRatio SU.group}{K:Teller SU.group}{V:Grace K R L}{U:Grasp V.U B Aχ}{W:GivenX V U}{q':Chi}
variable (c':Chamber V U W x k n h q' t')
open Prism
private lemma payHom (x d:ℝ): way_Q R k n x (d*b) q w A h=d*way_Q R k n x b q w A h:=by unfold way_Q; ring
lemma earn (m:Digit.Cash P_) (hu:0 < d)(t:0 < s)(p:s ≤ c'.δ/4)(u:c'.Rm w ≤ d*c'.δ / 8)(v:reserveT n k (radiusB x) 1*(6*c'.Lp)≤ d/2*s)(l:c'.HS≤ m.sh/10)(g:c'.LK≤ m.sf/10) : Tote c' P_ w m (d*c'.δ) (d*s) s (pack_Q k*c'.ym w+ (|c'.Lv|+3*|c'.Lp|)):=by
 let q:=reserveT n k (radiusB x) 1; have hw:0≤wren_K k n:=add_nonneg zero_le_one (lucre k n); have hy:0≤ rise_K k n w:=by unfold rise_K mark_Q composeCost; positivity
 let L:=q*(6*c'.Lp); change L ≤ _ at v; let φ(x:ℝ):= 4*x/c'.δ; let T (x y:ℝ):=wren_K k n*(φ x * c'.Φ false+rise_K k n w * c'.θ x)+q*(6*y*c'.Lp); have hp:=c'.ful
 have hs(x:ℝ)(p':0<x) : T x (φ x) ≤ φ x * (d*c'.δ/8):=by
    have he:0 < φ x:=by unfold φ; positivity
    have h0(x y:ℝ)(u:0≤x): c'.θ (x*y)=x*c'.θ y:=by unfold Chamber.θ; rw [payHom (d:=x), abs_mul,abs_of_nonneg u]
    have h1:c'.θ x≤ φ x*c'.θ c'.δ:=by
       have hx:x/c'.δ*c'.δ=x:=div_mul_cancel₀ _ hp.ne'; rw [←hx,h0 _ _ (by positivity),hx]; unfold φ; have hu:0 ≤ c'.θ c'.δ:=abs_nonneg _; gcongr; linarith -- tune
    unfold T; exact (add_le_add_left (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left h1 hy) _) hw) _).trans (le_trans (le_of_eq (show _= φ x*c'.Rm w from by unfold Chamber.Rm q; ring)) (mul_le_mul_of_nonneg_left u he.le))
 have hm:c'.Rm w≤ d*c'.δ:=by have h:=mul_pos hu hp; linarith only [h,u]
 refine ⟨p,t,hm,?_,?_,l,g,?_,?_⟩
 · let C:=φ s; have hz:T s 1=T s C+(1-C)*L:=by unfold T L; ring
   have hc:0≤ C:=by unfold C φ; positivity
   have hl: C ≤1:=by unfold C φ; apply (div_le_one hp).mpr; linarith
   have hq: T s C ≤ d/2*s:=(hs s t).trans_eq (by unfold φ; field_simp; ring)
   have hc': (1-C)*L ≤ d/2*s:= (mul_le_mul_of_nonneg_left v (by linarith : 0≤1-C)).trans (mul_le_of_le_one_left (by positivity) (by linarith))
   rw [show 6*c'.Lp=6*1*c'.Lp from by ring]; change T s 1 ≤ _; rw [hz]; linarith only [hc',hq]
 · intro z t' l' ε; change T z (φ z)≤ _; exact (hs z t').trans (show φ z * (d*c'.δ/8) ≤ φ z * _ from mul_le_mul_of_nonneg_left (by have h:=mul_pos hu hp; linarith) (by unfold φ; positivity))
 · unfold Chamber.Km; linarith only [le_abs_self c'.Lv,le_abs_self c'.Lp]
 linarith only [abs_nonneg c'.Lv,abs_nonneg c'.Lp,le_abs_self c'.Lp]
end Grain
end YM.CF.Py
