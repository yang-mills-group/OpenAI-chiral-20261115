import YM.SU5.Assay.EngineAxle
import YM.SU5.Assay.RawNormal
import YM.SU5.Assay.Breath
import YM.SU5.Assay.WrapMix
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-! Raw mark transfers. -/
variable {P j}{g:ℕ→P.VMark}{p:Vantage}{T:P.RawLag j x}{a b:ℝ}
local notation "β"=> P.rawBase j x
local notation "τ"=> P.tock

namespace Glaze
lemma rawBase_tile_pay (A:P.Glaze)(s:ℕ)(a b:ℝ): ‖β (A.apron s) a b‖≤ ‖A.tile j s‖:=(P.rawBase_pay ..).trans (P.engine_pay ..)
end Glaze

namespace Reel
variable {Z:Ballad.Lead.Clan}(r:P.Reel j Z)(A:P.Glaze)(s m:ℕ)
local notation "D"=> r.dusk A m
local notation "C"=> r.twist A m
lemma rawBase_splice (u:τ s (D).w≤a)(v:τ s (D).w≤b):
 β ((C).apron s) a b= β (A.apron s) a b- β ((D).apron s) a b:=by
 have l:(A.apron s).u j ≤ (D).w:=by change A.w≤_;rw [dusk_span];omega
 rw [P.rawBase_engineAxle _ _ ((C).apron s), P.rawBase_engineAxle _ _ ((D).apron s)]
 have p: P.Focused j (D).w (D).F:=⟨(D).centers j,(D).color⟩
 exact (engineAxle_sub x s (Focused.widen x l) p _ _).trans
   (congrArg (· - P.engineAxle j x s (D).w (D).F a b) (engineAxle_widen x s rfl l u v))
lemma twist_due (u:τ s (D).w≤a)(v:τ s (D).w≤b):
 ‖β ((C).apron s) a b- β (A.apron s) a b‖≤ ‖(D).tile j s‖:=by
 let t:= β (A.apron s) a b; let y:=β ((D).apron s) a b
 have ht:t-y-t= -y:=by abel
 rw [r.rawBase_splice x A s m u v, ht, norm_neg]
 exact Glaze.rawBase_tile_pay ..
lemma twist_norm :∀ᶠ n:ℕ in atTop,∀g:P.Glaze,∀k:ℕ,
  ∀l≥τ n (r.twist g k).w,∀y≥τ n (r.twist g k).w,
  ∀ x:P.Spectrum0 j,‖P.rawBase j x ((r.twist g k).apron n) l y-P.rawBase j x (g.apron n) l y‖≤ ‖g.tile j n‖*r.c^k:=
 r.history.mono fun n e g k _ v _ t x=> (r.twist_due x g n k v t).trans (e g k)
open Glaze in
lemma refine_raw {G:ℕ→P.Glaze}(h:Glaze.Grows j G)(w:P.RawNormal j x (serial G) g p T):
 P.RawNormal j x (serial (r.wrapMix G)) g p T:=by
 let t:=r.stays_tiny (Tiny.ofFade w.fades)
 refine w.viaDiff t.fades (r.shadow_vanish h) (fun a u b v=>?_)
 exact ((t.early u).and (t.early v)).mono fun s z=> r.twist_due x (G s) s (ply s) z.1 z.2
end Reel
variable (P j)

def rawUnit (l r:ℝ):X:=(U).wax (l+r)
local notation "ζ"=>P.rawUnit j x
lemma respool_unit (p:Vantage):P.respool j x p (ζ)=P.unitLag j x:=by
 funext a b;unfold respool rawUnit unitLag
 rw [P.reprise_wax]
 unfold locate;rw [P.cart_wax,mul_assoc,P.cart_splice,add_neg_cancel,P.cart_null,mul_one]
lemma unit_rawBase (A:P.Apron)(h:A.F=1)(l r:ℝ)(v:A.realWidth P j≤l)(t:A.realWidth P j≤r):
 P.rawBase j x A l r= ζ l r:=by
 let q:= A.realWidth P j
 have p:0≤q:= (A.real_width_pos P j).le
 unfold rawBase hang sand
 rw [P.engine_seen,h,map_one,P.seenBox_unit j x _ (add_pos (A.pos j) (A.pos j)),Nat.cast_add,P.tock_add]
 change (U).wax (l-q)*(U).wax (q+q)*(U).wax (r-q)=(U).wax (l+r)
 have he:=sub_nonneg.mpr v; have ht:=sub_nonneg.mpr t; change 0≤l-q at he
 rw [wax_sq (U) he (by linarith),wax_sq (U) (by linarith) ht,
   show l-q+(q+q)+(r-q)=l+r by abel]
lemma rawOther_unit:P.rawOther j x (ζ)=ζ:=by funext a b;unfold rawOther rawUnit;rw [wax_symm,add_comm]
lemma rawUnit_normal {D:ℕ→P.Apron}(h:P.Fades D)(q:∀s,(D s).F=1)(u:Tendsto (P.laysM ∘ g) atTop (𝓝 p)):P.RawNormal j x D g p (ζ):=by
 refine ⟨h,u,fun a v b y=>?_⟩
 refine (tendsto_const_nhds (x:=ζ a b)).congr' ?_
 filter_upwards [h.one v j,h.one y j] with s v' y'
 change _=P.charter _ _ _ (P.rawBase ..)
 rw [P.unit_rawBase j x _ (q s) _ _ v'.le y'.le];unfold rawUnit;rw [P.charter_wax]
lemma breath_raw:P.RawNormal j x (Glaze.serial P.breathes) (fun _=>0) 0 (ζ):=
 P.rawUnit_normal j x P.breath_small.fades (fun _=>rfl) tendsto_const_nhds
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
