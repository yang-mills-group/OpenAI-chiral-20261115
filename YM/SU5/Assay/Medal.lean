import YM.SU5.Assay.Wipe
import YM.SU5.Assay.Book
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
open Ballad
/-! One literal graded tag per clan; normalization y fixed before trying on shrinking hosts. -/
variable {P j}{A:P.Glaze}{s:ℕ}{y z:ℂ}{a b:ℝ}
local notation "β"=>P.rawBase j x
local notation "τ"=>P.tock
local notation "Ϝ"=>P.engineAxle j x
local notation "μ"=>P.seenBox j x
local notation "φ"=>P.rawUnit j x
namespace Glaze
lemma soot_pay (p:τ s A.w≤a)(q:τ s A.w≤b):
 β ((A.soot y).apron s) a b=β (A.apron s) a b+ (-y)•φ a b:=by
 let D:P.Glaze:=⟨A.w,A.pos,∅,1,one_mem _,one_mem _,BFits.empty _ _⟩
 have h(f:P.Glaze):P.Focused j f.w f.F:=⟨f.centers j,f.color⟩
 have u:P.Focused j A.w ((-y)•(1:P.Test)):=⟨by rw [map_smul]; exact (D.centers j).smul _,(enclave K).smul_mem (one_mem _) _⟩
 have t:Ϝ s A.w 1 a b=φ a b:= (engineAxle_widen x s (D:=D.apron s) rfl le_rfl p q).trans (unit_rawBase P j x _ rfl _ _ p q)
 rw [P.rawBase_engineAxle,P.rawBase_engineAxle]
 exact (engineAxle_add x s (h A) u _ _).trans (congrArg (Ϝ s A.w A.F a b + ·)
    ((engineAxle_smul x s (h D) (-y) _ _).trans (congrArg ((-y)•·) t)))
lemma coat_pay (A:P.Glaze)(s:ℕ)(z:ℂ)(a b:ℝ):β ((A.coat z).apron s) a b=z• β (A.apron s) a b:=by
 rw [P.rawBase_engineAxle,P.rawBase_engineAxle];exact engineAxle_smul x s ⟨A.centers j,A.color⟩ ..
end Glaze
lemma Taste.fixed (u:P.Taste A.F A.S y)(p:0<a)(q:0<b):
 Tendsto (fun s=>β (A.apron s) a b) atTop (𝓝 (y•φ a b)):=by
 have h:= (Taste.clean x u p q).add_const (y•φ a b)
 rw [zero_add] at h;refine h.congr' ?_
 filter_upwards [P.tock_small A.w p,P.tock_small A.w q] with s v t
 rw [Glaze.soot_pay x v t,neg_smul];abel
lemma Taste.washed (u:P.Taste A.F A.S y)(v:y≠0):
   P.RawNormal j x (Glaze.serial (fun _=>A.coat y⁻¹)) (fun _=>0) 0 (φ):=by
 refine ⟨(A.coat y⁻¹).static.fades,tendsto_const_nhds,fun a p b q=>?_⟩
 simp only [P.align_zero,Glaze.serial,Glaze.coat_pay]
 have h:=(Taste.fixed x u p q).const_smul y⁻¹
 rwa [smul_smul,inv_mul_cancel₀ v,one_smul] at h

variable (P) in
structure Medal (Z:Lead.Clan) where
 n:ℕ
 width:ℕ
 y:ℂ
 gap:P.calibration.ℓ<n
 pos:0<width
 paid:P.BFits width (P.flash n).patio
 nonzero:y≠0
 worth:P.Taste (P.defaultR Z n) (P.flash n).patio y
variable {Z:Lead.Clan}
namespace Medal
lemma available {r:P.Register}{u v:ℝ}{w:Supplier}(h:uniform P r w u v)(q:Tasting.Paid P.par)(Z:Lead.Clan):Nonempty (P.Medal Z):=by
 obtain ⟨n,p,y,e,t⟩:= vividAt Z h q ((K).ℓ+1)
 obtain ⟨s,u,x⟩:= ((P.eventually_BFits (P.flash n).patio).and (eventually_ge_atTop 1)).exists
 exact ⟨n,s,y,p,x,u,e,t⟩
variable (m:P.Medal Z)
def cross:P.Glaze:=⟨m.width,m.pos,_,_,P.defaultBay Z m.n,P.defaultColor Z m.n,m.paid⟩
def bright:P.Glaze:=m.cross.coat m.y⁻¹
def shine:P.Folio:=(P.defaultFolio Z m.n).ink m.y⁻¹
lemma gained : P.RawNormal j x (Glaze.serial (fun _=>m.bright)) (fun _=>0) 0 (φ):=
 Taste.washed x (A:=m.cross) m.worth m.nonzero
lemma first (s:ℕ) :P.FirstDress (m.bright.apron s) Z.2 m.shine:=
 ⟨Submodule.smul_mem (P.Beam s (P.flash m.n).patio Z.2) m.y⁻¹ (Beam.of_sensed (P.sensedDefault s _ _ m.gap)),Wove.smul (P.flash_prices Z m.gap) m.y⁻¹⟩
lemma simultaneously {e:ℝ}(p:0<a)(q:0<b)(r:0<e):
  ∀ᶠ s in atTop,∀ j:Axis,∀x:P.Spectrum0 j,
    ‖P.rawBase j x (m.bright.apron s) a b-P.rawUnit j x a b‖<e:=by
 apply eventually_all.mpr
 intro j
 let c:=‖m.y⁻¹‖
 have t:0<c:=norm_pos_iff.mpr (inv_ne_zero m.nonzero)
 filter_upwards [Taste.clean_rate j (A:=m.cross) (div_pos r t) m.worth p q,
    P.tock_small m.cross.w p,P.tock_small m.cross.w q] with s v w u
 intro x
 have y:=(lt_div_iff₀' t).mp (v x)
 change ‖m.y⁻¹‖*_<e at y
 rw [←norm_smul,Glaze.soot_pay x w u,smul_add,←Glaze.coat_pay,neg_smul,smul_neg,smul_smul,inv_mul_cancel₀ m.nonzero,one_smul] at y
 rw [sub_eq_add_neg]
 exact y
end Medal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
