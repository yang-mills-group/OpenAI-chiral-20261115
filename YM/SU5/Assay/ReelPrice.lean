import YM.SU5.Assay.Kiln
import YM.SU5.Assay.JointDelta
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
local notation "σ"=>P.rawSlot j x
local notation "β"=>P.base j x
local notation "κ"=>P.coffee j x
local notation "𝔤"=>P.Grips j x
local notation "ξ"=>P.prepared
local notation "μ"=>P.singleState j
local notation "⟪" T "⟫"=>inner ℂ Ω ((T:Y) Ω)
open Glaze
/-!
 Deliver the Reels' cost to actual calendar, all active grid heights,
 on any frames, specifically any parameter x:P.Spectrum0 j (so singleState
 readings unchanged on passing from x to P.advocate i y j if that is x).
 Shake estimate absorbs fixed exponentials but comparison requires paying
 **both** marks on the same frames (mixed pays for owner).

 `actOne`, `actTwo` use engraving height s directly (through Glaze).
-/
local notation "ι"=>P.walk j
def actOne (A:P.Glaze)(m:Bool)(F:SampleDose)(s t:ℕ):ℂ:=μ t x (ξ t (ι m (A.apron s)) F)
def actTwo (A:P.Glaze)(m:Bool)(F:SampleDose)(C:P.Glaze)(n:Bool)(G:SampleDose)(s t:ℕ):ℂ:=
 μ t x (ξ t (ι m (A.apron s)) F* ξ t (ι n (C.apron s)) G)
variable {P j x}{F G:SampleDose}{a b c:ℝ}{s t:ℕ}
lemma Walled.walk {D:P.Apron}(h:Walled j F a b (D.realWidth P j))(m:Bool):Walled j F a b ((ι m D).realWidth P j):=by
 rw [P.walk_width];exact h
lemma Walled.grow {A C:P.Glaze}(p:A.w ≤ C.w)(h:Walled j F a b (P.tock s C.w)):
 Walled j F a b (P.tock s A.w):=h.currency ((P.tock_le s ..).mpr (Int.ofNat_le.mpr p))
-- The unused wall parameters **only premises** of enrollment here
local notation "γ"=>P.actOne j x
local notation "Δ"=>P.actTwo j x
lemma walk_height (m:Bool)(D:P.Apron):(ι m D).s=D.s:=by cases m <;> rfl
variable (m n:Bool)
lemma actOne_price (A:P.Glaze)(h:Walled j F a b (P.tock s A.w))(v:s ≤ t):γ A m F s t= inner ℂ (Vac) (σ t (ι m (A.apron s)) a b F (Vac)):=by
 have e: (ι m (A.apron s)).s ≤ t:= (P.walk_height _ _).trans_le v
 exact (P.priced_rawSlot _ _ _ _ e (Walled.walk (D:=A.apron s) h m)).symm
lemma actTwo_price (A C:P.Glaze)(h:Walled j F a b (P.tock s A.w))(q:Walled j G b c (P.tock s C.w))(v:s ≤ t):Δ A m F C n G s t= inner ℂ (Vac) ((σ t (ι m (A.apron s)) a b F*σ t (ι n (C.apron s)) b c G) (Vac)):= by
 have e: (ι m (A.apron s)).s ≤ t:= (P.walk_height _ _).trans_le v
 have i: (ι n (C.apron s)).s ≤ t:= (P.walk_height _ _).trans_le v
 exact (P.priced_pair _ _ _ _ _ e i (Walled.walk (D:=A.apron s) h m) (Walled.walk (D:=C.apron s) q n)).symm

variable {A C:ℕ→P.Glaze}{Z Z':Ballad.Lead.Clan}(r:P.Reel j Z)(l:P.Reel j Z')
lemma Reel.wrap_larger (s:ℕ): (A s).w ≤ (r.wrapMix A s).w:=by rw [r.wrap_span];exact Nat.le_add_right ..
lemma Reel.first_claim (F:SampleDose)(h:Grows j A):∃d,Tapers d∧∀m x a b s t,s ≤ t→Walled j F a b (P.tock s (r.wrapMix A s).w)→
 ‖P.actOne j x (r.wrapMix A s) m F s t- P.actOne j x (A s) m F s t‖≤d s:=by
 obtain ⟨d,v,i⟩:=r.negligible F h
 refine ⟨_,v,fun m x a b s t c p=>?_⟩
 have q:=Walled.grow (Reel.wrap_larger r (A:=A) s) p
 rw [actOne_price m _ p c,actOne_price m _ q c]
 exact (P.vacant_diff j x _ _).trans (i _ _ x p)
lemma Reel.both_claim (F G:SampleDose)(h:Grows j A)(q:Grows j C):∃d,Tapers d∧∀m n x a b c s t,s ≤ t→Walled j F a b (P.tock s (r.wrapMix A s).w)→ Walled j G b c (P.tock s (l.wrapMix C s).w)→
 ‖P.actTwo j x (r.wrapMix A s) m F (l.wrapMix C s) n G s t- P.actTwo j x (A s) m F (C s) n G s t‖≤d s:=by
 obtain ⟨d,v,i⟩:=joint_negligible r l F G h q
 refine ⟨_,v,fun m n x a b c s t g p w=>?_⟩
 have a':=Walled.grow (Reel.wrap_larger r (A:=A) s) p
 have b':=Walled.grow (Reel.wrap_larger l (A:=C) s) w
 rw [actTwo_price m n _ _ p w g,actTwo_price m n _ _ a' b' g]
 exact (P.vacant_diff j x _ _).trans (i _ _ _ x p w)

-- CP consequence for holders, needs no RawNormal, also BSOT+Kiln.
lemma Reel.delivers {M:P.LagOp j x}(g:Grows j A)(h:P.Kiln j x (serial A) M):P.Kiln j x (serial (r.wrapMix A)) M:=by
 refine ⟨h.gridded,r.refine_normal _ g h.normal,?_⟩
 intro F a b p
 have v:Tendsto (Prod.fst:ℕ×ℕ→ℕ) atTop atTop:=by rw [←prod_atTop_atTop_eq]; exact tendsto_fst
 exact Reel.wrap_rehearses r (m:=false) (Tiny.ofFade h.normal.fades) g p v (t:=Prod.snd) (h.pressed F a b p)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
