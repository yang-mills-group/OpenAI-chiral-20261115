import YM.SU5.Assay.Daily
import YM.SU5.Assay.Sighting
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
variable (P j)
/-- A sleeve booked in measure charges, in absolute coordinates. -/
structure Sleeve (k:ℤ)(w:ℕ)(Z:Finset Cover):Prop where
 width: 0<w
 frame: Between K j (b*k) (b*(k+w)) Z
/-- A normalized bias, preserving the measurement support & scale query and
 *using* copies of such query calipers. It must serve ALL marks paid
 on the measurement support, including loose ones. Error scales by the
 whole valuation cost. Viewer recipe finite and guarded. -/
structure WitnessSleeve (s:ℕ)(x:P.Spectrum0 j)(k:ℤ)(w:ℕ)(Z:Finset Cover)
 (n:ℕ)(δ:ℝ)(a:ℕ)(f:P.Test) extends P.Sleeve j k w Z where
 ticket: ∃X:Finset P.Test, (∀i∈X,i∈P.inRoom (plow K j (-k) Z))∧ P.Placard j w n X a f
 ceiling: ‖μ j s a f (Ω j)‖<2
 pledge: ‖P.rinse j s w n (μ j s a f (Ω j))‖=1
 conserve: ∀g∈ bay K Z true,∀d:ℝ,pay g.val d→
    ‖P.E s (P.viewFrom j a n w k f g).val-P.singleState j s x g‖≤δ*d

variable {P j} {k:ℤ}{Z:Finset Cover} {x:P.Spectrum0 j}{a n:ℕ}{δ:ℝ}
local notation "Z₀"=> plow K j (-k) Z
local notation "B" D:max=> bay K D true
local notation "Q"=> P.viewFrom j a n w k f
local notation "R"=> P.framed j s w n
lemma Sleeve.earns (p:P.Sleeve j k w Z): Between K j 0 (b*w) Z₀:=by
 have v:=Between.relocate K j p.frame (-k)
 rwa [show ruler (K).B=b from rfl,mul_neg,neg_add_cancel,mul_add,←add_assoc,neg_add_cancel,zero_add] at v
lemma Sleeve.claim (p:P.Sleeve j k w Z)(h:g∈B Z):P.BEntry j w (σ (-k) g):=
 ⟨p.width,Z₀,P.shifts_support _ _ _ h,p.earns⟩
private lemma Sleeve.loan (p:P.Sleeve j k w Z)(_y:0<δ)(z:P.Hil j)
 (u:∀g∈ P.onShelf Z₀, ‖R g z - P.singleState j s x g‖<δ) (h:g∈B Z)(d:ℝ)(l:pay g.val d):
 ‖R (σ (-k) g) z-P.singleState j s x g‖≤δ*d:=by
 have t:=p.claim h
 have v:0≤d:= (norm_nonneg _).trans (l 1 (1,1))
 obtain (rfl|r):=v.eq_or_lt
 · have g₀:g=0:=Subtype.ext (funext fun i=> funext fun y=>norm_eq_zero.mp ((l i y).antisymm (norm_nonneg _)))
   unfold framed; rw [g₀,map_zero,map_zero,meanBox_zero _ _ _ p.width];simp
 · let c:ℂ:=(d:ℂ)⁻¹
   let i:=σ (-k) g
   have cw:‖c‖=d⁻¹:= by simp [c,abs_of_pos r]
   have l':pay i.val d:= chime_pay K j _ _ l
   have j': c•i ∈ P.onShelf Z₀:=⟨(B Z₀).smul_mem (P.shifts_support j (-k) _ h) _,fun m v=> (pay_scale l' c m v).trans_eq (by rw [cw,inv_mul_cancel₀ r.ne'])⟩
   have he:R (c•i) z=c•R i z:=by unfold framed; rw [meanBox_smul s t c,smul_apply,inner_smul_right];rfl
   have hi:=u _ j'
   rw [he,map_smul,show P.singleState j s x i=P.singleState j s x g from P.slide_single ..,←smul_sub,norm_smul,cw] at hi
   calc
    _ = d*(d⁻¹*‖R i z-P.singleState j s x g‖):=by rw [←mul_assoc,mul_inv_cancel₀ r.ne',one_mul]
    _ ≤ d*δ:=mul_le_mul_of_nonneg_left hi.le r.le
    _ = δ*d:=mul_comm ..
lemma Sleeve.witness (p:P.Sleeve j k w Z)(s:ℕ)(x:P.Spectrum0 j)(R':P.Register)(n:ℕ)(y:0<δ):
 ∃a f,P.WitnessSleeve j s x k w Z n δ a f:=by
 obtain ⟨X,h,a,f,h₁,b₁,c,v⟩:= P.reserve_daily j s w Z₀ R' p.earns p.width x n y
 refine ⟨a,f,p,⟨X,h,h₁⟩,b₁,c,?_⟩
 intro g t d u
 rw [viewFrom_mean s n h₁.earns (p.claim t)]
 exact p.loan y _ v t d u
namespace WitnessSleeve
variable(p:P.WitnessSleeve j s x k w Z n δ a f)
include p
lemma borrowed :P.BEntry j a f:= p.ticket.choose_spec.2.earns
lemma draws : f ∈ S:= p.ticket.choose_spec.2.keeps (fun i u=> (p.ticket.choose_spec.1 i u).2.1)
lemma presses_color (t:g∈S): Q g∈ S:= viewFrom_keeps n k p.draws t
lemma price (h:g∈B Z):
 P.E s (Q g).val=R (σ (-k) g) (μ j s a f (Ω j)):=
 viewFrom_mean s n p.borrowed (p.claim h)
lemma unit:P.E s (Q 1).val=1:=by
 rw [p.price ((B Z).one_mem),map_one,rinse_unit _ _ _ _ _ p.width,p.pledge];simp
lemma subsidy_zero (h:g∈B Z)(t:μ j s w (σ (-k) g)=0):P.E s (Q g).val=0:=by
 rw [p.price h];unfold framed;rw [t];simp
end WitnessSleeve
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
