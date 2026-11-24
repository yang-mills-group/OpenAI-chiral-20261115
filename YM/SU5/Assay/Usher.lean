import YM.SU5.Assay.Baluster
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
local notation "B" M:max=> bay K M true
variable {k:ℤ}{Z U D:Finset Cover}{x:P.Spectrum0 j}{a n r l:ℕ}{d δ:ℝ}
local notation "Q"=> P.viewFrom j a n w k f
local notation "E"=> P.E s
local notation "W"=> P.singleState j s x
local notation "m₀"=> P.period
local notation "h₀"=> P.cutoff

local notation "A"=>P.sterling s
private lemma adjust (c:ℝ){e:ℝ}(hc:0≤c)(he:0<e):∃t:ℝ,0<t ∧ t ≤ e ∧
 ∀{u y z:ℂ}{p:ℝ},0≤p→ ‖z‖≤c*p→ ‖u-1‖≤t→ ‖y-z‖≤t*p→ u≠0∧ ‖y/u-z‖≤e*p:=by
 let d:=min (e/(2*(1+c))) (1/4)
 have hd:0<d:= by unfold d; positivity
 have hu:2*(1+c)*d ≤e:= by rw [mul_comm,← le_div_iff₀ (by positivity:0<2*(1+c))]; apply min_le_left
 refine ⟨d,hd,by nlinarith,?_⟩
 intro u y z p hp hy q t
 have f: 1/2 < ‖u‖:=by
    have g:=norm_sub_norm_le (1:ℂ) u
    rw [norm_one,norm_sub_rev] at g
    have r:d≤1/4:=min_le_right ..
    linarith only [r,g,q]
 have h:u≠0:=norm_ne_zero_iff.mp (f.trans' (by norm_num)).ne'
 refine ⟨h,?_⟩
 rw [div_sub' h,norm_div]
 apply (div_le_iff₀ (show 0<‖u‖ by linarith)).mpr
 -- y-z*u
 calc
   _= ‖(y-z) - z*(u-1)‖ :=by congr 1; ring
   _≤ d*p+(c*p)*d:=(norm_sub_le ..).trans (by rw [norm_mul]; gcongr) -- hp etc
   _= (2*(1+c)*d*p)*(1/2):=by ring
   _ ≤ _:=by gcongr

/-- Full normalized regulator licenses even for a recalibration to
 unit viewer. No extra claims (other than the identity).
 The query itself still in exactly its own normalization. -/
structure Flight (P:Spine)(j:Axis)(s:ℕ)(x:P.Spectrum0 j)(k:ℤ)(w:ℕ)(Z:Finset Cover)(n:ℕ)(τ:ℝ)(a:ℕ)(f:P.Test)(U D:Finset Cover)(r l:ℕ)
 extends P.Shows s (U∪Z∪D) r l where
 -- oops section shadow avoid notation
 lock: P.sterling s r l (P.viewFrom j a n w k f 1)≠0
 cost:∀g∈bay P.calibration Z true,∀d:ℝ,pay g.val d→
   let Y₀:=fun t=>P.sterling s r l (P.viewFrom j a n w k f t)
   ‖Y₀ g-P.singleState j s x g‖≤τ*d ∧ ‖Y₀ g / Y₀ 1-P.singleState j s x g‖≤τ*d
lemma WitnessSleeve.depart (p:P.WitnessSleeve j s x k w Z n δ a f)(q:P.Balcony j k w Z a n f U D d){e:ℝ}(t:0<e):
 ∀ᶠ i in atTop,∀j',legacy Y (m₀ i) (h₀ j')→ P.Flight j s x k w Z n (δ+e) a f U D i j':=by
 let Z₀:=U∪Z∪D
 let C:=toll Y H s Z₀
 have d':= q.positive
 have u:C≥0:= (toll_pays Y H s Z₀).1
 obtain ⟨b₁,t',v,h⟩:=adjust (C*d*d) (by positivity) t
 have bound(g:P.Test)(y:ℝ)(z:g∈B Z)(w':pay g.val y):
    ‖E (Q g).val‖ ≤ C*d*d*y:=(E_bound Y H V s Z₀ (q.budget z) (q.funding w')).trans_eq (by change C*_=_; ring)
 filter_upwards [q.leads s t'] with i a₀ j' z
 obtain ⟨a₁,a₂⟩:=a₀ j' z
 have r:‖A i j' (Q 1)-1‖≤b₁:=by
   have o:=a₂ 1 ((B Z).one_mem) 1 (fun i v=> (norm_one : ‖(1:Fock.FC (Single ((K).c i)))‖=1).le)
   rwa [p.unit,mul_one] at o
 have hr(g:P.Test)(y:ℝ)(z:g∈B Z)(w':pay g.val y):= h (pay_nonneg w') (bound g y z w') r (a₂ g z y w')
 refine ⟨a₁,(hr 1 1 ((B Z).one_mem) (fun i v=> (norm_one : ‖(1:Fock.FC (Single ((K).c i)))‖=1).le)).1,?_⟩
 intro g u c w' Y₀
 have h':=p.conserve g u c w'
 rw [add_comm δ,add_mul]
 exact ⟨(norm_sub_le_norm_sub_add_norm_sub ..).trans (add_le_add ((a₂ g u c w').trans
   (mul_le_mul_of_nonneg_right v (pay_nonneg w'))) h'),
  (norm_sub_le_norm_sub_add_norm_sub ..).trans (add_le_add ((hr g c u w').2) h')⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
