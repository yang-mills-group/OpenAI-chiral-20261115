import YM.SU5.Assay.SleeveSplice
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
local notation "m"=> P.period
local notation "h₀"=> P.cutoff
local notation "ℓ" r:max l:max=> legacy Y (m r) (h₀ l)
local notation "N" r:max=> (momentm Y (m r) s)
local notation "B" D:max=> bay K D true
variable(P s)
/-- The finite volume, finite UV horizon election-terminal reader at this
 observation height. -/
def sterling (r l:ℕ)(f:P.Test):ℂ:=Journey.sharp Y H s (m r) (h₀ l) f.val
local notation "A"=> P.sterling s
/-- The financial and license gates on a course. -/
structure Shows (Z:Finset Cover)(r l:ℕ):Prop where
 legacy: ℓ r l
 tickets: Ferry Y s (m r) (h₀ l)
 scale: (((P.run.voyage (m r)).X (P.run.uv (h₀ l))).gram 0).beta=P.par.x
 local_lic: Tivoli Z ((K).c (N r))
/-- Include arbitrarily late cutoffs. -/
lemma in_cone (r:ℕ):∀ᶠ l in atTop, ℓ r l:=
 ((Y).uv_grows.comp (V).pick.grow_k).tendsto_atTop.eventually_ge_atTop _
lemma balcony_gates(Z:Finset Cover){e:ℝ}(p:0<e):∀ᶠ r in atTop, ∀ l,ℓ r l →
    P.Shows s Z r l ∧ ∀f∈B Z,∀d:ℝ,pay f.val d → ‖A r l f-P.E s f.val‖≤e*d:=by
 filter_upwards [(boutique Y H V Z s).2 e p, floor_pays Y H V s,
  (V).pick.grow_i.tendsto_atTop.eventually (turning Y H s Z)] with r u v t l h
 refine ⟨⟨h,v _ h,(coupling_clock Y _ _ (v _ h).depth).1,t⟩,?_⟩
 intro f F d D; exact (u f.val F (N r) t.hosp d (D _)).2 _ h
variable {P s}{k:ℤ}{Z U D:Finset Cover}{x:P.Spectrum0 j}{a n:ℕ}{d δ:ℝ}
local notation "Q"=> P.viewFrom j a n w k f
local notation "E"=> P.E s
local notation "W"=> P.singleState j s x
variable (s) in
lemma Balcony.leads(p:P.Balcony j k w Z a n f U D d){e:ℝ}(t:0<e):
 ∀ᶠ r in atTop,∀ l,ℓ r l→ P.Shows s (U∪Z∪D) r l ∧
    ∀g∈B Z,∀y:ℝ,pay g.val y→‖A r l (Q g)-E (Q g).val‖≤e*y:=by
 have u:=p.positive
 filter_upwards [P.balcony_gates s (U∪Z∪D) (div_pos t (mul_pos u u))] with r h l hc
 obtain ⟨p₁,h⟩:=h l hc
 refine ⟨p₁,?_⟩
 intro g q y v
 refine (h _ (p.budget q) _ (p.funding v)).trans_eq ?_;field_simp
lemma WitnessSleeve.stairs (p:P.WitnessSleeve j s x k w Z n δ a f)(q:P.Balcony j k w Z a n f U D d) {e:ℝ}(t:0<e):
 ∀ᶠ r in atTop,∀ l,ℓ r l→ P.Shows s (U∪Z∪D) r l ∧
    ‖A r l (Q 1)-1‖≤e ∧ ∀g∈B Z,∀y:ℝ,pay g.val y→ ‖A r l (Q g)-W g‖≤(δ+e)*y:=by
 filter_upwards [q.leads s t] with r h l hc
 obtain ⟨p₁,h⟩:=h _ hc
 refine ⟨p₁,?_,?_⟩
 · have u:pay (1:P.Test).val 1:=fun i x=> (norm_one : ‖(1:Fock.FC (Single ((K).c i)))‖=1).le
   have h:= h 1 ((B Z).one_mem) 1 u
   rwa [p.unit,mul_one] at h
 intro g a' y u
 rw [add_comm δ,add_mul]
 exact (norm_sub_le_norm_sub_add_norm_sub ..).trans (add_le_add (h g a' y u) (p.conserve g a' y u))
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
