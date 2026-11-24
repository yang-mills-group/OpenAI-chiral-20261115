import YM.SU5.Assay.StencilSeat
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
private lemma pick_some {I M:Type*}[PseudoMetricSpace M](Q:I→M)(X B:Set I)
 (c:IsCompact (closure (Q '' B))) (d:(Q '' B)⊆ closure (Q '' X)){e:ℝ}(h:0<e):
 ∃Z:Finset I,(∀x∈Z,x∈X)∧∀y∈B,∃x∈Z,dist (Q y) (Q x)<e:=by
 have o:closure (Q '' B)⊆⋃ x:X,Metric.ball (Q x.val) e:=by
   intro y a
   obtain ⟨_,⟨x,b₀,rfl⟩,p⟩:= Metric.mem_closure_iff.mp ((closure_minimal d isClosed_closure) a) e h
   exact Set.mem_iUnion.mpr ⟨⟨x,b₀⟩,p⟩
 obtain ⟨v,r⟩:= c.elim_finite_subcover _ (fun _=>Metric.isOpen_ball) o
 refine ⟨v.image Subtype.val,fun x a=> (by obtain ⟨u,_,rfl⟩:=mem_image.mp a; exact u.2),?_⟩
 intro y p
 obtain ⟨x,s,t⟩:= Set.mem_iUnion₂.mp (r (subset_closure ⟨y,p,rfl⟩))
 exact ⟨_,mem_image_of_mem _ s,t⟩

variable(s)
local notation "Q"=>μ j s w
local notation "W"=>P.singleState j s
lemma ticket_payoff (x:P.Spectrum0 j)(p:P.BEntry j w f): ‖W x f‖≤‖Q f‖:=by
 rw [single_state]
 refine (NonUnitalStarAlgHom.norm_apply_le (P.chi j x) (P.reading j s f)).trans ?_ -- .. hazard:
 change ‖P.compressed j s f‖≤_
 rw [meanBox_state s p]
 exact P.shadow_bound j (Q f)
variable (P j w)(n:ℕ)
local notation "R"=>P.framed j s w n
lemma dish_small (f:P.Test)(z:P.Hil j)(h:‖z‖<2): ‖R f z‖≤4*‖Q f‖:=by
 let y:=P.guardPlate j s n z
 have e:‖y‖≤ 2:=((P.guardPlate j s n).le_opNorm z).trans ((mul_le_of_le_one_left (norm_nonneg z) (P.heat_norm j (Ν s n))).trans h.le)
 exact (norm_inner_le_norm y _).trans (calc
   _ ≤ 2*(‖Q f‖*2):=mul_le_mul e (((Q f).le_opNorm y).trans (mul_le_mul_of_nonneg_left e (norm_nonneg _))) (norm_nonneg _) zero_le_two
   _ = _:=by ring)
/-! X allowed preparation claims, B actual list (not even necessarily finite). -/
lemma approach_earns (X B:Set P.Test)(p:∀i∈X,P.BEntry j w i)(q:∀i∈B,P.BEntry j w i)
 (c:IsCompact (closure (Q '' B))) (d:(Q '' B)⊆closure (Q '' X)) (x:P.Spectrum0 j)(t:P.Register){δ:ℝ}(u:0<δ):
 ∃ (F:Finset P.Test),(∀i∈F,i∈X)∧∃ a f,P.Placard j w n F a f ∧ let z:= μ j s a f (Ω j)
    ‖z‖<2 ∧ ‖P.rinse j s w n z‖=1 ∧∀i∈B, ‖R i z - W x i‖<δ:=by
 obtain ⟨F,g,e⟩:= pick_some _ _ _ c d (e:=δ/6) (by positivity)
 obtain ⟨a,f,h,h',h'',v⟩:= P.framed_earns j s w n F (fun i l=>p i (g i l)) x t (δ/6) (by positivity)
 refine ⟨F,g,a,f,h,h',h'',?_⟩
 let z:=μ j s a f (Ω j)
 intro i l
 obtain ⟨b',m,y⟩:=e i l
 have r:=p _ (g _ m); have r':=q i l
 have o:=ticket_payoff s x (r'.sub r)
 have k:=P.dish_small j s w n (i-b') z h'
 rw [dist_eq_norm,←meanBox_sub s r' r] at y
 calc
   ‖R i z-W x i‖ = ‖(R b' z-W x b')+(R (i-b') z-W x (i-b'))‖:=by
     have t:R (i-b') z=R i z-R b' z:=by unfold framed;rw [meanBox_sub s r' r,sub_apply,inner_sub_right]
     rw [t,map_sub]; congr 1;abel
   _ ≤ ‖R b' z-W x b'‖ + (4*‖Q (i-b')‖+‖Q (i-b')‖) :=(norm_add_le ..).trans ((add_le_add le_rfl ((norm_sub_le ..).trans (add_le_add k o))))
   _ < δ:=by change ∀i∈F,‖R i z-W x i‖<_ at v;linarith only [v _ m, y]
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
