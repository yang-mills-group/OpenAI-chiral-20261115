import YM.SatinExist.LandingX
import YM.SatinExist.Plutus
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower Py Py.Rate Py.Rate.LocalLimit Preparation Journey
variable {N P:Side}(G:Ratio N P) (j:ℕ)(hj:4≤j)(p:Odd G.count.val)(e:3≤G.count.val)
namespace Xara
open Buffered.Stent.Rhoda
variable (Q:SpaceM)(M:Male)(ho:‖Q‖≤1){w:ℕ}(b:LaurentRadius j G.count w)(w₀:2*w<N.val)
variable (V:StepData (More N) (More P))(ξ:Chi)(δ β:ℝ)(l:Loom N) (t:V.patch.Branches V.kernel SU.group)(q:0<δ)(u:2*δ<firstRadius SU.group)(hx:Measurable l)
variable (a c:Cover)(k v: Fin 3)(f f':SU.F) (n m:Fin 2)
local notation "Φ" y:max=> Advance.padded G (Satin.region y N) (clothRadius G.count w)
local notation "K" b:max z:max V:max=> byMode G j Q.val M z b V
local notation "ι" i:max f:max => basisC N a i f
section heading
variable (X:Mark N)(h:Envelope X)(U:FC (Single P)→L[ℝ]ℂ)(W:Fields P)
local notation "γ" α:max σ:max=> before G j Q.val M p ξ δ X α W (drawn l σ)
include b t p q u h hx
lemma packU (d:ℝ) (g:∀ (α:Tree.Forest (ratio G))(σ:Orbit N), ‖U (before G j Q.val M p ξ δ X α W (drawn l σ))‖≤ d) : ‖U (pushMark G V j Q.val M p ξ δ β l X W)‖≤ d:=by
 let X':= gathered G j Q.val M p ξ δ X W
 have he(v:Orbit N): ‖U (X' (drawn l v))‖≤ d:= by
    letI:Nonempty (Tree.Forest (ratio G)):= Tree.select _ p; let C:ℝ:= Fintype.card (Tree.Forest (ratio G)); have hC:0<C:=by unfold C; positivity
    unfold X' gathered avgF; rw [map_smul,map_sum, norm_smul,Real.norm_of_nonneg (inv_pos.mpr hC).le]; exact (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_pos.mpr hC).le).trans ((mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> g i v)) (inv_pos.mpr hC).le).trans_eq (by rw [sum_const,nsmul_eq_mul,card_univ]; exact inv_mul_cancel_left₀ hC.ne' d))
 let φ(v:Orbit N):= V.density β W.1 v.1; let A:= fun v:Orbit N=> φ v • X' (drawn l v); have hZ: Integrable A (city N):= Env.integrableX (Env.scale (Env.along (slice_env V β t W.1) measurable_fst) (Env.along (g:=fun x:Orbit N=>(W,drawn l x)) (env_gathered G j Q.val M p ξ δ b q u X h) (measurable_const.prodMk (drawn_m l hx)))) _
 rw [outright G V j Q.val M p ξ δ β l b hx t q u X h]; change ‖U (∫ v,A v∂city N)‖≤_; rw [← ContinuousLinearMap.integral_comp_comm _ hZ]; unfold A; simp_rw [map_smul]; have hp:= V.isKernel t β
 have hv:Integrable φ (city N):= (hp.integrable W.1).comp_fst (depot N)
 refine le_trans (norm_integral_le_of_norm_le (hv.mul_const d) (Eventually.of_forall fun v=>?_)) (le_of_eq ?_)
 · rw [norm_smul,Real.norm_of_nonneg (hp.positive ..)]; exact mul_le_mul_of_nonneg_left (he v) (hp.positive ..)
 rw [integral_mul_const,Scree.city,integral_prod _ hv]; unfold φ; simp_rw [integral_const,probReal_univ, one_smul]; rw [hp.total]; exact one_mul _ -- tune
#print axioms packU
end heading
local notation "J" b:max z:max V:max=> byMode G j Q.val M z b V
variable (A B: GemUT)
abbrev chapX (N:Side)(A:GemUT)(a:Cover)(f:SU.F): Mark N:=fun _=> Fock.remove (basisC N a (dnSpin A.2.2.1) (Bun A.1 f))*create (basisC N a (upSpin A.2.2.2) (Bun A.2.1 f))
lemma envChap{N: Side}: Envelope (chapX N A a f):= ⟨measurable_const, ‖chapX N A a f (1,1)‖,fun _=>le_rfl⟩
local notation "φ" a:max s:max t:max=> chapX N s a t
abbrev DiamondX := (2*capP*spendU^2)^2
lemma diaPlus : 0≤ DiamondX:=sq_nonneg _
section
include p
lemma chopX (β:Tree.Forest (ratio G))(W:Fields P)(X:Fields N): let Z:=middle G ξ δ β W X; let C:= basisC N a (dnSpin A.2.2.1) (Bun A.1 f); let Y:=basisC N a (upSpin A.2.2.2) (Bun A.2.1 f); before G j Q.val M p ξ δ (chapX N A a f) β W X= Fock.remove (J false Z C)*create (J true Z Y):=by
 intro z C Y
 have hp: withinM (Tset N)ᶜ C:= by unfold withinM C basisC Lifted.index; rw [map_smul, within_basis _ _ (mem_compl.mpr fun t=>dn_half A.2.2.1 ((Window.mem_Tset ..).1 t))]
 have hr: withinM (Tset N) Y:= by unfold withinM Y basisC Lifted.index; rw [map_smul, within_basis _ _ ((Window.mem_Tset ..).2 (up_half _))]
 change subF G j Q.val M p z (Fock.remove C*create Y)=_
 rw [sub_mul _ _ _ _ _ _ (fine_remove _ hp (within_univ _)) (fine_create _ hr (within_univ _)), sub_create _ _ _ _ _ _ hr,sub_remove _ _ _ _ _ _ hp]
end
variable (S U T D: Finset Cover)(I:FC (Single P) →ₗ[ℂ] ℂ)
local notation "B_" X:max W:max=>pushMark G V j Q.val M p ξ δ β l X W
variable (z:ℝ)
include hj p e ho w₀ b t q u hx
lemma braidX (g:Wing (Satin.region U P) (Satin.region D P) I z)(x:nodeC a∈ S)(y:nodeC c∈ T) (T':Φ S⊆ Satin.region U P)(D':Φ T⊆Satin.region D P)(T0:0≤z)(W W':Fields P): ‖I ((B_ (chapX N A a f) W)*(B_ (chapX N B c f') W'))‖ ≤ DiamondX*z:=by
 let Z:= B_ (φ c B f') W'
 let J₁:= LinearMap.toContinuousLinearMap (I.restrictScalars ℝ)
 let U₀:= ContinuousLinearMap.mul ℝ (FC (Single P))
 let G':= J₁.comp (U₀.flip Z)
 apply packU G j p Q M b V ξ δ β l t q u hx (X:=chapX N A a f) (envChap _ _ _) G' W (DiamondX*z) -- tune
 intro k m
 let V':= before G j Q.val M p ξ δ (chapX N A a f) k W (drawn l m)
 apply packU G j p Q M b V ξ δ β l t q u hx (X:=chapX N B c f') (envChap _ _ _) (J₁.comp (U₀ V')) W' (DiamondX*z)
 intro w d; change ‖I (V'* _)‖ ≤ _
 unfold V'; rw [chopX,chopX]; refine quadrants (Satin.region U P) (Satin.region D P) I z g _ _ _ _ T0 (ready_dn G j hj p e Q M ho b w₀ a _ f _ _ S U x T') (ready_up G j hj p e Q M ho b w₀ a _ f _ _ S U x T') (ready_dn G j hj p e Q M ho b w₀ c _ f' _ _ T D y D') (ready_up G j hj p e Q M ho b w₀ c _ f' _ _ T D y D')
#print axioms braidX
end Xara
end YM.CF.Buffered.Afterglow.Six
