import YM.SU5.Assay.Consecutive
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
private lemma thicken {X:Type*}[NormedAddCommGroup X]{D:Set X}(d:Dense D)(k:ℝ)(p:0<k)(g:ℕ→X→ℂ)
 (a:∀n x y,‖g n x-g n y‖ ≤ k*‖x-y‖)(b':∀x∈D,Tendsto (fun n=>g n x) atTop (𝓝 0))(x:X): Tendsto (fun n=>g n x) atTop (𝓝 0):=by
 refine Metric.tendsto_nhds.mpr (fun e he=>?_)
 obtain ⟨y,h,h'⟩:= Metric.mem_closure_iff.mp (d x) (e/2/k) (by positivity)
 filter_upwards [Metric.tendsto_nhds.mp (b' y h) (e/2) (by positivity)] with n hn
 rw [dist_zero_right] at hn ⊢
 rw [dist_eq_norm,lt_div_iff₀ p,mul_comm _ k] at h'
 exact (norm_le_norm_sub_add (g n x) (g n y)).trans_lt (by linarith only [h',hn,a n x y])
local notation "Δ" a:max=> (fun (k n:ℕ)(d:Trans j)=>T j (a,(k+n:ℕ),d)-T j (a,n,d))
private lemma ups {a:ℕ}(p:0<a): Tendsto (fun n=>a*n) atTop atTop:=tendsto_atTop_mono' _ (Eventually.of_forall (fun n=> Nat.le_mul_of_pos_left n p)) tendsto_id
variable (P j s)(d:Trans j)(k:ℕ)
private lemma early_only (u v:ℕ)(x:P.Vox j u)(y:P.Vox j v):
 Tendsto (fun n=>inner ℂ (P.piece j u x) ((Δ s) k n d (P.piece j v y))) atTop (𝓝 0):= by
 let t:=max s (max u v)
 have hu:u≤t:=(le_max_left ..).trans (le_max_right s _)
 have hv:v≤t:=(le_max_right ..).trans (le_max_right s _)
 have hs:s≤t:=le_max_left ..
 let q:=L^(t-s)
 obtain ⟨_,_,p,h⟩:= P.floor_range j u x
 obtain ⟨_,_,r,g⟩:= P.floor_range j v y
 rw [←h,←g,←meanBox_raise u p t hu,←meanBox_raise v r t hv]
 refine ((P.across_ask_fee j t _ _ d (p.raise u t hu) (r.raise v t hv) (q*k)).comp (ups (pow_pos (Λ).R.L.property (t-s)))).congr ?_
 intro n
 simp only [Function.comp_apply,P.slide_up j s _ t hs]
 simp only [q,castor,timeMesh,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,mul_add]
 rfl

lemma P_across (x y:P.Hil j): Tendsto (fun n=>inner ℂ x ((Δ s) k n d y)) atTop (𝓝 0):=by
 let p:=sounds Y H V (π).circuit j 0 false C₀
 have h(n): ‖(Δ s) k n d‖≤ 2:=(norm_sub_le _ _).trans ((add_le_add (show ‖T j _‖≤1 from P.grow j _) (show ‖T j _‖≤1 from P.grow j _)).trans (by norm_num))
 have i(n)(x y:P.Hil j): ‖inner ℂ x ((Δ s) k n d y)‖≤(2*‖x‖+1)*‖y‖∧‖inner ℂ x ((Δ s) k n d y)‖≤(2*‖y‖+1)*‖x‖:=by
   have hn:‖inner ℂ x ((Δ s) k n d y)‖≤‖x‖*(2*‖y‖):=by
     refine (norm_inner_le_norm x _).trans ?_
     have k₀:‖(Δ s) k n d y‖≤2*‖y‖:=(((Δ s) k n d).le_opNorm y).trans (by gcongr; exact h n)
     gcongr
   constructor <;> nlinarith only [hn,norm_nonneg x,norm_nonneg y]
 refine thicken p (2*‖x‖+1) (by positivity) (fun n y=>inner ℂ x ((Δ s) k n d y)) ?_ ?_ y
 · intro n z w; rw [←inner_sub_right,←map_sub]; exact (i ..).1
 intro y hy
 refine thicken p (2*‖y‖+1) (by positivity) (fun n x=>inner ℂ x ((Δ s) k n d y)) ?_ ?_ x
 · intro n z w; rw [←inner_sub_left]; exact (i ..).2
 obtain ⟨v,_,rfl⟩:=Set.mem_iUnion.mp hy
 intro x hx; obtain ⟨u,_,rfl⟩:=Set.mem_iUnion.mp hx
 exact P.early_only j s d k ..
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
