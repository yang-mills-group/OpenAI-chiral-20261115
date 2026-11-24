import YM.SU5.Assay.Crosstalk
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
variable (P j s)(d:Trans j)
local notation "D" u:max "|" k:max => T j (u,k,d)
private lemma aliases (c:ℕ)(pc:0<c)(x:P.Hil j)(p:(D s | (c:ℤ)) x=x)(k:ℕ):
 (D s |(k:ℤ)) x=x:=by
 let u:=(D s | (k:ℤ)) x-x
 have pe (n:ℕ): (D s | (c*n:ℕ)) x=x:=by
   induction n with
   | zero=> simp only [mul_zero,Nat.cast_zero,P.shift_zero]; rfl
   | succ n h=> rw [Nat.mul_succ,Nat.cast_add,←P.shift_plus,ContinuousLinearMap.mul_apply,p,h]
 have hy:Tendsto (fun n=>c*n) atTop atTop:= tendsto_atTop_mono' _ (Eventually.of_forall (fun n=>Nat.le_mul_of_pos_left n pc)) tendsto_id
 have hz:inner ℂ u u=0:=by
   refine tendsto_nhds_unique tendsto_const_nhds (((P.P_across j s d k u x).comp hy).congr ?_)
   intro n; simp only [Function.comp_apply, sub_apply] -- want cast k+c*n
   rw [Nat.cast_add,←P.shift_plus,ContinuousLinearMap.mul_apply,pe]
 exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℂ)).mp hz)
private lemma aliases_all (c:ℕ)(pc:0<c)(x:P.Hil j)(p:(D s | (c:ℤ)) x=x)(k:ℤ): (D s | k) x=x:=by
 rcases le_total 0 k with h|h
 · simpa only [Int.toNat_of_nonneg h] using P.aliases j s d c pc x p k.toNat
 have q:0≤ -k:=neg_nonneg.mpr h
 have g: (D s| (-k)) x=x:= by simpa only [Int.toNat_of_nonneg q] using P.aliases j s d c pc x p (-k).toNat
 calc
  _ = ((D s| k)*(D s| (-k))) x :=by rw [ContinuousLinearMap.mul_apply,g]
  _ = x :=by rw [P.shift_plus,add_neg_cancel,P.shift_zero]; rfl
lemma sent_up (x:P.Hil j)(p:(D s|1) x=x)(u:ℕ)(z:ℤ): (D u| z) x=x:=by
 let t:=max s u
 have h:=le_max_left s u
 rw [P.slide_up j u _ t (le_max_right ..)]
 refine P.aliases_all j t d (L^(t-s)) (pow_pos (Λ).R.L.property _) x ?_ _
 rw [P.slide_up j s _ t h] at p
 simpa only [castor,mul_one,timeMesh,Nat.cast_pow] using p
lemma fixed_frame (x:P.Hil j): x∈P.vacuum j ↔ ν j (Ν s 1) x=x ∧ ∀d:Trans j,T j (s,1,d) x=x:=by
 rw [P.ground_ok]
 exact ⟨fun h=>⟨h.1 _,fun _=>h.2 _⟩,fun h=>⟨P.warms_to_all j s x h.1,fun ⟨u,z,d⟩=>P.sent_up j s d x (h.2 d) u z⟩⟩
private lemma keepsProj {«H»:Hilbert}(N:Submodule ℂ «H»)[N.HasOrthogonalProjection]
   (g:(«H»).Op)(h:∀x∈N,g x∈N)(e:∀x∈N,(star g) x∈N)(x:«H»):
   N.starProjection (g x)=g (N.starProjection x):=by
 refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (N.starProjection_apply_mem x)) (fun w u=>?_)
 rw [←map_sub, ←ContinuousLinearMap.adjoint_inner_right]
 exact Submodule.starProjection_inner_eq_zero x _ (e w u)
private lemma symProj {«H»:Hilbert}(N:Submodule ℂ «H»)[N.HasOrthogonalProjection]:
    star N.starProjection=N.starProjection:=by
 ext1 x;apply ext_inner_right ℂ; intro y
 change inner ℂ (N.starProjection.adjoint x) y=_
 rw [ContinuousLinearMap.adjoint_inner_left,Submodule.inner_starProjection_left_eq_right]

lemma frame_project (N:Submodule ℂ (P.Hil j))[N.HasOrthogonalProjection]
 (h:∀x∈N,ν j (Ν s 1) x∈N)(e:∀d:Trans j,∀k:ℤ,∀x∈N,T j (s,k,d) x∈N) {x:P.Hil j}(p:x∈N):
 P.inHil j (P.piZero j x) ∈N:=by
 let M:=P.vacuum j
 have g(y:P.Hil j)(q:y∈M): N.starProjection y ∈ M:=by
   obtain ⟨t,v⟩:= (P.fixed_frame j s y).mp q
   refine (P.fixed_frame j s _).mpr ⟨?_,?_⟩
   · rw [←keepsProj N _ h ?_,t]; rw [P.heats_star];exact h
   intro d;rw [←keepsProj N _ (e d _) ?_,v d];rw [P.shift_star]; exact e d _
 have z:= keepsProj M _ g (by rw [symProj]; exact g) x
 rw [Submodule.starProjection_eq_self_iff.mpr p] at z
 exact Submodule.starProjection_eq_self_iff.mp z.symm
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
