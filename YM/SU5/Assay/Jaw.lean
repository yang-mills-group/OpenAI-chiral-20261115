import YM.SU5.Assay.Base
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
/-! Centered inscriptions in a wider caliper. Both budgets in ticks and
 center offset integer (tocks). `Jaw z n w` says capacity w covers
 centering of z at n ticks from left (allows equality at endpoints).
-/
abbrev tock := bell (timeMesh P.par)
lemma tock_when (s n:ℕ):P.tock s n = (whenly (timeMesh P.par) s n:ℝ):=by simp [tock,bell,whenly]
lemma tock_zero (s:ℕ):P.tock s 0=0:=by simp [tock,bell]
lemma tock_add (s:ℕ)(p q:ℤ):P.tock s (p+q)=P.tock s p+P.tock s q:=bell_add ..
lemma tock_sub (s:ℕ)(p q:ℤ):P.tock s (p-q)=P.tock s p-P.tock s q:=P.bell_sub ..
lemma tock_one (s:ℕ):P.tock s 1=P.macroStep s:=by simp [tock,bell,macroStep]
lemma tock_le (s:ℕ)(p q:ℤ):P.tock s p≤P.tock s q ↔ p≤q:=bell_le ..
lemma tock_pose (s:ℕ)(r:Cover):P.tock s (r j)=P.meshPose s r j:=rfl
lemma tock_price (s:ℕ)(n:ℤ):P.tock s n = n*P.macroStep s:=rfl
def Jaw (z:ℕ)(n:ℤ)(w:ℕ):Prop:= z≤n∧(z:ℤ)≤ (w:ℤ)-n
variable {n k:ℤ}{w z:ℕ}{P j x}
lemma Jaw.checked (h:z≤n)(q:n+z≤w):Jaw z n w:= ⟨h,by omega⟩
lemma Jaw.shifted (h:z≤ (w:ℤ)+n)(t:z≤ (w:ℤ)-n):Jaw z (w+n) (w+w):=⟨h,by push_cast;omega⟩

local notation "σ"=> P.shifts j
local notation "μ"=> P.seenBox j x
local notation "ι"=>P.reprise j x
variable (x) in
lemma Jaw.widen {f:P.Test}(s:ℕ)(h:Jaw z n w)
 (t:P.BEntry j (z+z) (σ z f))(e:f∈enclave P.calibration):
 P.BEntry j w (σ n f) ∧
 μ s w (σ n f)=(U).hang (P.tock s z) (μ s (z+z) (σ z f)) (P.tock s n) (P.tock s (w-n)):=by
 obtain ⟨p,u⟩:=h
 let a:ℕ:= (n-z).toNat; let b:ℕ := ((w:ℤ)-n-z).toNat
 have ha:(a:ℤ)=n-z:=Int.toNat_of_nonneg (by omega)
 have hb:(b:ℤ)=(w:ℤ)-n-z:=Int.toNat_of_nonneg (by omega)
 have hW:a+(z+z)+b=w:=by omega
 have g:σ n f=σ a (σ z f):=by rw [shifts_sum,ha,sub_add_cancel]
 rw [g]; have he:= t.pad a b; rw [hW] at he
 refine ⟨he,?_⟩
 have q:= seenBox_pad s x t (P.shifts_keep j _ e) a b; rw [hW] at q; rw [q]
 have ga:= congrArg (P.tock s) ha
 have gb:= congrArg (P.tock s) hb
 rw [P.tock_sub,P.tock_when] at ga gb
 unfold hang sand wax; rw [←ga,←gb,Real.toNNReal_coe,Real.toNNReal_coe]

lemma jaw_real (P:Spine)(s:ℕ): Jaw z n w ↔ P.tock s z ≤ P.tock s n ∧ P.tock s z ≤ P.tock s w-P.tock s n:=by
 rw [←P.tock_sub,P.tock_le,P.tock_le];rfl

variable (P j x)(D:P.Apron)
local notation "β"=> P.base j x D
local notation "τ"=>D.realWidth P j
local notation "ι₀"=>P.tock D.s
lemma jaw_base (p:Jaw (D.u j) n w):
 P.BEntry j w (σ n D.F) ∧ ι (μ D.s w (σ n D.F))=β (ι₀ n) (ι₀ w-ι₀ n):=by
 obtain ⟨v,t⟩:=p.widen x D.s (D.admit j) D.realM
 rw [←P.engine_seen] at t
 rw [t,P.reprise_hang,P.tock_sub];exact ⟨v,rfl⟩
lemma jaw_seen (p:Jaw (D.u j) n w):
 μ D.s w (σ n D.F) = (U).hang τ (D.engine P j x) (ι₀ n) (ι₀ w-ι₀ n):= by
 rw [(p.widen x D.s (D.admit j) D.realM).2,←P.engine_seen,P.tock_sub];rfl
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
