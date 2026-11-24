import YM.CF.Hove.Pair
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable (j:ℕ)(p:4≤j)(e:Even j)
variable {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(M:Male)(b:Bool)(o: Site c)(T:Script Male)(u:Use j G.count T)
variable(C:ℝ)(hC:0≤C)(X ε:ℝ)(n:ℕ)(ι:BenchQ j G w M b o T C n)
local notation "β"=> baseF
local notation "Y" b:max d:max=> wingF j G w T M b (heel G o) d
local notation "R₁"=> Tap.lace 0 G.count
local notation "R₂"=> Tap.lace 1 G.count
local notation "θ"=> (1+(n:ℝ))
variable (S:Matrix (Single c) Kt ℂ)(H:Matrix (Single c) Kt ℂ)
local notation "Ψ"=> chipF j G w T M (heel G o)
variable (V:Dome)
local notation "W" b:max d:max=> (wingF j G w T M b (heel G o) d)
local notation "W0"=> rampF false o
local notation "W1"=> rampF true o
variable (A₀:BenchQ j G w M false o T C n)(A₁:BenchQ j G w M true o T C n)
local notation "Z"=> (β false)
local notation "Z1"=> (β true)
variable(Xa Yb:ℝ)(hv0:‖V.1‖≤Xa)(hv1:∀ s:Axis,‖V.2.1 s‖≤Yb)(hv2:∀ s:Axis,‖V.2.2 s‖≤Yb)
include A₀ A₁ hC hv0 hv1 hv2
local notation "Z₀"=> C + ‖baseF false‖ + ‖baseF true‖ + 1
local notation "ζ"=> ((R₁:ℂ)*(R₂:ℂ))
variable (s:Axis)
local notation "θQ"=> Z₀^2*(R₁^2*Xa)+12* Z₀^2*(R₁*R₂*Yb)/θ
lemma tonic_X : ‖partX o (Ψ V) s - ζ • culm (V.2.1 s)‖≤ θQ:=by
 let a(k):= (Y false k)* spanH false o s; let b(k):= (Y true k)*W1; let P:=Z₀
 have hp:0 ≤ P:=by unfold P; positivity
 have hz:0 ≤ R₁:=by unfold lace; positivity
 have he:0 ≤ R₂:=by unfold lace; positivity
 have hτ:0 ≤ θ:=by positivity
 have hY:C ≤ P:=by unfold P; linarith [norm_nonneg Z,norm_nonneg Z1]
 let ξ:=P^2*(R₁^2*Xa); let η:=P^2*(R₁*R₂*Yb)/θ
 let X(v):=φv false G.count v s; let Zx:= (R₁:ℂ) • Z1; let F(i):=(a [])ᴴ * V.2.2 i * b [i]; let L(i):=(a [i])ᴴ*V.2.1 i*b []; let G_(i):=(X i)ᴴ *V.2.1 i*Zx
 have hl: ζ • culm (V.2.1 s)= ∑ i:Axis,G_ i:=by
    rw [sum_eq_single s]; swap; · intro i _ h; unfold G_ X φv; simp [h]
    change _=star (X s)*_* Zx; unfold Zx X φv; rw [if_pos rfl,star_smul, show star Z=Z from φ_a _, Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]; unfold culm; simp
    simp
 have hv₁: ∀ i,‖X i‖≤ P*R₂:=by
    intro i; unfold X φv; split; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he,mul_comm]; gcongr; unfold P; linarith [norm_nonneg Z1]
    rw [norm_zero]; positivity
 have hx₀:(‖a []‖≤ P*R₁):=(A₀.nextV s).trans (by gcongr)
 have hQ:‖b []‖≤ P*R₁:= A₁.mass.trans (by gcongr)
 have h':‖∑ i:Axis,F i‖≤ 4*η:=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>η) ?_).trans_eq (by simp [Axis])); intro i _; apply (surgeH _ _ _ (P*R₁) (P*R₂/θ) hx₀ ((A₁.cap i).trans (by gcongr)) (hv2 i)).trans_eq; unfold η; ring
 have hx:‖∑ i:Axis,(L i-G_ i)‖≤4*(2*η):=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>2*η) ?_).trans_eq (by simp [Axis])); intro i _; apply (lyz _ _ _ (X i) Zx _ _ (P*R₂/θ) (P*R₁/θ) (hv₁ i) hQ ((A₀.turn i s).trans (by gcongr)) (A₁.scale.trans (by gcongr)) (hv1 i)).trans_eq; unfold η; ring
 unfold partX; rw [ζg,hl, add_sub_assoc, ←sum_sub_distrib]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (surgeH _ _ _ _ _ hx₀ hQ hv0) h')) hx).trans_eq ?_); unfold η P; ring
lemma tonic_Y : ‖partY o (Ψ V) s - ζ • culm (V.2.2 s)‖≤ θQ:=by
 let a(k):= (Y true k)* spanH true o s; let b(k):= (Y false k)*W0; let P:=Z₀
 have hp:0 ≤ P:=by unfold P; positivity
 have hz:0 ≤ R₁:=by unfold lace; positivity
 have he:0 ≤ R₂:=by unfold lace; positivity
 have hτ:0 ≤ θ:=by positivity
 have hY:C ≤ P:=by unfold P; linarith [norm_nonneg Z,norm_nonneg Z1]
 let ξ:=P^2*(R₁^2*Xa); let η:=P^2*(R₁*R₂*Yb)/θ
 let X(v):=φv true G.count v s; let Zx:= (R₁:ℂ) • Z; let F(i):=(b [i])ᴴ * V.2.1 i * a []; let L(i):=(b [])ᴴ*V.2.2 i*a [i]; let G_(i):=Zxᴴ *V.2.2 i*X i
 have hl: ζ • culm (V.2.2 s)= ∑ i:Axis,G_ i:=by
    rw [sum_eq_single s]; swap; · intro i _ h; unfold G_ X φv; simp [h]
    change _=star Zx*_*X s; unfold Zx X φv; rw [if_pos rfl,star_smul, show star Z=Z from φ_a _, Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]; unfold culm; simp [mul_comm] -- commute star issue
    simp
 have hv:‖Zx‖≤ P*R₁:=by unfold Zx; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz,mul_comm]; gcongr; unfold P; linarith [norm_nonneg Z1]
 have hx₀:(‖a []‖≤ P*R₁):=(A₁.nextV s).trans (by gcongr)
 have hQ:‖b []‖≤ P*R₁:= A₀.mass.trans (by gcongr)
 have h':‖∑ i:Axis,F i‖≤ 4*η:=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>η) ?_).trans_eq (by simp [Axis])); intro i _; apply (surgeH _ _ _ (P*R₂/θ) (P*R₁) ((A₀.cap i).trans (by gcongr)) hx₀ (hv1 i)).trans_eq; unfold η; ring
 have hx:‖∑ i:Axis,(L i-G_ i)‖≤4*(2*η):=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>2*η) ?_).trans_eq (by simp [Axis])); intro i _; apply (lyz _ _ _ Zx (X i) _ (P*R₂) (P*R₁/θ) (P*R₂/θ) hv ((A₁.tube i s).trans (by gcongr)) (A₀.scale.trans (by gcongr)) ((A₁.turn i s).trans (by gcongr)) (hv2 i)).trans_eq; unfold η; ring
 unfold partY; rw [ζg,hl, add_sub_right_comm,add_sub_assoc, ←sum_sub_distrib]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (surgeH _ _ _ _ _ hQ hx₀ hv0) hx)) h').trans_eq ?_); unfold η P; ring
end YM.CF.Hove
