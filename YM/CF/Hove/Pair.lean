import YM.CF.Hove.Chest
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
def coneL : Pal→ₗ[ℂ] Pal:={ toFun:= fun X=>culm X,map_add':=fun x y=>by unfold culm; rw [mul_add,add_mul],map_smul':=fun x y=>by unfold culm; rw [RingHom.id_apply,Matrix.mul_smul,Matrix.smul_mul] }
abbrev pruneQ:= 1+‖coneL.toContinuousLinearMap‖
lemma pruned(X:Pal):‖culm X‖≤pruneQ*‖X‖:=le_trans (coneL.toContinuousLinearMap.le_opNorm X) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
variable (A B D:Pal){K L':ℝ}
lemma surgeH (a b:ℝ)(h:‖A‖≤ a)(p:‖B‖≤ b)(u:‖D‖≤ K): ‖Aᴴ*D*B‖≤ a*K*b:=by
 refine (norm_mul_le _ _).trans (mul_le_mul ?_ p (norm_nonneg _) ?_)
 · change ‖star A * D‖≤ _; exact (norm_mul_le ..).trans (mul_le_mul ((norm_star A).trans_le h) u (norm_nonneg _) ((norm_nonneg _).trans h)) -- mul_le_mul last wants a≥
 exact mul_nonneg ((norm_nonneg _).trans h) ((norm_nonneg _).trans u)
lemma lyz (Rv Z:Pal)(a b x y:ℝ)(h:‖Rv‖≤ a)(p:‖B‖≤ b)(s:‖A-Rv‖≤x)(v:‖B-Z‖≤ y)(u:‖D‖≤ K) : ‖Aᴴ*D*B-Rvᴴ*D*Z‖≤x*K*b+a*K*y:=by
 rw [show _ᴴ*D* B-Rvᴴ*D*Z=((A-Rv)ᴴ*D*B)+(Rvᴴ*D*(B-Z)) from ?_]; swap; · simp only [Matrix.conjTranspose_sub,Matrix.sub_mul,Matrix.mul_sub]; abel
 exact (norm_add_le ..).trans (add_le_add (surgeH _ _ D _ _ s p u) (surgeH _ _ D _ _ h v u))
local notation "R₁"=> Tap.lace 0 G.count
local notation "R₂"=> Tap.lace 1 G.count
local notation "θ"=> (1+(n:ℝ))
variable (S:Matrix (Single c) Kt ℂ)(H:Matrix (Single c) Kt ℂ)
def snapH : Op (Single c) →ₗ[ℂ] Pal:={ toFun:=fun A=> Sᴴ*A*H,map_add':=fun x y=>by rw [Matrix.mul_add,Matrix.add_mul],map_smul':=fun x y=>by rw [RingHom.id_apply, Matrix.mul_smul,Matrix.smul_mul] }
local notation "Ψ"=> chipF j G w T M (heel G o)
variable (V:Dome)
lemma crisp(U Q:Matrix Kt (Single c) ℂ): snapH S H (Uᴴ*D*Q)=(U*S)ᴴ *D* (Q*H):=by unfold snapH; change Sᴴ*(Uᴴ*D*Q) *H=_; rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
local notation "W" b:max d:max=> (wingF j G w T M b (heel G o) d)
lemma ζg : Sᴴ*Ψ V* H= ((Y false [])*S)ᴴ*V.1* ((Y true [])*H)+(∑ a:Axis, ((Y false [])*S)ᴴ*V.2.2 a*((Y true [a])*H))+ ∑ a:Axis,((Y false [a])*S)ᴴ*V.2.1 a*((Y true [])*H) :=by
 change snapH S H (Ψ V)=_; simp only [chipF,map_add,map_sum]; simp_rw [crisp]
local notation "W0"=> rampF false o
local notation "W1"=> rampF true o
variable (A₀:BenchQ j G w M false o T C n)(A₁:BenchQ j G w M true o T C n)
local notation "Z"=> (β false)
local notation "Z1"=> (β true)
variable(Xa Yb:ℝ)(hv0:‖V.1‖≤Xa)(hv1:∀ s:Axis,‖V.2.1 s‖≤Yb)(hv2:∀ s:Axis,‖V.2.2 s‖≤Yb)
include A₀ A₁ hC hv0 hv1 hv2
local notation "Z₀"=> C + ‖baseF false‖ + ‖baseF true‖ + 1
lemma comet_v : ‖mornC o (Ψ V) - (R₁:ℂ)^2 • culm V.1‖≤ ((2* Z₀^2)*(R₁^2*Xa)+(8*Z₀^2)*(R₁*R₂*Yb))/θ:=by
 let a(k):= (Y false k)*W0; let b(k):= (Y true k)*W1; let Zp:=Z₀; have hp:0 ≤ Zp:=by unfold Zp; positivity
 have hz:0 ≤ R₁:=by unfold lace; positivity; -- end
 have he:0 ≤ R₂:=by unfold lace; positivity;
 have hq:0 < θ:=by positivity
 have hx:= A₀.mass; have hb:= A₁.mass; let Zx:= (R₁:ℂ) • Z; let Zy:= (R₁:ℂ) • Z1
 have hl : (R₁:ℂ)^2 • culm V.1= Zxᴴ*V.1*Zy:=by
    change _= star Zx*V.1*Zy; unfold Zx Zy; rw [star_smul,show star (_:ℂ)=((R₁:ℝ):ℂ) from (by simp),show star Z=_ from φ_a _,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul]; unfold culm; rw [smul_smul,pow_two]
 have hY:C ≤ Zp:=by unfold Zp; linarith [norm_nonneg Z,norm_nonneg Z1]
 have hp1:‖Zx‖≤ Zp*R₁:=by unfold Zx; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz,mul_comm]; gcongr; unfold Zp; linarith [norm_nonneg Z1]
 let ξ:=(2*Zp^2)*(R₁^2*Xa)/θ; let η:=Zp^2*(R₁*R₂*Yb)/θ
 have p₀:‖(a [])ᴴ* V.1*b []-Zxᴴ*V.1*Zy‖≤ ξ:=by
    refine (lyz _ _ _ Zx Zy (Zp*R₁) (Zp*R₁) (Zp*R₁/θ) (Zp*R₁/θ) hp1 (hb.trans (mul_le_mul_of_nonneg_right hY hz)) (A₀.scale.trans (by gcongr)) (A₁.scale.trans (by gcongr)) hv0).trans_eq ?_; unfold ξ; ring
 have hD:‖∑ i:Axis,(a [])ᴴ * V.2.2 i*b [i]‖≤ 4*η:=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>η) ?_).trans_eq (by simp [Axis])); intro i _; refine (surgeH _ _ _ (Zp*R₁) (Zp*R₂/θ) (hx.trans ?_) ((A₁.cap i).trans ?_) (hv2 i)).trans_eq ?_; gcongr; gcongr; unfold η; ring
 have hQ:‖∑ i:Axis,(a [i])ᴴ* V.2.1 i* b []‖≤ 4*η:=by
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>η) ?_).trans_eq (by simp [Axis])); intro i _; refine (surgeH _ _ _ (Zp*R₂/θ) (Zp*R₁) ((A₀.cap i).trans ?_) (hb.trans ?_) (hv1 i)).trans_eq ?_; gcongr; gcongr; unfold η; ring
 unfold mornC; rw [ζg j G w M o T W0 W1 V,hl]; rw [add_sub_right_comm, add_sub_right_comm]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add p₀ hD)) hQ).trans_eq ?_); unfold ξ η Zp; ring
end YM.CF.Hove
