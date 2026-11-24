import YM.SU5.FiniteGaugeData.Celeritas.Fluxa
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
open OS OS.Semigroup Spectral Lattice Function Filter Metric Mist.Utah Complex Set MeasureTheory MeasureTheory.Measure Boundary Probe NormedSpace InnerProductSpace
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators
set_option quotPrecheck false
namespace Land
variable {K:Axis→Hilbert}(W:∀ a:Axis,OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) (U:Set (Shrine K)) (a b:Axis)
variable (o:E4)(A B: Shrine K)(z:OS.Cross a)(u s:ℝ≥0)
private abbrev γ (S:E4):Fin 2→E4:= ![o,S]
abbrev tapL (A B:Shrine K): Fin 2→Shrine K:= ![A,B]
abbrev stampPos : Fin 2→ E4:= γ o (jeer a (z.val+o) ((u:ℝ)+A.t a+B.t a))
abbrev Corr:ℂ:= chorus W Ω (tapL A B) (stampPos a o A B z u) [0,1] a
local notation "T" =>W a
local notation "Q"=>tapL A B
local notation "p1" u:max z:max=> stampPos a o A B z u
local notation "F" =>orbit_on W a o B
local notation "x1" => (F) (Ω a)
local notation "G" x:max=>(W a).E x
variable (L: B.f a=star (A.f a)) (q:∀ z:E4,(W a).unit.translation z (Ω a) =Ω a)
lemma stampD : (stampPos a o A B z u 1) a=o a+((u:ℝ)+(A.t a))+ (B.t a):=by change (jeer ..) (_)= _; rw [top_a,PiLp.add_apply,show z.val a=0 from z.property, zero_add]; ring
lemma formation (c:0<u): List.Pairwise (Seers Q (p1 u z) a) [0,1]:=by simp [Seers,endX,startX,tapL, show z.val a=0 from z.property]; linarith only [(show (0:ℝ)<u from c),stampD a o A B z u]
lemma shift_t : Hi Q (p1 u z) a 0 1=u:=by unfold Hi startX endX; rw [stampD]; let h(z:ℝ):=Real.toNNReal z; change _= _; rw [show (o a+ _+_-_)-_=(u:ℝ) from ?_]; rw [Real.toNNReal_coe]; change (_+((u:ℝ)+ ↑(A.t a))+↑(B.t a)-↑(B.t a))- (o a+ ↑(A.t a))= _; ring
local notation "U1" => leg (T)
include L q
lemma activist : Corr W Ω a o A B z u=inner ℂ x1 ((W a).U z ((G u) x1)):=by
 let y:=z.val+o; let X:=(A.f a); let k:=(p1 u z); have he: actO W Q k a 0=star F:= by change orbit_on W a o A =_; unfold orbit_on; rw [opt_star,L,star_star]
 let v:=Ω a; have hw :actO W Q k a 1 v=(W a).U z x1:= by
    have hp: (p1 u z) 1=jeer a y ((u:ℝ)+A.t a+B.t a):=rfl
    let y':=(u:ℝ)+A.t a+B.t a; have hv:=leg_G T (jeer a y y') v q
    change orbit_on W a (jeer a y y') B v= _; rw [show orbit_on W a (jeer a y y') B v=orbit_on W a y B v from sit W Ω a B false q y' y]; change opt T (z.val+o) _ v=_; rw [← opt_add, opt, leg_sp, mul_apply_eq_comp,leg_G T (-z.val) v q]; rfl
 change inner ℂ v (actO W Q k a 0 ((W a).E (Hi Q k a 0 1) (actO W Q k a 1 v)))=_; rw [he,hw,show Hi Q k a 0 1=_ from shift_t ..]; exact ((ContinuousLinearMap.adjoint_inner_right F _ _)).trans (congrArg (inner ℂ x1) (DFunLike.congr_fun ((W a).independent ..) _))
abbrev r(u:ℝ≥0)(z:OS.Cross a):= (Corr W Ω a o A B z u).re
def Payment : Prop:=∀ (v:OS.Cross a),‖v‖≤1→∀ (z:ℝ≥0),z≤1→
 let C:=r W Ω a o A B; let m:= (1+z:ℝ≥0); C (m+m) 0 -2*C (m+m) ((z:ℝ) • v)+2*C (m+1) 0 ≤ C 2 0 -- Lean private def leak? unfold public. $2 corrmm-2 corr... ≤ corrmm+c2−2...$
-- contour link iff.Adv. 
private lemma legwork (i j:ℝ≥0) : (inner ℂ ((G i) x1) ((W a).U z ((G j) x1))).re= (Corr W Ω a o A B z (i+j)).re:=by
 rw [activist W Ω a o A B z _ L q]; refine congrArg Complex.re ?_; rw [← ContinuousLinearMap.adjoint_inner_right,(W a).sym]; apply congrArg; refine DFunLike.congr_fun (show ((G i)*(W a).U z * G j)=(W a).U z*((G (i+j))) from ?_) x1; rw [show G (i+j)=(G i)*(G j) from (W a).time ..,(show (G i)*(W a).U z=(W a).U z*(G i) from (W a).independent ..),mul_assoc]
private lemma up_price(i j:ℝ≥0):(inner ℂ ((G i) x1) ((G j) x1)).re= (Corr W Ω a o A B 0 (i+j)).re:=by
 have ht:=legwork W Ω a o A B 0 L q i j; rw [(W a).uZero] at ht; exact ht
private lemma p_norm(u:ℝ≥0): ‖(G u) x1‖^2= (Corr W Ω a o A B 0 (u+u)).re:= (inner_self_eq_norm_sq (𝕜:=ℂ) _).symm.trans (up_price W Ω a o A B L q u u)
lemma p_vec : Velocity (W a) 1 1 x1 ↔ Payment W Ω a o A B:=by
 have ht(i:ℝ≥0)(z:OS.Cross a): let U:=(G (1+i)) x1; let Tx(x:E4):=(W a).U z; let K:=1+i; dist ((W a).U z U) U ≤ dist U ((G 1) x1) ↔ ((r W Ω a o A B) (K+K) 0- 2* (Corr W Ω a o A B z (K+K)).re + 2* (Corr W Ω a o A B 0 (K+1)).re ≤ (Corr W Ω a o A B 0 2).re):=by
    intro U K_ K; rw [dist_comm _ U,← sq_le_sq₀ (by positivity) (by positivity),dist_eq_norm,dist_eq_norm,norm_sub_sq (𝕜:=ℂ),norm_sub_sq (𝕜:=ℂ),RCLike.re_eq_complex_re,(W a).unitary]; unfold U; rw [up_price W Ω a o A B L q,legwork W Ω a o A B _ L q]; simp_rw [p_norm W Ω a o A B L q]; -- order s
    unfold r K; have h:(1:ℝ≥0)+1=2:=by norm_num
    rw [h]; constructor <;> intro hp <;> linarith
 unfold Velocity Payment; apply forall_congr'; intro v; apply forall_congr'; intro p; apply forall_congr'; intro s; simp only [NNReal.coe_le_one]; apply forall_congr'; intro p; apply ht
#print axioms p_vec
end Land
end YM.CF.Buffered.Afterglow.Hierarchy.Celeritas
