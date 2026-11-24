import YM.SU5.Reconstruction.AnglePath.Geometry
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D){G:Clasp K H H}
open Multiplier Chirp OS Semigroup Boundary Probe Picket
variable (C:Clasp J H D) {a b:Axis}(S:OS.Semigroup H a)
local notation "Π" => S.ℚmeasure
open Bank Complex
variable (r:b≠a) (P:Tanning A C S b G)
local notation "X₀"=> A.bond C
local notation "V"=> Picket.trans S
variable (s t:ℝ)(y:E4)
noncomputable def evolves {b:Axis}(z:ℂ): H.Op:= V y*(column S b 1 (baton s t 1 z)*column S b (-1) (baton s t (-1) z)) -- v then cross
-- b implicit not incl needs explicit
local notation "E"=> evolves (b:=b) S s t y
noncomputable def chart (u:ℝ):H.Op:= V y*(S.U (xi s t u • Picket.cross a b r)* S.E (Real.toNNReal (tau s t u))) -- real
variable (p:0≤ s)(q:0≤ t)
include p q
local notation "F" e:max z:max => column S b e (baton s t e z)
lemma price(z:ℂ)(u:z∈scroll)(x:H): ‖evolves (b:=b) S s t y z x‖≤‖V y‖*‖x‖:=by
 have h(e:ℝ)(v:e=1∨e=-1)(x:H): ‖(F e z) x‖ ≤‖x‖:= ((F e z).le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (column_size b e S _ (room s t e p q v z u)))
 change ‖(V y) (_:H)‖≤_; refine ((V y).le_opNorm _).trans (mul_le_mul_of_nonneg_left ((h 1 (by simp) _).trans (h (-1) (by simp) _)) (norm_nonneg _))
private lemma travel : AnalyticOnNhd ℂ (evolves (b:=b) S s t y) income:=by
 by_cases h:s+t=0
 · have he':s=0:=by linarith
   have b':t=0:=by linarith
   rw [show evolves (b:=b) S s t y=(fun x=>V y) from funext (by intro x; simp [evolves,he',b',baton,stroke])]; exact fun x h=>analyticAt_const
 have hv(e:ℝ)(v:e=1∨e=-1) (x:ℂ)(u:x∈income): AnalyticAt ℂ (fun z:ℂ=> (F e z)) x:= (columns_hol b e S _ (suite s t e p q v x u (lt_of_le_of_ne (add_nonneg p q) (Ne.symm h)))).comp (by unfold baton rod; fun_prop : AnalyticAt ℂ (baton s t e) x)
 intro x t; exact analyticAt_const.mul ((hv 1 (by simp) x t).mul (hv (-1) (by simp) x t))
private lemma arrive (f:ℂ→H)(h:ContinuousOn f scroll):ContinuousOn (fun z=> evolves (b:=b) S s t y z (f z)) scroll:=by
 have u(e:ℝ)(v:e=1∨e=-1)(g:ℂ→H)(k:ContinuousOn g scroll): ContinuousOn (fun z=> (F e z) (g z)) scroll:=by
    rw [continuousOn_iff_continuous_restrict]; apply CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule.actor_continuous (fun z:scroll=> F e z.val) 1 zero_lt_one ?_ ?_ _ (continuousOn_iff_continuous_restrict.mp k)
    · intro z x; rw [one_mul]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) (column_size b e S _ (room s t e p q v _ z.property)))
    intro x; apply continuous_iff_continuousAt.mpr; intro w; refine column_dawn b e S _ _ (Eventually.of_forall fun z=> room s t e p q v _ z.property) (room s t e p q v _ w.property) ?_ x; exact ((show Continuous (baton s t e) from by unfold baton rod; fun_prop).comp continuous_subtype_val).tendsto _
 exact (V y).continuous.comp_continuousOn (u _ (Or.inl rfl) _ (u _ (Or.inr rfl) f h))
include r P
lemma march(u:ℝ)(v:u∈ Icc (0:ℝ) 1): evolves (b:=b) S s t y (u:ℂ)=chart S r s t y u:=by
 have p:= eu_exp b 1 (xi s t u) S P.paces (Real.toNNReal (tau s t u)) r (by simp)
 rw [Real.coe_toNNReal _ (ratePos s t (‹0 ≤ s›) q v)] at p; unfold chart evolves; rw [realTurn s t u 1 (by simp),realTurn s t u (-1) (by simp),p]
lemma imprint : evolves (b:=b) S s t y 0=V y*(S.U (t • Picket.cross a b r)* S.E (Real.toNNReal s)):=by
 simpa [chart,tau,xi,sn,cs] using march A C S r P s t y p q 0 (by simp)
variable (v:y a=0)(w:y b=0)
omit r
include v w
lemma imaginary(u:ℝ): C.cLeft u * E 0=E ((u:ℂ)*I) *C.cLeft u := by
 let k:=(u:ℂ)*I; let Q₁:= C.cLeft u; have he(e:ℝ)(t':e=1∨e=-1): Q₁ * F e 0= F e k * Q₁:=by
    rw [Bank.imaginaryTurn s t e u,show baton s t e 0=Picket.stroke e s t from (by unfold baton rod; simp)]
    exact columnTurn A C S P e u _ t' (by rw [contour_re]; positivity)

 unfold evolves; rw [←mul_assoc,(A.drumCenter C S P u v w).eq,mul_assoc, ←mul_assoc _ (F 1 0),he 1 (by simp),mul_assoc _ Q₁, he (-1) (by simp)]; simp only [mul_assoc]; rfl
include r
lemma Dollars (f g:X)(B:A.L g=V y ((S.U (t • Picket.cross a b r)) (S.E (Real.toNNReal s) (A.L f)))) (z:ℂ)(Z:z∈scroll): bond A C z g=evolves (b:=b) S s t y z (X₀ z f):=by
 apply sub_eq_zero.mp; let F₀:=(A.bond C · g); let F₁ (z:ℂ):=E z (X₀ z f); let H':=(F₀-F₁); change H' z=0; apply Bank.entangles H' (‖A.bill C g‖+‖V y‖*‖A.bill C f‖) ?_ ?_ ?_ ?_ z Z
 · intro u v; exact (norm_sub_le (X₀ u g) _).trans (add_le_add (A.bond_bound C u v _) ((price (b:=b) S s t y p q u v _).trans (mul_le_mul_of_nonneg_left (A.bond_bound C u v _) (norm_nonneg _))))
 · refine (A.bond_inner C g).sub (fun x u=>?_); change AnalyticAt ℂ F₁ x; refine DifferentiableOn.analyticAt ?_ (interiorOpen.mem_nhds u); exact (fun z q'=> (travel (b:=b) S s t y p q z q').differentiableAt.differentiableWithinAt.clm_apply ((A.bond_inner C f z q').differentiableAt.differentiableWithinAt))
 · exact (A.bond_full C g).sub (arrive (b:=b) S s t y p q _ (A.bond_full C f))
 intro x; let k:=(x:ℂ)*I; change X₀ k g - E k (X₀ k f)=0; rw [(A.bond_train C P.mid f).2.2.2 x,(A.bond_train C P.mid g).2.2.2 x, show A.L g=E 0 (A.L f) from (by rw [A.imprint C S r P s t y p q]; exact B),sub_eq_zero]; exact DFunLike.congr_fun (imaginary A C S P s t y p q v w x) _
end Organ
end YM.CrossedFrame.Cardio
