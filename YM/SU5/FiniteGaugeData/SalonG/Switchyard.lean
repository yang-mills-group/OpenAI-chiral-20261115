import YM.SU5.FiniteGaugeData.SalonG.Wing
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Nacre Heat Charm Chrono
namespace SalonG
variable {S T:Finset Cover}(K:Calibration)(a:Axis)(d n:ℕ)(z:ℤ)
local notation "Ψ"=> W K
-- support consensus, wagonW
abbrev mateW := Charm.fire K a (Heat.gaugeShift K.B d)
lemma mate_self (x:Ψ): mateW K a d (mateW K a d x)=x:= burning_ice ..
lemma freezing_tides (x:Ψ) : clockW K a d (Charm.fire K a 0 x)=mateW K a d x:= by unfold clockW; rw [burning_ice]
def reamW (x:Ψ)(n:ℕ) : Ψ:= if n%2=0 then x else mateW K a d x -- alternate orientation
lemma ream_zero (x:Ψ) : reamW K a d x 0=x:= rfl -- class?
lemma ream_alt (x:Ψ):reamW K a d x (n+1)=mateW K a d (reamW K a d x n):=by
 by_cases h:n%2=0; · rw [reamW,if_neg (by omega),reamW,if_pos h]
 rw [reamW,if_pos (by omega),reamW,if_neg h,mate_self]
abbrev Swing (f x: W K): W K:= f * clockW K a d x
abbrev Fold (K:Calibration)(a:Axis)(z:ℤ)(x y: W K): W K:= fire K a z x*y
lemma adjoint_frame (f x y:Ψ): Fold K a 0 x (Swing K a d f y)=clockW K a d (Fold K a 0 (Swing K a d (mateW K a d f) x) y):=by
 unfold Fold Swing mateW; rw [ice_join, clock_mul, clock_mul, freezing_tides, mateW,mate_self', clock_neg,clock_add,add_neg_cancel,tic_zero,←mul_assoc,commW K (fire ..) f] -- tune
where mate_self' (x:Ψ) : fire K a (gaugeShift K.B (d:ℤ)) (fire K a (gaugeShift K.B (d:ℤ)) x)=x:= burning_ice ..
-- turn plus sign? compute remaining clockW∘fire0∘clock+d_x=fire0 x, use clock_neg. commute
lemma adjoint_bend (f x y:Ψ): Fold K a 0 (Swing K a d f x) y=clockW K a (-(d:ℤ)) (Fold K a 0 x (Swing K a d (mateW K a d f) y)):=by rw [adjoint_frame,mate_self,clock_add,neg_add_cancel,tic_zero]

-- Geometry of assemblies
abbrev Callib := (yard K d:ℤ)
abbrev proceed (K:Calibration)(n d:ℕ) : ℕ := yard K d * n
local notation "D" => (yard K d)
local notation "A"=> Studio a 0 (yard K d) K.ℓ
lemma yard_h (x:ℤ): x*((yard K d):ℤ)= gaugeW K (x*d):= by rw [←yard_le]; unfold gaugeW; ring
lemma gauge_cast : gaugeW K (d:ℤ)=(yard K d:ℤ):= yard_le
lemma yard_step : gaugeW K ↑(d*n) = ((proceed K n d):ℤ):=by unfold proceed yard gaugeW; push_cast; ring
lemma proceed_succ : proceed K (n+1) d=proceed K n d+ D:=by unfold proceed; rw [mul_add,mul_one]
abbrev proceed_set (K:Calibration)(a:Axis)(d:ℕ)(S:Finset Cover): ℕ → Finset Cover
 | 0=>∅
 | n+1=> (S∪refract a (gaugeShift K.B d) S)∪ hour K (proceed_set K a d S n) a d
variable (f x:W K)
local notation "Q"=> proceed_set K a d S
local notation "m₁"=> refract a (gaugeShift K.B d) S
lemma ream_loc (p:Locator K f S): Locator K (reamW K a d f n) (S∪ (refract a (Heat.gaugeShift K.B d) S)):=by
 unfold reamW; split_ifs with h; · exact locate_sub K p subset_union_left
 exact locate_sub K (locate_cold K S a _ p) subset_union_right
lemma proceed_geo (p:A S) : Studio a 0 (proceed K n d) K.ℓ (proceed_set K a d S n):=by
 induction n with
 | zero=> exact Studio.empty
 | succ n ih=> rw [proceed_set]; apply Studio.union ((p.union (arbour p)).ante le_rfl (by rw [proceed_succ]; omega)); apply (ih.hour K (d:ℤ)).ante <;> rw [gauge_cast] <;> (try rw [proceed_succ]) <;> omega
abbrev Train (K:Calibration)(a:Axis)(d:ℕ)(f:W K): ℕ→ W K
 | 0=>1
 | n+1=> Swing K a d (reamW K a d f n) (Train K a d f n)
local notation "R"=> Train K a d f
lemma train_loc (p:Locator K f S) : Locator K ((Train K a d f) n) (proceed_set K a d S n):=by
 induction n with
 | zero=> exact locate_one K _
 | succ n ih=> exact locate_join _ _ (locate_sub _ (ream_loc K a d n f p) subset_union_left) (locate_sub _ (loc_tic K _ a d ih) subset_union_right)
-- ends precisely 2d away
abbrev wagon := clockW K a (d*(n+2):ℕ) x
abbrev rear (S: Finset Cover) := hour K S a (d*(n+2):ℕ)
abbrev openQ (x:W K): W K:= Train K a d f n * wagon K a d n x
lemma operate_succ : openQ K a d (n+1) f x= Swing K a d (reamW K a d f n) (openQ K a d n f x):=by rw [openQ,openQ,Swing,clock_mul, Train,Swing,mul_assoc]; unfold wagon; rw [clock_add]; apply congrArg; apply congrArg; congr 1; push_cast; ring -- congr levels
lemma open_loc (t:Locator K f S)(u:Locator K x T): Locator K (openQ K a d n f x) (proceed_set K a d S n ∪ rear K a d n T):= locate_join K _ (locate_sub _ (train_loc K a d n _ t) subset_union_left) (locate_sub _ (loc_tic K T a _ u) subset_union_right)
abbrev Width (f:W K)(C:ℝ):Prop:= ∀ (m:Side)(v:Fields (K.c m)), ‖f.val m v‖ ≤ C
abbrev RealWidth (f:W K)(m:Side)(C:ℝ):Prop:= ∀ v:Fields (K.c m),‖f.val m v‖≤ C
variable {K f x} {m:Side} {B A':ℝ}
namespace RealWidth
lemma reflected (p:RealWidth K f m B)(z:ℤ): RealWidth K (fire K a z f) m B:= fun v=> (theta_fee _ (f.val m (reflFields a z v))).le.trans (p _)
lemma tick (p:RealWidth K f m B)(z:ℤ): RealWidth K (clockW K a z f) m B:= reflected a (reflected a p 0) _
lemma mule (p:RealWidth K f m B)(e:RealWidth K x m A'): RealWidth K (f*x) m (B*A'):=fun v=> (norm_mul_le (f.val m v) (x.val m v)).trans (mul_le_mul (p v) (e v) (norm_nonneg _) ((norm_nonneg _).trans (p v)))
lemma smule (p:RealWidth K f m B)(z:ℂ): RealWidth K (z • f) m (‖z‖*B):=fun v=> (norm_smul z (f.val m v)).le.trans (mul_le_mul_of_nonneg_left (p v) (norm_nonneg _))
lemma camp (p:RealWidth K f m B): RealWidth K (Train K a d f n) m (B^n):=by
 induction n with
 | zero=> rw [pow_zero]; exact fun i=> (norm_one (α:=FC (Single (K.c m)))).le
 | succ n ih=> rw [Train,pow_succ']; unfold Swing reamW; split_ifs with e; · exact mule p (tick a ih ↑d)
               exact mule (reflected a p (Heat.gaugeShift K.B d)) (tick a ih ↑d)
lemma cashW {L:Loom (K.c m)}(p:RealWidth K f m B): cash L (f.val m)≤ B:= by
 unfold cash; apply (integral_mono_of_nonneg (Eventually.of_forall (fun _=> norm_nonneg _)) (integrable_const («μ»:=city _) B) (Eventually.of_forall (fun x'=> p _))).trans_eq ?_; simp
end RealWidth
lemma width_read (p:Locator K f S): Width K f (duration S * ‖reading K S f p‖):= fun m v=> (congrArg (fun t:Family K=>‖t m v‖) (reading_p K S f p)).symm.le.trans (compose_price ..)

#print axioms adjoint_frame
#print axioms proceed_geo
#print axioms operate_succ
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
