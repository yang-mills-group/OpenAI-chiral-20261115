import YM.SU5.FiniteGaugeData.Hierarchy.Garden
import YM.CF.Buffered.Diphthong
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Chrono
open Nacre Heat RP Mir -- other
variable {N:Side}
private abbrev moveT (t:Cover) : UNI (Single N) := prepU (lagX t) 1 inert N
-- tapMark's coordinate in matter on this level, DIPH.ORI carefully. refl outer b acts forward generating support displacement `+2*(b-a)•step` in gauge. pin twist with −t. Local fields recipe pull Yg (+t)! (note in `refl_rephase` `b-a` negative). 
abbrev tapMark (t:Cover)(f:Mark N): Mark N:= fun x=> twist (quantU (moveT (-t))) (f ((Yg (lagX t) x.1),Yg (lagX t) x.2))
lemma mirroredMove (i:Axis)(a b :ℤ){S:Support (More N)}{f:Mark N}{v:Bool}(p:AtSupport v S f) : reflMark i b (reflMark i a f) = tapMark ((b-a) • step i) f:=by
 funext x; unfold reflMark tapMark
 simp_rw [reflFields,Prod.map, fling,←kor,plane_join,theta_theta _ _ _ (firm_join i a b) (p.allV _).sector]; rw [← neg_smul,neg_sub]

private lemma twinT (x y:Cover) : joinX (lagX x) (lagX y)=lagX (x+y):= by simp only [joinX,lagX,one_mul,Signed.act_one, add_comm x y]
private lemma adjust (x y:Cover) (A:FC (Single N)): twist (quantU (moveT (-x))) (twist (quantU (moveT (-y))) A)= twist (quantU (moveT (-(x+y)))) A:=by
 rw [← Fock.twin]; apply congrArg (fun (U:UNI (Finset (Single N))) => twist U A)
 have h: moveT (N:=N) (-(x+y)) = moveT (-x) * moveT (-y):= by simp only [moveT,kio,twinT,one_mul, neg_add_rev]
 rw [h]; exact Subtype.ext (quant_mul ..).symm
lemma tap_join (x y:Cover)(f:Mark N): tapMark x (tapMark y f) = tapMark (x+y) f:=by
 funext z; unfold tapMark; simp_rw [← kor,twinT,adjust]

-- convenience with reflections
private lemma anti_join (x y : Cover) (i:Axis) (p:(Signed.mirror i).act x = y)(s:ℤ) : joinX (plane i s) (lagX x)= joinX (lagX y) (plane i s):=by simp only [plane,lagX,joinX,Signed.act_one,one_mul,mul_one,add_comm _ y, p]
lemma reflect_tap (t y:Cover) (i:Axis)(s:ℤ)(p:(Signed.mirror i).act t=y){f:Mark N}{v:Bool}{S:Support (More N)}(g:AtSupport v S f):
 reflMark i s (tapMark t f)=tapMark y (reflMark i s f) := by
  have hp: (Signed.mirror i).act (-y) = -t:= by rw [← p]; simp only [Signed.act_neg]; congr 1; ext j; by_cases e:i=j <;> simp [Signed.act,Signed.mirror, e]
  have hv: carR i s N * moveT (-t)= moveT (-y) * carR i s N:=by rw [carR,moveT,moveT,kio,kio,anti_join _ _ _ hp s,mul_one,one_mul]
  funext x; unfold reflMark tapMark; rw [Window.theta_twist_right (carR ..) (moveT (-t)) (moveT (-y)) (congrArg Subtype.val hv) (g.allV _).sector]; simp_rw [reflFields, Prod.map, fling, ← kor, anti_join _ _ _ p s]
open Charm
variable (K:Calibration) (S: Finset Cover)(j i:Axis)(a b z:ℤ)
private abbrev gZ := gaugeShift K.B z
abbrev tic (K:Calibration) : ℕ := 8*K.B.val -- gauge
lemma tic_pos : 0 < tic K:=Nat.mul_pos (by decide) K.B.property
lemma tick_tock : 2*gaugeShift K.B z= (tic K:ℤ)*z:=by simp only [tic,gaugeShift,Nat.cast_mul,Nat.cast_ofNat]; ring
def clockW (x: W K): W K:= fire K i (gZ K z) (fire K i 0 x)
-- room for ALL shifted entries
abbrev temple (t:Cover)(S:Finset Cover):= S.image (· + t)
abbrev beat (x:Cover) :Cover:= x+((tic K:ℤ)*z) • step i
abbrev hour : Finset Cover:= temple (((tic K:ℤ)*z) • step i) S -- binder synth? S K only if variables used in type? implicit
lemma beat_same (x:Cover) : beat K i z x i=x i+(tic K:ℤ)*z:=by simp [beat]
lemma beat_slant (x:Cover)(p:i≠j) : beat K i z x j=x j:=by simp [beat,p.symm]
lemma loc_tic {x: W K}(h:Locator K x S):Locator K (clockW K i z x) (hour K S i z):=by
 have ht: refract i (gZ K z) (refract i 0 S)= hour K S i z:=by
   rw [refract,refract,image_image]; apply congrArg (fun (f:Cover → Cover)=> S.image f); funext x r; change _= beat K i z x r; simp_rw [Function.comp_apply,fling_move]; split_ifs with h
   · rw [←h,beat_same]; rw [← tick_tock]; simp
   rw [beat_slant K r i z x h]
 rw [← ht]; exact locate_cold K _ i _ (locate_cold K _ i _ h)
lemma flightW(p:Ahead i a K.ℓ S): Ahead i (a+(tic K:ℤ)*z) K.ℓ (hour K S i z):=by
 intro y v; obtain ⟨u,s,rfl⟩:= mem_image.mp v; specialize p u s; change _ ≤ beat K i z u i; rw [beat_same]; linarith
lemma platformL (p:i≠j)(g:Ahead j a K.ℓ S):Ahead j a K.ℓ (hour K S i z):=by
 intro y v; obtain ⟨u,s,rfl⟩:= mem_image.mp v; specialize g u s; change _ ≤ beat K i z u j; rw [beat_slant K j i z u p]; exact g
private abbrev matterShift: Cover:= gZ K z • step i
lemma tapW (x:W K)(m:Side): (clockW K i z x).val m=tapMark (matterShift K i z) (x.val m):=by
 simpa only [sub_zero,clockW,ice_print,reflector,matterShift] using mirroredMove i 0 (gZ K z) ((well_for K x).1.paid.choose_spec.support m)
@[simp] lemma tic_zero (x:W K): clockW K i 0 x=x:= by simp only [clockW,gZ,gaugeShift,mul_zero,burning_ice]
lemma clock_add (x:W K) : clockW K i a (clockW K i b x)=clockW K i (a+b) x:= by
 apply Subtype.ext; funext m; rw [tapW,tapW,tapW,tap_join]; unfold matterShift gZ gaugeShift; rw [mul_add,add_smul]
lemma clock_cross (x:W K) : clockW K i a (clockW K j b x)=clockW K j b (clockW K i a x):= by apply Subtype.ext; funext m; simp only [tapW,tap_join,add_comm (matterShift K i a)]
lemma clock_neg (x:W K): fire K i a (clockW K i z x) = clockW K i (-z) (fire K i a x):=by
 apply Subtype.ext; funext m
 have h: (Signed.mirror i).act (matterShift K i z) = matterShift K i (-z):= by rw [matterShift,mirror_axial]; simp [matterShift,gZ,gaugeShift]
 rw [tapW,ice_print, ice_print, reflector, tapW]; exact reflect_tap _ _ i a h ((well_for K x).1.paid.choose_spec.support m)
lemma clock_normal (x:W K)(p:i≠j) : fire K i a (clockW K j z x) = clockW K j z (fire K i a x):=by
 apply Subtype.ext; funext m
 have h: (Signed.mirror i).act (matterShift K j z) = matterShift K j z:= by ext r; by_cases t:i=r <;> simp_all [Signed.act,Signed.mirror,matterShift, eq_comm]
 rw [tapW,ice_print,ice_print,reflector,tapW]; exact reflect_tap _ _ i a h ((well_for K x).1.paid.choose_spec.support m)
lemma clock_mul (x y:W K): clockW K i a (x*y)=clockW K i a x * clockW K i a y:=by simp_rw [clockW,ice_join]
@[simp] lemma clock_one : clockW K i a 1=1:=by unfold clockW; rw [ice_central,ice_central]
lemma clock_sum (x y:W K): clockW K i a (x+y)=clockW K i a x + clockW K i a y:=by simp_rw [clockW,ice_more]
lemma clock_scale (x:W K)(u:ℂ): clockW K i a (u•x)=u • clockW K i a x:=by simp only [clockW,ice_paid,star_star]
#print axioms clock_normal
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
