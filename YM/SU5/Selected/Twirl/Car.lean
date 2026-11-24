import YM.SU5.Selected.Twirl.Price
import YM.SU5.Selected.Cor.Micah
import YM.SU5.FiniteGaugeData.Tower.Roomer
import YM.SU5.Selected.Cor.Clasp
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
set_option synthInstance.maxSize 24000
namespace Mezz
open Payroll Caste Silks
local notation "ⅈ" => Complex.I
-- implicit from same history calibrated, `pre_shift` always exact no size requirement. Standards. Choose matrix turn sign!
open Nacre
open Afterglow Afterglow.Tower.SlabMark
variable {N:Side}(h:ℤ) (A:Mezz)
def pumped (k:ℕ):= {A with ride:=k}
-- preserving *all* supports and geometry. Changing only gauge root location of X. Deps still defeq by whnf!
lemma pump_data (e:A.Legate)(k:ℕ): (pumped A k).Legate:=⟨e.turn⟩
def wandW (h:ℤ) : Cover := h • step 3
local notation "w'" i:max => wandW i
local notation "S" h:max => Nacre.lagX (wandW h)
abbrev shuffleW (h:ℤ) (N:Side):=prepU (lagX (wandW (-h))) 1 inert N -- coefficient pulls FROM x-h
abbrev shuffleG (h:ℤ) (V:Pane N) : Pane N:= Yg (lagX (wandW h)) V -- arguments move +h (to buy future value. opposite!)
lemma pend_h : Ε (0:FaceL) (-h)=wandW (-h):= by
 funext x; fin_cases x <;> simp [Ε,wandW] <;> rfl
lemma shift_eqv (i:Axis)(q:i≠3) : joinX (S h) (plane i 0)=joinX (plane i 0) (S h):=by
 unfold joinX plane lagX; simp only [Signed.act_one,mul_one,one_mul,zero_smul,add_zero,zero_add]; congr 1; funext x; by_cases k:x=i; subst x; simp [Signed.mirror,Signed.act,wandW,q]; simp [Signed.mirror,Signed.act,k,Ne.symm k]
variable {S₀:Finset Cover}{K:Calibration}
local notation "Χ" f:max=> shuffleG h f
local notation "P" h:max=> shuffleW h N
lemma rear_r (x:Axis)(t:x≠3) : Commute (shuffleW h N) (carR x 0 N):= by
 change _*_=_; unfold shuffleW carR; rw [kio,kio, shift_eqv (-h) x t,one_mul,mul_one]
lemma ro_rear : Commute (shuffleW h N) (Ro N):= (rear_r h 0 (by decide)).mul_right (rear_r h 1 (by decide))
lemma fling_shuffle (x:Axis)(t:x≠3)(V:Pane N) : fling x 0 N (Χ V) = Χ (fling x 0 N V):=by unfold fling shuffleG; rw [←kor,←kor,shift_eqv h x t]
lemma swoop_shuffle (V:Pane N) : swoop (Χ V) = Χ (swoop V):= by unfold swoop; simp only [Function.comp_apply]; rw [fling_shuffle h 0 (by decide),fling_shuffle h 1 (by decide)]
lemma root_repair (d: A.BlockDay)(a:A.ride=0)(x:ℕ)(g:x ≤ A.passW): (A.pumped x).grape d true=A.grape d true+( (2:ℕ) • w' (x:ℤ)):=by
 funext i; by_cases p:i=3
 · subst i; have ht(k) : (A.pumped k).grape d true 3= A.slopeW d true +2*((min k A.passW:ℕ):ℤ):= rfl -- tune
   have hp:A.grape d true 3=A.slopeW d true+2* (min A.ride A.passW:ℕ):= rfl; rw [Pi.add_apply,hp,ht,a,Nat.min_def]; simp [g,min_eq_left,wandW,two_smul,two_mul] -- beware simp cast?
 rw [Pi.add_apply,A.fork_tr d true i p,(A.pumped x).fork_tr d true i p]; simp [wandW,p]
variable {f g:Buffered.Family K} {M:Tulip.Male}
-- exact theta_theta vs spin coherent. on one Mark F with Envelope. independent of AP reduction. compare Room via family over enough N.
lemma hover {S':Finset (Seat N)}(f:Buffered.Mark N)(F:Fields N)(e:AtSupport false S' f) : reflMark 3 h (reflMark 3 0 f) F = twist (quantU (shuffleW h N)) (f (Χ F.1,Χ F.2)):=by
 have hu(V:Pane N): fling 3 0 N (fling 3 h N V)=Χ V:=by unfold fling shuffleG; rw [←kor,Heat.plane_join,sub_zero]; rfl
 change theta _ (theta _ (f ((fling 3 0 N _) , fling 3 0 N _))) = _ -- syntax tune
 rw [hu,hu,Heat.theta_theta _ _ _ (Heat.firm_join 3 0 h) (e.allV _|>.sector),zero_sub]; rfl
local notation "Σ" h:max=> wrap (More N) ( (2:ℕ) • w' h)
lemma travel_shiftG (f:Pane N)(W:Lattice.Walk)(x:Seat N): travel (Χ f) x W= travel f (x+ wrap (More N) ( (2:ℕ) • wandW h)) W:=by
 change travel (Lattice.pull 1 (Σ h) _) _ _= _; rw [travel_pull]; simp [affine] -- map_rotate tune
lemma stamp_roll (x z:Seat N)(f:Pane N): stampG (x+ Σ h) f (z+ Σ h)= stampG x (Χ f) z:=by unfold stampG; rw [travel_shiftG]; congr 1; unfold march; rw [add_sub_add_right_eq_sub]
lemma anon_roll (x:Seat N): (lagX (wandW (-h))).anon N x=x- Σ h:= by unfold Shape.anon lagX affine wandW; simp [sub_eq_add_neg]
lemma guile_load (x:Seat N)(f:Pane N): (P h) * tradew N ((stampG x (Χ f))⁻¹) = tradew N ((stampG (x+ Σ h) f)⁻¹) * (P h):=by
 unfold shuffleW; rw [envoy]; congr 2; funext z; rw [Function.comp_apply,anon_roll h z]; nth_rw 2 [show z=z- Σ h+ Σ h from (by abel)]; rw [Pi.inv_apply,Pi.inv_apply,stamp_roll]
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms guile_load
#print axioms pump_data
#print axioms root_repair
#print axioms hover
