import YM.SU5.May.FloeTwist
import YM.SU5.May.FloePeople
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Floe
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open Stationary (Gaia cartWeight)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
variable {N:Side}{j:ℕ}(P:Ramp)(x y z:Cover)
def Gap (j:ℕ)(z: Cover):Prop:= z P.a+ z P.b ≤ -(2*(j:ℤ)+1)
def Clear (j:ℕ)(z: Cover):Prop:= (j:ℤ) < z P.a + z P.b + 1
lemma always_gap (u:Clear P j x)(h:Clear P j y): Gap P j ((whisper P).cell x-y):=by
 let X:=nodeC ((whisper P).cell x); have hv(i:Axis) : X i=P.s.act (nodeC x) i:=congrFun (branch_clock P x) i; have ht:=hv P.a; have hh:=hv P.b; rw [P.move_a] at ht; rw [P.move_b] at hh; unfold X nodeC at ht hh; simp only [nsmul_eq_mul,Pi.add_apply,Pi.mul_apply,Nat.cast_ofNat,Pi.ofNat_apply] at ht hh; unfold Gap; rw [Pi.sub_apply,Pi.sub_apply]; unfold Clear at u h; omega
abbrev Smallish (N :Side)(x:Cover):Prop:=∀ i,2*(x i).natAbs< N.val
lemma measured (h:Smallish N (x-y)) : separation (wrap (More N) (nodeC x)) (wrap (More N) (nodeC y))= pdist (wrap (More N) (nodeC x-nodeC y)):=by rw [separation, map_sub]; -- rfl
private lemma widths_resume(i:Axis): nodeC x i-nodeC y i=2*(x-y) i:=by unfold nodeC; simp; ring
lemma gap_width(k:ℕ)(h:Smallish N (x-y))(u:x-y∉ box k): k < separation (wrap (More N) (nodeC x)) (wrap (More N) (nodeC y)):=by
 rw [box_test] at u
 let z:= nodeC x-nodeC y
 have hz(i:Axis):z i=2*(x-y) i:= widths_resume x y i
 rw [measured x y h]; have he: lift (wrap (More N) z)=z:= lift_eq_iff.mpr ⟨rfl,fun i=> by have hi:=h i; rw [hz,show (More N).val=N.val*2 from rfl,Nat.cast_mul]; push_cast; omega⟩
 obtain k'|k':=(Classical.not_and_iff_not_or_not ..).mp u -- push neg maybe form!
 · push Not at k'; obtain ⟨i,f⟩:= k'; have hg:=component_le (wrap (More N) z) i; rw [he,hz] at hg; change _ < pdist (wrap _ z); omega
 push Not at k'; obtain ⟨i,f⟩:= k'; have hg:=component_le (wrap (More N) z) i; rw [he,hz] at hg; change _ < pdist (wrap _ z); omega

local notation "R"=>((N.val):ℝ)
abbrev nature (N:Side)(x:Cover)(c:Trace j N):Gaia:= traceV N.val (point N x (traces N j c))
variable (p: Odd N.val) (c d:Trace j N)
include p
lemma natural_stamp(i:Axis): nature N x c i= (x i:ℝ)+1/2+↑(traces N j c i)/R:=by
 have h:=point_cost N p x (traces N j c) i; change (↑(point N x (traces N j c) i)+1/2)/R=_; have he:=congrArg (fun x:ℤ=>(x:ℝ)) h; push_cast at he; have hp:=side_pos N
 field_simp; linarith
lemma natural_dew(i:Axis): |nature N x c i-((x i:ℝ)+1/2)| ≤ (j:ℝ)/2:=by
 rw [natural_stamp x p,add_sub_cancel_left, abs_div, abs_of_pos (side_pos ..),div_le_iff₀ (side_pos ..)]
 have hm :=mid_double N p; obtain ⟨hx,v⟩:=trace_extent N p j c i
 have ht : (|traces N j c i|:ℤ) ≤ (j:ℤ)*mid N:=by rw [abs_le]; constructor; rwa [←neg_mul] at *; exact v
 suffices he: 2*|(traces N j c i:ℤ)| ≤ (j:ℤ)*N.val by
   have hu: 2*|(traces N j c i:ℝ)| ≤ (j:ℝ)*R:=by exact_mod_cast he
   linarith only [hu]
 nlinarith
lemma cost_coord(i:Axis): |(x-y) i - ((nature N x c - nature N y d) i:ℝ)| ≤ j :=by
 have ht:=abs_le.mp (natural_dew x p c i); have hv:=abs_le.mp (natural_dew y p d i);
 rw [abs_le]; change -_≤ ↑(x i -y i)- (nature N x c i -nature N y d i)∧ ↑(x i -y i)-(nature N x c i-nature N y d i) ≤ (j:ℝ); push_cast; constructor <;> linarith [ht.1,ht.2,hv.1,hv.2]
lemma defined_now (u:Clear P j x): face_tilt P (nature N x c):=by
 have he:= natural_dew x p c P.a; have ht:= natural_dew x p c P.b; unfold face_tilt; have hx:(j:ℝ) < (x P.a:ℝ)+(x P.b:ℝ)+1:=by unfold Clear at u; exact_mod_cast u
 linarith [ (abs_le.mp he).1,(abs_le.mp ht).1]
omit p in
lemma compactHere(x:Cover): ∃ T:Set Gaia, IsCompact T ∧ ∀ (N:Side) (c:Trace j N), Odd N.val→nature N x c∈ T:=by
 let A(i:Axis):= (x i:ℝ)+1/2; let T:= Set.univ.pi (fun i:Axis=>Set.Icc (A i-j/2) (A i+j/2)); have ht:IsCompact T:=isCompact_univ_pi (fun _ : Axis=> isCompact_Icc)
 let f:(Axis→ℝ)→Gaia:=WithLp.toLp 2; refine ⟨f '' T,ht.image (PiLp.continuous_toLp ..),fun n c p=> ⟨(nature n x c).ofLp,fun i _=> ?_,rfl⟩⟩; obtain ⟨z,l⟩:= abs_le.mp (natural_dew x p c i); change A i- (j:ℝ)/2≤ _∧ _ ≤ A i+(j:ℝ)/2; simp only [A]; constructor <;> linarith
lemma off_m (u:Gap P j (x-y)): (nature N x c P.a+ nature N x c P.b) - (nature N y d P.a+nature N y d P.b) ≤ -1:=by
 obtain ⟨hx,ht⟩:= abs_le.mp (cost_coord x y p c d P.a); obtain ⟨hv,hr⟩:= abs_le.mp (cost_coord x y p c d P.b); have he: ∀ i, (nature N x c-nature N y d) i= (nature N x c) i-(nature N y d) i:=fun i=>rfl; rw [he] at hx ht hv hr; have hz:(↑((x-y) P.a):ℝ)+↑((x-y) P.b)≤ -(2*(j:ℝ)+1):=by unfold Gap at u; exact_mod_cast u
 linarith
-- support law ensures physical.P colors b travel far; continuity for pencil. 
omit p
lemma ice_shift (u:1≤j)(e:Even N.val)(w s: Personality)(M:Jill.Male)(r:ℝ)(q:0≤r) : ice j N M r x y w s=ice j N M r (x+z) (y+z) w s:=by
 by_cases p:w.down=s.down; · simp [ice, rankG, player, p];
 cases f:w.down
 · have he:s.down=true:=by cases g:s.down<;> simp_all
   rw [show ice j N M r x y w s= -ice j N M r y x s w from rank_flip .., show ice j N M r (x+z) (y+z) w s= -ice j N M r (y+z) (x+z) s w from rank_flip .., personPrice u e M r q y x s w he f,personPrice u e M r q _ _ _ _ he f,add_sub_add_right_eq_sub]
 have he:s.down=false:=by cases g:s.down<;> simp_all
 rw [personPrice u e M r q x y w s f he,personPrice u e M r q _ _ _ _ f he,add_sub_add_right_eq_sub]
end YM.CF.May.Floe
#print axioms YM.CF.May.Floe.off_m
#print axioms YM.CF.May.Floe.ice_shift
