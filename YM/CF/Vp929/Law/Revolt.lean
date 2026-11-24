import YM.CF.Vp929.Law.Cells
import YM.CF.Vp929.Law.Spin
import YM.CF.Skye.Can
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric Rooms Mos Mesa Cube Lat WalkBound Skye Spire Scroll SU
open scoped Topology Classical Matrix.Norms.Frobenius
namespace March
variable (s t: March) (A:Realms)(f:Elm){K:ℝ}{C:Side}
def turns(A:Realms):Realms:=polarT s.charge ∘ Lattice.pull s.step s.endpt A
def kicks(f:Elm):Elm:= fun i=>polarT s.charge (f (s.slide i))
lemma next_point (d:Step)(x:Cover): s.slide (x+d.vec)=s.slide x+(d.rotate s.step).vec:=by rw [Step.vec_rotate]; simp [slide]; abel
def lane(d:Step)(x:Cover):= (d.rotate s.step).used (s.slide x)
lemma ladder(x:Cover)(d:Step): d.read (turns s A) x=polarT s.charge ((d.rotate s.step).read A (s.slide x)):=by
 change _= polarT s.charge ((d.rotate s.step).read A (affine s.step s.endpt x)); rw [←Step.pull_read]; cases h:d.neg <;> simp only [Step.read,h,↓reduceIte,map_inv,turns,comp_apply, Bool.false_eq_true]
lemma lane_z (d:Step)(x:Cover):zone (s.lane d x)=s.follow (span x (x+d.vec)):=by
 rw [Rooms.spanEq,s.next_point]; unfold lane; generalize (d.rotate s.step)=e; rcases e with ⟨i,(_|_)⟩; rfl; simp only [zone,Step.used,↓reduceIte,Step.vec]; rw [sub_add_cancel]; rw [Rooms.spanComm]; rw [←sub_eq_add_neg]
@[simp] lemma turnOne: turns 1 A=A:=by change polarT false ∘ pull 1 0 A=_; rw [Lattice.pull_id]; rfl
@[simp] lemma turnChain : turns (s*t) A=turns t (turns s A) :=by
 funext ⟨x,i⟩; change (posDir i).read (turns (s*t) A) x=(posDir i).read (turns t (turns s A)) x
 rw [(s*t).ladder,t.ladder,s.ladder]; rw [polar_t,Bool.xor_comm]; change (polarT _) (((posDir i).rotate (s.step*t.step)).read A _) = _; rw [trans,Step.rotate_mul]; rfl
@[simp] lemma turnBack : turns s⁻¹ (turns s A)=A:=by rw [← turnChain]; simp
@[simp] lemma turnForward : turns s (turns s⁻¹ A)=A:=by rw [← turnChain]; simp
@[simp] lemma kicksOne:kicks 1 f=f:=by funext i; change polarT false (f ((1:March).slide _))=_; rw [March.live]; rfl
@[simp] lemma kickChain:kicks (s*t) f=kicks t (kicks s f):=by funext i; unfold kicks; rw [trans,polar_t,Bool.xor_comm]; rfl
@[simp] lemma kickBack : kicks s⁻¹ (kicks s f)=f:=by rw [← kickChain]; simp
@[simp] lemma kickForward:kicks s (kicks s⁻¹ f)=f:=by rw [← kickChain]; simp
lemma capDistance(u v:SU.E): GDist u v=Mesa.lambda (u*v⁻¹)*(Real.sqrt (SU.group.repDim:ℝ)):=by
  unfold GDist Mesa.lambda Gauge.chord; rw [div_mul_cancel₀,← bolt u v v⁻¹,dist_eq_norm,mul_inv_cancel]; rfl
  exact (Real.sqrt_pos.mpr (by exact_mod_cast SU.group.dimPos)).ne'
private lemma polarCa(u v:SU.E)(p:Bool): GDist (polarT p u) (polarT p v)=GDist u v:=by rw [capDistance,capDistance, ←map_inv,←map_mul]; cases p with | false=> rfl | true=> exact congrArg (· * (Real.sqrt (SU.group.repDim:ℝ))) (Reef.cool ..)
lemma kickDistance (x:Cover)(e:Step): GDist ((s.kicks f) x*e.read (turns s A) x) ((s.kicks f) (x+e.vec))=GDist (f (s.slide x)*(e.rotate s.step).read A (s.slide x)) (f (s.slide x+(e.rotate s.step).vec)):=by unfold kicks; rw [next_point,ladder,←map_mul,polarCa]
lemma afoot_z (x:Cover)(e:Step): zone (e.used x) = span x (x+e.vec):=by rcases e with ⟨i,_|_⟩; rfl; simp only [zone,Step.used,Step.vec, ↓reduceIte,sub_add_cancel]; rw [spanComm]; rw [←sub_eq_add_neg]
lemma pair_eq(x:Cover)(e:Step):GDist (f x*e.read A x) (f (x+e.vec)) = GDist (f (e.used x).1 * A (e.used x)) (f ((e.used x).1+Lattice.step (e.used x).2)):=by
 rcases e with ⟨i,_|_⟩; rfl; simp only [Step.read,Step.used,Step.vec,↓reduceIte,sub_add_cancel]; rw [←sub_eq_add_neg]; let x':=x-Lattice.step i; let v:=A (x',i); change GDist (f x*v⁻¹) (f x')=GDist (f x'*v) (f x); rw [show f x=(f x*v⁻¹)*v by group, mul_inv_cancel_right]; unfold GDist; rw [bolt,dist_comm]
lemma spin_seal {X:Rooms}(p:Seal (s.follow X) A C f K): Seal X (turns s A) C (kicks s f) K:=by
 intro x i t; let e:=posDir i; let v:= e.rotate s.step; have h:zone (s.lane e x) ≤ s.follow X := by rw [lane_z]; exact (s.stride_le ..).2 t
 change GDist ((s.kicks f) x*e.read (turns s A) x) ((s.kicks f) (x+e.vec)) ≤_; rw [kickDistance,pair_eq]; exact p _ _ h
lemma spin_veil{X:Rooms}(p:Veil (s.follow X) A C f K): Veil X (turns s A) C (kicks s f) K:=by
 intro x i t; let e:=posDir i; let v:= e.rotate s.step; have h:Rooms.boundary (zone (s.lane e x)) (s.follow X) := by rw [lane_z]; exact ⟨(s.stride_le ..).2 t.1,fun q=> t.2 ((s.isInside ..).1 q)⟩
 change GDist ((s.kicks f) x*e.read (turns s A) x) ((s.kicks f) (x+e.vec)) ≤_; rw [kickDistance,pair_eq]; exact p _ _ h
lemma wellQuote{X:Rooms}: wellF (s.follow X) A C K ↔ wellF X (turns s A) C K:= ⟨fun ⟨f,v⟩=> ⟨_, spin_seal s A f v⟩, fun ⟨f,v⟩=>⟨_,by simpa only [turnBack] using spin_seal s⁻¹ (turns s A) f (C:=C) (K:=K) (X:=s.follow X) (by simpa only [foll_left] using v)⟩ ⟩
end March
end YM.CF.VolumeCape
