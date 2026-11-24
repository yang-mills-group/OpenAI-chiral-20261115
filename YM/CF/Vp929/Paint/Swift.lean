import YM.CF.Vp929.Paint.Scene
import Mathlib.GroupTheory.Perm.Cycle.Basic
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Rooms Lattice
open scoped Classical
namespace Atlas
variable {r:ℕ}(x y:Scene r)
def Proper (x:Scene r) :Prop:=∀d:Jux r,∀ i, x.shade d i ≠ x.shade d (i+d.val.val)
local notation "N"=> spanR
local notation "R"=> N*r
abbrev rise(s:March):March:=⟨s.step,s.charge,N • s.endpt⟩
abbrev star(s:March):Arm:=⟨s.step,s.charge⟩
def Flow(s:March):Prop:=(∀d i,x.shade d i=y.shade (wr s.step r d) (s.slide i))∧∀ i,y.flag ((rise s).slide i)=star s*x.flag i
lemma around (s:March)(a b:Cover):s.slide (a+b)=s.slide a+s.step.act b:= by unfold March.slide; rw [Signed.act_add]; abel
lemma tell(x y:Cover)(p:Range r x y)(z:Cover):Range r (x+z) (y+z):=by intro i; simpa using p i
lemma rs (s:March)(a:Cover): (rise s).slide (N • a)=N • s.slide a:= by unfold March.slide; rw [nsmul_add]; congr 1; exact map_nsmul s.step.actEquiv spanR a
theorem meetsM (s:March)(a:Cover)(h: Flow x y s): code (survey x a)=code (survey y (s.slide a)):=by
 apply (readInk ..).2; refine ⟨star s,fun d i=>?_,fun i=>?_⟩
 · change x.shade d (a+i.val)= y.shade (wr s.step r d) (s.slide a+s.step.act i.val); rw [h.1, around]
 change y.flag (N • s.slide a + s.step.act i.val)=_; rw [← rs s,← around (rise s), h.2]; rfl
private lemma spine: ∀ s : Signed,s^N=1:= by unfold spanR; exact fun s=> pow_card_eq_one
private lemma sumHere (a:ℕ→Cover)(b:Cover)(c k:ℕ) (h:∀i:ℕ,i<c→ Range k b (a i)):Range (c*k) (c • b) (∑i∈Finset.range c,a i):=by
 induction c with
 | zero=>simp [Range.refl]
 | succ i ih=>
   let H:= ih (fun j t=> h j (by omega)); let S:=∑j∈Finset.range i,a j; rw [Nat.succ_mul,succ_nsmul, Finset.sum_range_succ]; apply Range.trans (tell _ _ H b); rw [add_comm S b, add_comm S (a i)]; apply tell; apply h i (by omega)
theorem proper_code (e:Proper x)(a b:Cover)(k:Range r a b)(h:code (survey x a)=code (survey x b)):a=b:=by
 obtain ⟨z,u,v⟩:= (readInk ..).1 h; let s:March:=⟨z.dir,z.charge,b-z.dir.act a⟩; have he:s.slide a=b:= add_sub_cancel ..; let w(i:ℕ):=(s^i).slide a; have W(i:ℕ): w (i+1)=s.slide (w i):=by unfold w; rw [pow_succ', March.trans]
 have V:w 0=a:=by simp [w]
 have U(i:ℕ):Range (i*r) a (w i):=by
    induction i with
    | zero=> rw [V]; apply Range.refl
    | succ i ih=> rw [W,Nat.succ_mul,Nat.add_comm]; exact Range.trans k (he ▸ s.range ih)
 have Z(i:ℕ)(h:i≤N): Range R a (w i):= (U i).mono (Nat.mul_le_mul_right r h)
 have E(i:ℕ)(p:i≤N) (d:Jux r): x.shade d (w i)=x.shade (wr s.step r d) (w (i+1)):=by
    let c:Zone R:=⟨w i-a,(art ..).2 (Z i p)⟩; have h:= u d c; change x.shade d (a+(w i-a)) = x.shade (wr s.step r d) (b+s.step.act (w i-a)) at h; rw [W]; rw [← he,← around, add_sub_cancel a (w i)] at h; exact h
 have E'(i:ℕ)(p:i≤N) (d:Jux r): x.shade d a=x.shade (wr (s.step^i) r d) (w i):=by induction i with | zero=> simp [V] | succ i ih=> rw [pow_succ', wr_m, ih (by omega),E i (by omega)]
 have T:w N=a:=by
    by_contra t; let d:Jux r:=⟨⟨w N-a, (art ..).2 (Z N le_rfl)⟩,sub_ne_zero.mpr t⟩; apply e d a; change _=x.shade d (a+(w N-a)); rw [add_sub_cancel a (w N), E' N le_rfl d, spine, wr_v]
 let t:=∑i∈Finset.range N,w i; have p : (rise s).slide t=t:=by
    change s.step.actEquiv t+ N • s.endpt=t; unfold t; rw [map_sum]; have vx:(∑i∈Finset.range N,(s.step.actEquiv (w i)+s.endpt))=∑i∈Finset.range N,w (i+1):= by apply Finset.sum_congr rfl; intro i _; exact (W i).symm
    rw [Finset.sum_add_distrib,Finset.sum_const, Finset.card_range] at vx; rw [vx]; apply add_right_cancel (b:=a); rw [← V, ← Finset.sum_range_succ',Finset.sum_range_succ, V,T]
 let f: Zone (N*R):=⟨t-N•a,(art ..).2 <| sumHere w a N R fun i h=> Z i h.le⟩; have q:= v f; change x.flag (N • b + s.step.act (t-N•a))=z*x.flag (N•a+(t-N•a)) at q; rw [← he,←rs s,← around (rise s),add_sub_cancel (N•a) t,p] at q
 have Z':z=1:= mul_right_cancel (b:= x.flag t) (q.symm.trans (one_mul _).symm); have s':s.step=1:= congrArg Arm.dir Z'; have G(i:ℕ): w i=a+i • s.endpt:=by induction i with | zero=> simp [V] | succ i ih=> rw [W,March.slide, s', Signed.act_one, ih, succ_nsmul, add_assoc]
 rw [G N] at T; have y:N • s.endpt=0:= add_eq_left.mp T
 obtain Y:= (smul_right_injective Cover span_pos.ne') (y.trans (smul_zero ..).symm); rw [← he,March.slide,s',Y,Signed.act_one,add_zero]
end Atlas
end YM.CF.VolumeCape
