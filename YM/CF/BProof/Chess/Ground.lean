import YM.CF.BProof.Transit.Orel
import YM.CF.BProof.Half.Aspect
import YM.CF.Ridge.Ply
import YM.CF.BProof.Strip
/-! Frame at fixed letter lattice. We use gauge plane grid `field L 1` for starts. Our
`span` is oriented including points on left at cover pitch w and right at ≤ field-w.
All access w/ strict boundary gap; if this set is empty unit is still an Allowed mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Chess
open Function Filter Metric NormedSpace Finset Lattice Cube Bide Spire Bide.Town Bide.Half RG Fock Lat Skye Scree
open scoped Matrix.Norms.L2Operator Matrix Topology BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
variable (N L:Side)(i:Axis){s t h z w:ℕ}
def pace (k:ℕ):Site N := (L.val*k) • (Lattice.step i:Site N)
def drive(k:ℕ): Sweep N:= forward (-(pace N L i k))
abbrev field (L: Side) (k:ℕ):=2* (L.val * k)
lemma ply(k:ℕ): Py.ply_U L 1 (drive N L i k):=⟨ -(k • Lattice.step i), by rw [pow_one]; unfold drive forward pace; dsimp only; rw [mul_smul]; rw [smul_neg, map_neg,map_nsmul,map_nsmul,wrap_step]⟩
lemma pace_i(k:ℕ): (assembly N).embed (pace N L i k)=field L k • (Lattice.step i:Seat N):=by unfold pace; rw [←wrap_step N i,← map_nsmul, Ratio.embed_wrap,map_nsmul,map_nsmul,wrap_step,field,show (assembly N).count.val = 2 from rfl]; simp only [mul_smul]
lemma drive_i(x:Seat N) : boxA (drive N L i s) x i=x i-field L s:=by
 rw [sitA]; change (Signed.act 1 x+(assembly N).root (-pace N L i s)) i=_; rw [Signed.act_one,map_neg,Ratio.root_embed,pace_i]; simp [sub_eq_add_neg]
lemma mTor : (Fixed.reflectSweep N i)*Fixed.reflectSweep N i=1:=by nth_rw 1 [←Fixed.inv_reflectSweep i]; rw [inv_mul_cancel]; -- `Fixed` shape
lemma pace_add(a b:ℕ): pace N L i (a+b)=pace N L i a+ pace N L i b:=by simp [pace,mul_add,add_smul]
lemma drive_roll(a b:ℕ): drive N L i a*drive N L i b = drive N L i (a+b):=by change Sweep.mk (1*1) (_+Signed.act 1 _) _=_; simp only [one_mul,Signed.act_one,drive,pace_add,forward]; rw [neg_add]; rfl
lemma drive₀ : drive N L i 0=1:=by simp [drive,pace,forward]; rfl -- tune length
abbrev home (L:Side)(s:ℕ)(N:Side):Prop:=field L s=(More N).val
lemma honest (u:home L s N): pace N L i s=0:=by
 have he:= natM N; unfold home field at u; unfold pace; rw [show L.val*s=N.val from by omega]; ext k; simp only [Pi.smul_apply,nsmul_eq_mul,ZMod.natCast_self, zero_mul, Pi.zero_apply]
lemma homeP (u:home L s N): drive N L i s=1:=by rw [drive,honest N L i u,neg_zero]; rfl
lemma heel(a:ℕ): drive N L i a * Fixed.reflectSweep N i = Fixed.reflectSweep N i *(drive N L i a)⁻¹ := by
 unfold drive; rw [Town.inv_s]; let s:=Signed.mirror i; let x:=pace N L i a; have hx:s.act x=(-x):= by ext j; by_cases h:j=i <;> simp [s,Signed.act,Signed.mirror,h,x,pace] -- tune
 change Sweep.mk (1*s) ((-x)+Signed.act 1 0) false = Sweep.mk (s*1) (0+s.act (- -x)) false; rw [one_mul,mul_one,Signed.act_one,add_zero,zero_add,neg_neg,hx]
-- Open plane neighborhoods of radius w (level chosen positive), at same offset.
def span (s w:ℕ): Finset (Seat N):=univ.filter fun y=>∃ a:ℕ,w≤a∧a+w≤field L s∧ y i = a
lemma spans {x:Seat N}:x∈span N L i s w↔ ∃ a:ℕ,w≤a∧a+w≤field L s∧x i=a:=by simp [span]
lemma field_add(a b:ℕ): field L (a+b)=field L a+field L b:=by simp [field,mul_add]
lemma front(b:ℕ): span N L i s w⊆ span N L i (s+b) w:=fun x y=> let ⟨a,p,v,t⟩:=(spans N L i).1 y; (spans N L i).2 ⟨a,p,(by rw [field_add]; omega), t⟩
lemma behind (x:Seat N)(u:x∈ regionD (drive N L i s) (span N L i t w)):∃ a:ℕ,w ≤ a∧ a+w ≤ field L t ∧ x i= (field L s+a:ℕ):=by
 have ht:boxA (drive N L i s) x∈ span N L i t w:= by simpa only [regionD, Finset.mem_map_equiv,Equiv.symm_symm] using u
 obtain ⟨a,p,v,h⟩:=(spans N L i).1 ht; refine ⟨a,p,v,?_⟩; rw [drive_i] at h; simpa [Nat.cast_add,eq_sub_iff_add_eq, add_comm] using sub_eq_iff_eq_add.mp h
lemma back : regionD (drive N L i s) (span N L i t w)⊆ span N L i (s+t) w:=fun _ e=> let ⟨a,p,v,t⟩:= behind N L i _ e; (spans N L i).2 ⟨_,by omega,by rw [field_add]; omega,t⟩ -- `_all` infer tune
lemma circular(a b:ℕ)(p:field L (a+b)≤ (More N).val)(h:0<w) : Disjoint (span N L i a w) (regionD (drive N L i a) (span N L i b w)):=by
 refine Finset.disjoint_left.mpr (fun x y z=>?_); obtain ⟨u,p1,k,g⟩:=(spans N L i).1 y; obtain ⟨t,b1,s,f⟩:=behind N L i _ z
 have he:=congrArg ZMod.val (g.symm.trans f); rw [field_add] at p; rw [ZMod.val_natCast_of_lt (show u < _ from by omega), ZMod.val_natCast_of_lt (show field L a+t<_ from by omega)] at he; omega
lemma spin(a:ℕ): regionD (drive N L i a) (regionD (Fixed.reflectSweep N i) (span N L i a w)) ⊆ span N L i a w:=by
 intro x h; simp only [regionD,Finset.mem_map_equiv,Equiv.symm_symm] at h; obtain ⟨b,p,v,t⟩:=(spans N L i).1 h; apply (spans N L i).2; refine ⟨field L a-b,(by omega),(by omega),?_⟩; rw [Fixed.box_reflect,show (Signed.mirror i).act (boxA (drive N L i a) x) i= -(x i-field L a) from ?_] at t -- tune
 · have ht:=t; clear t; rw [Nat.cast_sub (by omega), ← ht]; -- subtract? `- (x_i-field a)` yes
   abel
 rw [show (Signed.mirror i).act (boxA (drive N L i a) x) i= -(boxA (drive N L i a) x i) by simp [Signed.act,Signed.mirror]]; rw [drive_i]
lemma stretch (p:field L s=N.val): span N L i s w ⊆ shade N i true w:=by
 intro x h; obtain ⟨b,v,t,y⟩:=(spans N L i).1 h; apply (shine i).2; change w≤ (x i).val ∧ (x i).val+w ≤ _; rw [y,ZMod.val_natCast_of_lt (by have :=natM N; have ht:0 < N.val :=N.property; omega)]; exact ⟨v,t.trans_eq p⟩
end YM.CF.BProof.Chess
