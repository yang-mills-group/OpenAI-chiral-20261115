import YM.CF.BProof.Half.Vantage
import YM.CF.BProof.Grid.Vertex
import YM.CF.BProof.Counter.Turn
import YM.CF.Ridge.Ply
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide.Mask
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Half
open Skye Taxi.Denn Py
section
variable {c n:Side}(B:Ratio c n) {r:ℕ}
abbrev valid(n:Side)(B: Ratio c n)(r:ℕ)(x:Per n):Prop:= ∃ y:Per c, ∃ a:ℕ,r ≤ a ∧ a+r≤ B.count.val ∧ base B y+a=x
theorem V_add {x:Per n}(h:valid n B r x)(z:Per c):valid n B r (x+base B z):= by obtain ⟨y,a,p,v,rfl⟩:=h; refine ⟨y+z,a,p,v,?_⟩; rw [base_add]; abel
lemma b_neg(x:Per c):base B (-x)= -base B x:=by refine eq_neg_of_add_eq_zero_left ?_; rw [← base_add,neg_add_cancel,base_zero]
lemma V_neg {x:Per n}(h:valid n B r x): valid n B r (-x):=by
 obtain ⟨y,a,p,v,rfl⟩:=h; refine ⟨-y+ -1,B.count.val-a,(by omega),(by omega),?_⟩; rw [base_add,b_neg,b_neg,base_one,Nat.cast_sub (show a≤ _ from by omega)]; abel
lemma near (x:Per n)(t:2*r ≤ B.count.val) : ∃ y: Per n,valid n B r y∧ delta1 n x y≤ r:=by
 let i:= BProof.block B x; let a:=part B x; let L:=B.count.val; let z:=max r (min a.val (L-r)); have h:a.val<L:=a.isLt; have hr:L=B.count.val:=rfl; have hx:base B i+a.val=x:=glue_block ..
 refine ⟨base B i+z,(by refine ⟨_,z,le_max_left ..,?_,rfl⟩; unfold z; omega),?_⟩
 let w:=base B i; change delta1 n x (w+(z:Per n)) ≤_; nth_rw 1 [←hx]; apply (Circle.δle (base B i+(a.val:Per n)) _ _).2; by_cases g:a.val≤ z
 · left; rw [offset_dist _ g (by have := count_le B; unfold z; omega)]; unfold z; omega -- t and potential z=L, hv even if r=0; prove
 right; rw [offset_dist _ (by omega) (by have:= count_le B; omega)]; unfold z; omega
abbrev warm (r:ℕ)(x:Site n):Prop:=∀ i,valid n B r (x i)
lemma validZ (F:Signed)(x:Site n){v:Site n}(h:warm B r v)(u:Site c): warm B r (affine F (B.embed u) v):=by
 intro i; rw [affine,Pi.add_apply,base_apply]; by_cases e:F.flip i; -- bool coercion? act def
 · apply V_add B; unfold Signed.act; -- uses inverse perm & flip may diff i! tune
   split; apply V_neg B (h _); apply h
 apply V_add B; unfold Signed.act; split; apply V_neg B (h _); apply h
lemma occurs {x: Site n} (p:2*r≤ B.count.val):∃ y: Site n, warm B r y∧ separation x y≤ r:=by
 choose y u t using fun i=> near B (x i) p; exact ⟨y,u,Grid.dist_le.mpr t⟩ -- separation defeq
end
variable {N L:Side}{r:ℕ} {R:Patch}
local notation "Λ"=>More N
-- Lift origin & negative qualification once periods chosen
lemma bill_r{c:Side}(B:Ratio c (More N))(p:B.count.val ∣ N.val){x: Seat N}(u:0<r)(v:warm B r x)(i:Axis): x∈ shade N i true r∪shade N i false r:=by
 obtain ⟨y,a,g,z,e⟩:=v i; have ht:x i=(base B y+a):=e.symm; let l:=(B.count.val); have hx: (x i).val=y.val*l+a:=ht ▸ subdiv_val B _ (show a<B.count.val from by omega) -- tune
 obtain ⟨L,h⟩:= p; have hy:N.val=L*l:=h.trans (mul_comm ..); have hv:0 < l:=B.count.property
 let J:= y.val*l; have he: (x i).val < (More N).val:= ZMod.val_lt (x i); have hs:=natM N; change a+r≤ l at z; apply mem_union.mpr; by_cases H:y.val<L
 · left; refine (shine i).2 ?_; have hL: y.val*l+l ≤ N.val:=by rw [← Nat.succ_mul,hy]; exact Nat.mul_le_mul_right _ H
   change r ≤ (x i).val∧(x i).val+r ≤ _; omega
 right; refine (shine i).2 ?_; change r ≤ (-x i).val∧(-x i).val+r≤ _; have hL:N.val≤ y.val*l:=hy ▸ Nat.mul_le_mul_right _ (by omega)
 have hw:y.val*l+l ≤ 2*N.val:=by rw [←Nat.succ_mul]; have ht:=Nat.mul_le_mul_right l (ZMod.val_lt y); have hz:=B.exact_size; rw [←hz, natM] at ht; omega
 have hh:(x i)≠0:=by intro h; rw [h,ZMod.val_zero] at hx; omega
 rw [ZMod.neg_val,if_neg hh]; omega
lemma motion_r {c:Side}(B:Ratio c (More N))(t:B.count.val=2*R.L.val)(s:Sweep N)(h:ply_U R.L 1 s)(x:Seat N): warm B r (boxA s x) ↔ warm B r x:=by
 obtain ⟨g,p⟩:=h; rw [pow_one] at p; let a:=R.L.val; set z:=(assembly N).embed s.b; have hx:z=B.embed (wrap c g):=by
    unfold z; rw [p,Ratio.embed_wrap,Ratio.embed_wrap,t,mul_smul]; rfl -- tune
 have hp(y:Seat N): boxA s y=affine s.s (B.embed (wrap c g)) y:= hx ▸ sitA ..
 rw [hp]; constructor; swap; · exact fun h=>validZ _ s.s x h _
 intro h; have hk:= validZ B s.s⁻¹ x h (-(s.s⁻¹.act (wrap c g))); rw [show affine s.s⁻¹ _ _ =x from ?_] at hk; exact hk
 unfold affine; rw [Signed.act_add,←Signed.act_mul,inv_mul_cancel,Signed.act_one,←Ratio.signed, ← Ratio.root_embed B, ← Ratio.root_embed B,map_neg]; abel
end YM.CF.BProof.Bide.Mask
