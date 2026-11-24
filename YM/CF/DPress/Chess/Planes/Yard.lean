import YM.CF.DPress.Chess.Planes.Boot
-- integer grid tallies for the coarse gauge weight, fixed before Λ. Units of gauge links.
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Lattice Finset Laurent Spire Skye Scroll Lat Rush Wilson FD
open Cube (More assembly)
open scoped Topology BigOperators Classical
namespace Wall
variable (W:Wall){n:Side}(L:Side){μ:ℕ}
abbrev len(L:Side):ℤ:=2*(L.val:ℤ)
abbrev deed (n L:Side):Prop:=len L∣ n.val -- note coercion
lemma emb_ok (h:deed n L): len L∣ (More n).val:= by rw [show (More n).val=n.val*2 from rfl,Nat.cast_mul]; exact dvd_mul_of_dvd_left h _
lemma L_p : 0<len L:=by unfold len; have h:= L.property; positivity
abbrev fieldS(L:Side)(p:ℕ)(x:ℤ):Prop:= ∀ z:ℤ,(p:ℤ) ≤ |x-len L*z|
abbrev fort (p:ℕ)(x:Seat n):Prop:=∀ i:Axis,∀ z:ℤ,(z:Per _)= x i → fieldS L p z
lemma guardF(x z w:ℤ)(p:len L∣ z-x): fieldS L μ x↔ fieldS L μ z:=by
 have hp {a b j:ℤ}(p:len L∣ a-b)(u:fieldS L μ b) : (μ:ℤ)≤ |a-len L*j|:=by obtain ⟨k,p⟩:=p; rw [show a-len L*j=b-len L*(j-k) by rw [mul_sub]; omega]; exact u _
 exact ⟨fun u _=>hp p u,fun u _=>hp (by rw [←neg_sub]; exact dvd_neg.mpr p) u⟩
lemma incF (x y:ℤ)(k:len L∣x-y): fieldS L μ x↔fieldS L μ y:= (guardF L y x 0 k).symm
lemma negF(x:ℤ):fieldS L μ (-x)↔fieldS L μ x:=by
 have h{x:ℤ}(p:fieldS L μ x)(y:ℤ) : (μ:ℤ)≤ |-x-len L*y|:= by rw [show -x - len L*y= -(x-len L*(-y)) by rw [mul_neg]; abel,abs_neg]; exact p _
 exact ⟨fun p=>(by simpa only [neg_neg] using (show fieldS L μ (-(-x)) from fun y=> h p y)),fun p y=> h p y⟩
lemma weakF (x:Seat n)(h:deed n L) : fort L μ x ↔ ∀ i:Axis,fieldS L μ (natural x i):=by
 refine ⟨fun p i=> p i _ (congrFun (Rush.nat_true x) i),fun u i z p=>?_⟩; have h':((natural x i:ℤ):Per _)=x i:= congrFun (nat_true x) i; exact (incF L _ _ ((emb_ok L h).trans ((ZMod.intCast_eq_intCast_iff_dvd_sub ..).1 (p.trans h'.symm)))).1 (u i) -- divisibility sign? cast z = x ⇒ N|?
-- can fill window inside each 2L lattice cell
lemma mane {x:ℤ} (h:(μ:ℤ)≤x)(p:x+(μ:ℤ) ≤ len L) : fieldS L μ x:=by
 intro z; by_cases t:z≤0; · have ht:=mul_nonpos_of_nonneg_of_nonpos (L_p L).le t; exact le_trans (b:=x-len L*z) (by omega) (le_abs_self _)
 have hv:= Nat.cast_nonneg (α:=ℤ) μ; have ht:= le_mul_of_one_le_right (L_p L).le (by omega : 1 ≤ z); rw [abs_of_nonpos (by omega : x-_≤ 0)]; omega
lemma receipt (a:ℤ) (p:μ ≤ L.val) :∃ x:ℤ,x.natAbs ≤ μ ∧ fieldS L μ (a+x):=by
 let j:= a%len L; have h:= Int.emod_nonneg a (L_p L).ne'; have ht:= Int.emod_lt_of_pos a (L_p L); have he(k:ℤ)(t:fieldS L μ (j+k)):fieldS L μ (a+k):= (incF L _ _ ((by use -(a/len L); rw [mul_neg]; have hp: j+len L*(a/len L)=a:= Int.emod_add_mul_ediv ..; omega): len L ∣ j+k-(a+k))).mp t
 have hp:2*(μ:ℤ)≤len L:= by unfold len; omega
 by_cases u:j< μ; · exact ⟨(μ:ℤ)-j,(by change 0≤j at h; omega),he _ (mane L (by omega) (by omega))⟩
 change j<len L at ht; by_cases v:j+(μ:ℤ)≤len L; · exact ⟨0,by omega,he _ (mane L (by omega) (by omega))⟩
 exact ⟨len L-μ-j,by omega,he _ (mane L (by omega) (by omega))⟩
lemma flagsJ (x:Seat n)(g:deed n L)(h:μ≤ L.val): ∃ y: Seat n,fort L μ y ∧ separation x y ≤ μ:=by
 choose r p q using fun i:Axis=> receipt L (natural x i) h; let z:= wrap (More n) r; refine ⟨z+x,?_,?_⟩
 · have he(i):(((natural x i :ℤ)+r i:ℤ):Per (More n))=(z+x) i:=by rw [Int.cast_add,show ((natural x i:ℤ):Per _)=x i from congrFun (nat_true x) i]; exact add_comm (x i) _
   intro i t u; exact (incF L _ _ ((emb_ok L g).trans ((ZMod.intCast_eq_intCast_iff_dvd_sub ..).1 (u.trans (he i).symm)))).mp (q i) -- tune sign
 rw [separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le (box_test.mpr (by constructor <;> intro i <;> have h:=p i <;> omega))
-- s times coord blocks of λ. reflect-y remains fort.
abbrev gridOK {n:Side}(L:Side)(s:Sweep n):Prop:=∃ v:Cover,s.b=wrap n (L.val • v)
private lemma gradeS (g:deed n L)(s:Sweep n)(p:gridOK L s)(x:Seat n)(i:Axis) : fieldS L μ (natural x i)↔ fieldS L μ (natural (boxA s x) (s.s.perm i)):=by
 obtain ⟨k,p⟩:=p; let y:=natural x; let j:= s.s.perm i; let w:=s.s.act y+ ( (2:ℕ) • (L.val • k)); let a:=natural (boxA s x); have ht:wrap (More n) a=wrap _ w:=by rw [nat_true (boxA s x),sitA]; unfold w affine; rw [p,(assembly n).embed_wrap,show (assembly n).count.val=(2:ℕ) from rfl,map_add,←wrap_signed]; unfold y; rw [nat_true]
 have h:= incF (μ:=μ) L (w j) (a j) ((emb_ok L g).trans ((ZMod.intCast_eq_intCast_iff_dvd_sub (a j) (w j) (More n).val).1 (congrFun ht j))); -- tune
 change fieldS L μ (y i)↔ _; apply Iff.trans _ h; have he:w j=(if s.s.flip i then -(y i) else y i)+len L*(k j):=by
    simp only [w,j, Pi.add_apply,s.s.act_at, Pi.smul_apply,nsmul_eq_mul]; unfold len; norm_num; ring
 rw [he]; generalize e:s.s.flip i=t; cases t with
 | false=> simp only [Bool.false_eq_true, ite_false]; apply (incF L _ _ _).symm; rw [add_sub_cancel_left]; simp
 | true=> simp only [ite_true]; apply Iff.trans (negF L _).symm; apply (incF L _ _ _).symm; rw [add_sub_cancel_left]; exact dvd_mul_right _ _
lemma through (g:deed n L)(s:Sweep n)(p:gridOK L s)(x:Seat n):fort L μ (boxA s x)↔ fort L μ x:=by rw [weakF L _ g,weakF L _ g]; exact ⟨fun q i=>(gradeS L g s p x i).2 (q _), fun q i=>(by obtain ⟨i,rfl⟩:= s.s.perm.surjective i; exact (gradeS L g s p x i).1 (q i))⟩
end Wall
end YM.CF.DPress.Chess
