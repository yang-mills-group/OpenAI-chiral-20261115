import YM.CF.BProof.Floral.Myrtle
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll Hake Jet Push.AbsoluteSums Trees
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {ι J:Type*}
structure Wallet (S:J→Finset ι)(w:ι→ℝ)(Q:ι→ℝ→Prop)(c:ℝ):Prop where
 exec :∃ a:ι→ℝ,(∀ i,Q i (a i)) ∧ ∀ j,(∑ i∈S j, w i*a i)≤c
namespace Wallet
variable {S:J→Finset ι} {w:ι→ℝ}{Q R P:ι→ℝ→Prop}{a b:ℝ}
lemma mono(p:Wallet S w Q a)(t:a≤b):Wallet S w Q b:=by obtain ⟨i,v,h⟩:=p.exec; exact ⟨i,v,fun j=>(h j).trans t⟩
lemma serve(p:Wallet S w Q a)(t:∀ i b,Q i b→P i b):Wallet S w P a:=by obtain ⟨i,v,h⟩:=p.exec; exact ⟨i,fun x=>t _ _ (v _),h⟩
lemma cone(p:Wallet S w Q a)(u: Wallet S w R b)(v:∀ i a b,Q i a→ R i b → P i (a+b)):Wallet S w P (a+b):=by
 obtain ⟨i,k,h⟩:=p.exec; obtain ⟨j,g,q⟩:=u.exec; exact ⟨i+j,fun x=>v _ _ _ (k _) (g _),fun x=>by simp only [Pi.add_apply,mul_add,sum_add_distrib]; exact add_le_add (h x) (q x)⟩
lemma scale (p:Wallet S w Q a)(u:0≤b)(v:∀ i t,Q i t → P i (b*t)):Wallet S w P (b*a):=by
 obtain ⟨i,v',t⟩:=p.exec; exact ⟨fun x=>b*i x, fun x=> v _ _ (v' x),fun x=>by simp_rw [mul_left_comm _ b,← mul_sum]; exact mul_le_mul_of_nonneg_left (t x) u⟩
lemma widen {W:ι→ℝ}(p:Wallet S w Q a)(bnd:∀ i,W i≤w i)(t:∀ i a,Q i a→0≤a):Wallet S W Q a:=by
 obtain ⟨i,u,T⟩:=p.exec; exact ⟨i,u,fun j=>(sum_le_sum (fun x _=>mul_le_mul_of_nonneg_right (bnd x) (t _ _ (u x)))).trans (T j)⟩
variable (hw:∀ i,1≤w i)(p:Wallet S w Q a)(t:∀ i a,Q i a→0≤a)
include hw p t
lemma pos [Nonempty J]:0≤a:=by obtain ⟨i,u,v⟩:=p.exec; exact (sum_nonneg (fun j _=>mul_nonneg (zero_le_one.trans (hw j)) (t _ _ (u j)))).trans (v (Classical.arbitrary J))
lemma uniform (k:ι)(v: J)(g:k∈S v)(q:Monotone (Q k)):Q k a:=by
 obtain ⟨i,u,T⟩:=p.exec; apply q (le_trans ?_ (T v)) (u k); exact le_trans (le_mul_of_one_le_left (t _ _ (u k)) (hw k)) (single_le_sum (fun i _=> mul_nonneg (zero_le_one.trans (hw i)) (t _ _ (u i))) g)
omit hw p t
lemma rule [Nonempty J]{L:ℝ}{P:ι→ Cost L}(b:∀ i,0<w i)(g:∀ i, Rule (P i))(u:∀ i,∃ j,i∈ S j): Rule (fun x c=>Wallet S w (fun i=> P i x) c):= (Rule.tally S w P b g u).rose fun _ _ =>⟨fun p=>⟨p⟩,fun p=>p.exec⟩
end Wallet
variable {n:Side}{P:BudgetPoint}
private abbrev regsite (i:Seat n):= Finset.univ.filter fun y:Hub n=> i=y.val.1
private abbrev regw (P:BudgetPoint)(y:Hub n):= currency P.B P.supportExponent y.val.2
variable {h a b L:ℝ}
lemma reg_grade (p:1≤h){i:Hub n}{G:InkD n}(h: PressB P i G h a):0≤a:= (press_high h p 1 (ping_f P i.val.2) ∅).grade
lemma regcur (P:BudgetPoint)(i:Hub n): 1≤ regw P i:= Real.one_le_exp (mul_nonneg P.exponent_pos.le (Nat.cast_nonneg _))
abbrev Books (P:BudgetPoint)(F:RegBudget n)(h c:ℝ):= IncX (fun _=> False) F P h c
lemma bkiff {F:RegBudget n}: Books P F h a ↔ Wallet regsite (regw P) (fun i=> PressB P i (F i) h) a:=by
 constructor
 · intro p; obtain ⟨i,u,T⟩:=p.weight; refine ⟨i,u,fun x=>?_⟩; unfold regsite; rw [sum_filter]; exact T _
 intro p; obtain ⟨i,u,T⟩:=p.exec; refine ⟨⟨i,u,fun x=>?_⟩,fun _ s=>s.elim⟩; unfold regsite at T; simp_rw [sum_filter] at T; exact T x
namespace Books
variable {F G:RegBudget n}
lemma here (k:Books P F h a)(u:1≤h)(i:Hub n):PressB P i (F i) h a:= Wallet.uniform (regcur P) (bkiff.mp k) (fun _ _=>reg_grade u) i i.val.1 (mem_filter.mpr ⟨mem_univ _,rfl⟩) (fun _ _ h p=> regular_incr p h)
lemma mono (k:Books P F h a)(p:a≤b):Books P F h b:=bkiff.mpr ((bkiff.mp k).mono p)
lemma pos (k:Books P F h a)(p:1≤h):0≤a:=Wallet.pos (regcur P) (bkiff.mp k) (fun _ _=>reg_grade p)
lemma plus (k:Books P F h a)(v:Books P G h b):Books P (F+G) h (a+b):= bkiff.mpr ((bkiff.mp k).cone (bkiff.mp v) fun _ _ _=> regular_plus)
lemma σ (k:Books P F h a)(z:ℂ): Books P (z • F) h (‖z‖*a):= bkiff.mpr ((bkiff.mp k).scale (norm_nonneg z) fun _ _=> regular_scale z)
lemma sub (k:Books P F h a)(u:Books P G h b): Books P (F-G) h (a+b):=bkiff.mpr ((bkiff.mp k).cone (bkiff.mp u) fun _ _ _=> regular_sub)
lemma diff{F:ℂ→RegBudget n}(u:1<L)(k:1≤h)(v:∀ z∈disk L, Books P (F z) h a) (t:∀ i U,pingS P.threshold i.val.2 U→Hol (disk L) (fun z=>F z i U))(q:a/(L-1)≤b): Books P (F 1-F 0) h b:=by
 have ht:= @Wallet.rule (Hub n) (Seat n) regsite (regw P) _ L _ (fun i=>zero_lt_one.trans_le (regcur P i)) (fun i=> pea u k (fun z g=>here (v z g) k i) (t i)) (fun i=>⟨i.val.1,mem_filter.mpr ⟨mem_univ _,rfl⟩⟩)
 exact bkiff.mpr (ht.du u (fun i=> bkiff.mp (v i i.property)) q)
end Books
-- same tall money for Force including all touched
private abbrev fsite (i:Seat n):= Finset.univ.filter fun y:Force n=> i∈y.val.1.val.2
private abbrev fc (P:BudgetPoint)(y:Force n):=regw P y.val.1
abbrev Pressed (P:BudgetPoint)(F:ForceBudget n)(h c:ℝ):=Dark (fun _=>False) F P h c
lemma priff{F:ForceBudget n} : Pressed P F h a ↔ Wallet fsite (fc P) (fun i=>ForceB P i (F i) h) a:=by
 constructor
 · intro p; obtain ⟨i,v,w⟩:=p.weight; refine ⟨i,v,fun x=>?_⟩; unfold fsite; rw [sum_filter]; exact w x
 intro p; obtain ⟨i,v,t⟩:=p.exec; refine ⟨⟨i,v,fun x=>?_⟩,fun _ s=>s.elim⟩; unfold fsite at t; simp_rw [sum_filter] at t; exact t x
namespace Pressed
variable {F G:ForceBudget n}
lemma grade {E:Copy n}{i:Force n}(p:ForceB P i E h a)(k:1≤h):0≤a:= (force_high p k (1,Classical.arbitrary _) (ping_f P _) ∅).grade
lemma here (k:Pressed P F h a)(u:1≤h)(i:Force n):ForceB P i (F i) h a:= Wallet.uniform (w:=fc P) (fun (i:Force n)=>regcur P i.val.1) (priff.mp k) (fun _ _ v=>grade v u) i i.val.1.val.1 (mem_filter.mpr ⟨mem_univ _,i.val.1.property⟩) (fun _ _ h p=> force_incr p h)
lemma mono (k:Pressed P F h a)(p:a≤b):Pressed P F h b:=priff.mpr ((priff.mp k).mono p)
lemma pos (k:Pressed P F h a)(p:1≤h):0≤a:=Wallet.pos (w:=fc P) (fun (i:Force n)=>regcur P i.val.1) (priff.mp k) (fun _ _ k=>grade k p)
lemma plus (k:Pressed P F h a)(v:Pressed P G h b):Pressed P (F+G) h (a+b):= priff.mpr ((priff.mp k).cone (priff.mp v) fun _ _ _=> force_plus)
lemma σ (k:Pressed P F h a)(z:ℂ): Pressed P (z • F) h (‖z‖*a):= priff.mpr ((priff.mp k).scale (norm_nonneg z) fun _ _=> force_scale z)
lemma sub (k:Pressed P F h a)(u:Pressed P G h b): Pressed P (F-G) h (a+b):=priff.mpr ((priff.mp k).cone (priff.mp u) fun _ _ _=> force_sub)
lemma diff{F:ℂ→ ForceBudget n}(u:1<L)(k:1≤h)(v:∀ z∈disk L, Pressed P (F z) h a) (t:∀ (i:Force n)(U:Orbit n),pingS P.threshold (i.val.1.val.2\i.val.2) U.1→Hol (disk L) (fun z=>F z i U))(q:a/(L-1)≤b): Pressed P (F 1-F 0) h b:=by
 have ht:= @Wallet.rule (Force n) (Seat n) fsite (fc P) _ L _ (fun i=>zero_lt_one.trans_le (regcur P i.val.1)) (fun i=> silk u k (fun z g=>here (v z g) k i) (t i)) (fun i=>⟨i.val.1.val.1,mem_filter.mpr ⟨mem_univ _,i.val.1.property⟩⟩)
 exact priff.mpr (ht.du u (fun i=> priff.mp (v i i.property)) q)
end Pressed
end YM.CF.Floral
