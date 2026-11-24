import YM.CF.BProof.Floral.Tolls
import YM.CF.Hype.Migrate
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll Jet Push.AbsoluteSums Trees
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{h a b c t L:ℝ}
abbrev HiveQ (W:Aura n→ℝ)(p:BudgetPoint)(a b:ℝ):Prop:=∀ i:Seat n,tallB W p.B a i ≤ b
abbrev honour (P:BudgetPoint)(a:ℝ)(Q:Aura n→ℝ→Prop) := Wallet (fun i:Seat n=>univ.filter fun y:Aura n=>i∈ y.val) (fun x=>currency P.B a x.val) Q
lemma beauty {Q:Aura n→ℝ→Prop}: honour P a Q b ↔ ∃ T:Aura n→ℝ,(∀ i,Q i (T i))∧ HiveQ T P a b :=by
 constructor
 · intro p; obtain ⟨i,v,t⟩:=p.exec; exact ⟨i,v,fun j=> by unfold tallB; simp_rw [mul_comm (i _)]; exact t j⟩
 rintro ⟨i,p,t⟩; refine ⟨i,p,fun j=>?_⟩; simp_rw [mul_comm (_:ℝ) (i _)]; exact t j
lemma honour_one(p:0≤a)(P:BudgetPoint)(i:Aura n):1≤ currency P.B a i.val:= Real.one_le_exp (mul_nonneg p (Nat.cast_nonneg _))
variable {Q:Aura n→ℝ→Prop}
namespace honour
lemma pos (v:honour P a Q b)(p:0≤a)(t:∀ i a,Q i a→0≤a):0≤b:= Wallet.pos (honour_one p P) v t
lemma here (v:honour P a Q b)(p:0≤a)(t:∀ i a,Q i a→0≤a)(h:∀ i,Monotone (Q i))(i:Aura n):Q i b:=by obtain ⟨j,g⟩:=i.property; exact Wallet.uniform (honour_one p P) v t i j (mem_filter.mpr ⟨mem_univ _,g⟩) (h i)
lemma widen (v:honour P a Q b)(p:t≤a)(u:∀ i a,Q i a→0≤a):honour P t Q b:= Wallet.widen v (fun i=>Real.exp_monotone (mul_le_mul_of_nonneg_right p (Nat.cast_nonneg _))) u
lemma rule (P:BudgetPoint)(a:ℝ){Q:Aura n→ Cost L}(t:∀ i,Rule (Q i)):Rule fun x c=> honour P a (fun i=> Q i x) c:= Wallet.rule (fun _=> Real.exp_pos _) t fun i=>by obtain ⟨j,h⟩:=i.property; exact ⟨j,mem_filter.mpr ⟨mem_univ _,h⟩⟩
end honour
abbrev Binder (P:BudgetPoint)(h a:ℝ)(F:Pax n):ℝ→Prop:=honour P a (fun i=> Medal P i.val ∅ (F i) h)
namespace Binder
variable {F G:Pax n}
lemma pos (v:Binder P h a F b)(p:0≤a)(k:0≤h):0≤b:=honour.pos v p fun _ _ s=>s.wage k
lemma here (v:Binder P h a F b)(p:0≤a)(k:0≤h)(i:Aura n):Medal P i.val ∅ (F i) h b:= honour.here v p (fun _ _ s=>s.wage k) (fun _ _ _ h p=>p.big h) i
lemma plus (v:Binder P h a F b)(t: Binder P h a G c):Binder P h a (F+G) (b+c):=v.cone t fun _ _ _=> Medal.plus
lemma sub (v:Binder P h a F b)(t: Binder P h a G c):Binder P h a (F-G) (b+c):=by rw [sub_eq_add_neg]; exact plus v (t.serve fun _ _ s=>s.negT)
lemma σ (v:Binder P h a F b)(z:ℂ):Binder P h a (z • F) (‖z‖*b):=v.scale (norm_nonneg z) fun _ _=> medal_scale z
lemma wide (v:Binder P h a F b)(p:t≤a)(u:0≤h):Binder P h t F b:= honour.widen v p fun _ _ s=> s.wage u
lemma diff {F:ℂ→ Pax n} (u:1<L)(k:1≤h)(v:∀ z∈disk L,Binder P h a (F z) b)(t:∀ i:Aura n,∀ U:Orbit n,pingS P.threshold i.val U.1→ Hol (disk L) (fun z=>F z i U))(p:0≤a)(q:b/(L-1)≤c): Binder P h a (F 1-F 0) c:=by
 have ht:= honour.rule P a (fun i=> medal_rule u k (fun z g=> here (v z g) p (zero_le_one.trans k) i) (fun U h=>t i U (by simpa using h)))
 exact ht.du u (fun i=> v i i.property) q
end Binder
abbrev leafP (P:BudgetPoint)(h:ℝ)(F:Cusp n)(i:Aura n)(c:ℝ):Prop:=0≤c ∧ ∀ D∈ fullD i, Medal P i.val D (F i D) h c
abbrev Heats(P:BudgetPoint)(h a:ℝ)(F:Cusp n):ℝ→Prop:= honour P a (leafP P h F)
namespace Heats
variable {F G:Cusp n}
lemma iff_anuk: Heats P h a F b ↔ ∃ T:Aura n→ℝ,Larch.Anuk F T P h ∧ HiveQ T P a b:=by
 unfold Heats; rw [beauty]; apply exists_congr; intro W; apply and_congr_left; intro p; constructor
 · intro v; exact ⟨fun i=>(v i).1,fun i D s t=> (v i).2 _ (mem_filter.mpr ⟨mem_univ _,s,t⟩)⟩
 intro p i; exact ⟨p.1 i,fun D v=> p.2 _ _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2⟩
lemma pos (v:Heats P h a F b)(p:0≤a):0≤b:=honour.pos v p fun _ _ s=>s.1
lemma here (v:Heats P h a F b)(p:0≤a)(i:Aura n)(D)(g:D∈ fullD i):Medal P i.val D (F i D) h b:= (honour.here v p (fun _ _ s=>s.1) (fun _ _ _ h s=> ⟨s.1.trans h,fun j v=>(s.2 j v).big h⟩) i).2 D g
lemma plus (v:Heats P h a F b)(t:Heats P h a G c):Heats P h a (F+G) (b+c):= v.cone t fun _ _ _ u v=>⟨add_nonneg u.1 v.1,fun D p=>(u.2 D p).plus (v.2 D p)⟩
lemma sub (v:Heats P h a F b)(t:Heats P h a G c):Heats P h a (F-G) (b+c):=by rw [sub_eq_add_neg]; exact plus v (t.serve fun _ _ v=>⟨v.1,fun D p=> (v.2 D p).negT⟩)
lemma σ (v:Heats P h a F b)(z:ℂ):Heats P h a (z • F) (‖z‖*b):= v.scale (norm_nonneg z) fun _ _ s=> ⟨mul_nonneg (norm_nonneg _) s.1,fun i e=> medal_scale z (s.2 i e)⟩
lemma diff {F:ℂ→ Cusp n} (u:1<L)(k:1≤h)(v:∀ z∈disk L,Heats P h a (F z) b)(t:∀ i:Aura n,∀ D∈fullD i,∀ U:Orbit n,pingS P.threshold (i.val\D) U.1→ Hol (disk L) (fun z=>F z i D U))(p:0≤a)(q:b/(L-1)≤c): Heats P h a (F 1-F 0) c:=by
 let Q(i:Aura n)(x:Points L):=leafP P h (pick F x) i
 have ht(i:Aura n):Rule (Q i):=by
    let f(D:Support (More n)):= fun z=>F z i D; have he(x:Points L)(D):pick F x i D=pick (f D) x:=by cases x <;> rfl
    refine (Rule.max_cost (fun D:fullD i=>medal_rule (F:=f D) u k (fun z g=>here (v z g) p i _ D.property) (t i _ D.property))).rose fun x c=> ?_
    unfold Q leafP; simp_rw [he]; exact and_congr Iff.rfl (by simp)
 exact (honour.rule P a ht).du u (fun i=> v i i.property) q
end Heats
end YM.CF.Floral
