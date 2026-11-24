import YM.CF.BProof.Floral.Vixen
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll Jet Push.AbsoluteSums Trees
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{h a b c t L:ℝ}{F G:Cusp n}
def Bud (P: BudgetPoint)(F:Cusp n)(i:Aura n)(h b:ℝ):Prop:=∃ v:Support (More n)→ℝ,(∀ D∈ fullD i, Medal P i.val D (F i D) h (v D)) ∧ (∑ D∈fullD i,v D)≤b
abbrev Flaws (P:BudgetPoint)(h a:ℝ)(F:Cusp n):ℝ→Prop:= honour P a (fun i=> Bud P F i h)
namespace Flaws
abbrev Dued (F:Cusp n)(T:Aura n→ Support (More n)→ℝ)(i:Aura n)(P:BudgetPoint)(h:ℝ): Prop:=∀ D∈ fullD i,Medal P i.val D (F i D) h (T i D)
lemma give:Flaws P h a F b ↔ ∃ T:Aura n→ Support (More n)→ℝ,(∀ i,Dued F T i P h)∧ HiveQ (Vow.hymn T) P a b:=by -- due abbrev insert
 unfold Flaws; rw [beauty]; constructor
 · rintro ⟨i,v,w⟩; choose T l m using v; exact ⟨T,l,fun x=>(sum_le_sum fun i v'=>mul_le_mul_of_nonneg_right (m i) (Real.exp_pos _).le).trans (w x)⟩
 rintro ⟨i,u,h⟩; exact ⟨_,fun j=> ⟨i j,u j,le_rfl⟩,h⟩
lemma bud_b (p:0≤h){i:Aura n}(q:Bud P F i h b):0≤b:=by obtain ⟨i,g,v⟩:=q; exact (sum_nonneg fun _ l=>(g _ l).wage p).trans v
lemma pos (v:Flaws P h a F b)(u:0 ≤h)(p:0≤a):0≤b:=honour.pos v p fun i _=> bud_b (i:=i) u
lemma here (v:Flaws P h a F b)(u:0≤h)(p:0≤a)(i:Aura n)(D)(w:D∈fullD i) : Medal P i.val D (F i D) h b:=by
 have he:= honour.here v p (fun i _=>bud_b (i:=i) u) (fun i a b p s=>by obtain ⟨t,h,g⟩:=s; exact ⟨t,h,g.trans p⟩) i; obtain ⟨c,v,t⟩:=he; exact (v D w).big ((single_le_sum (fun j k=>(v j k).wage u) w).trans t)
lemma plus (v:Flaws P h a F b)(t: Flaws P h a G c): Flaws P h a (F+G) (b+c):=by
 refine Wallet.cone v t fun i j k ⟨A,g,u⟩ ⟨B,l,w⟩=> ⟨A+B,fun D k=>(g D k).plus (l D k),?_⟩; simp only [Pi.add_apply,sum_add_distrib]; exact add_le_add u w
lemma σ (v:Flaws P h a F b)(z:ℂ): Flaws P h a (z • F) (‖z‖*b):= by
 refine Wallet.scale v (norm_nonneg z) fun i b ⟨A,p,u⟩=> ⟨‖z‖ • A, fun D k=>medal_scale z (p D k),?_⟩; simp only [Pi.smul_apply,smul_eq_mul,←mul_sum]; exact mul_le_mul_of_nonneg_left u (norm_nonneg _) 
lemma sub (v:Flaws P h a F b)(t: Flaws P h a G c): Flaws P h a (F-G) (b+c):= by simpa [sub_eq_add_neg] using plus v (σ t (-1:ℂ))
lemma wide (v:Flaws P h a F b)(p:t≤a)(u:0≤h): Flaws P h t F b:= honour.widen v p fun _ _ s=> bud_b u s
lemma diff {F:ℂ→ Cusp n} (u:1<L)(k:1≤h)(v:∀ z∈disk L,Flaws P h a (F z) b)(t:∀ i:Aura n,∀ D∈fullD i,∀ U:Orbit n,pingS P.threshold (i.val\D) U.1→ Hol (disk L) (fun z=>F z i D U))(p:0≤a)(q:b/(L-1)≤c): Flaws P h a (F 1-F 0) c:=by
 let Q(i:Aura n)(x:Points L):=Bud P (pick F x) i h
 have ht(i:Aura n):Rule (Q i):=by
    let f(D:Support (More n)):= fun z=>F z i D; have he(x:Points L)(D):pick F x i D=pick (f D) x:=by cases x <;> rfl
    refine (Rule.sigma (fullD i) (fun _=>1) (fun D (x:Points L)=> Medal P i.val D (pick (f D) x) h) (fun _ _=> zero_lt_one) fun D g=>medal_rule (F:=f D) u k (fun z l=>here (v z l) (zero_le_one.trans k) p i D g) (t i D g)).rose fun x c=> ?_
    unfold Q Bud; simp_rw [he]; simp only [lab,one_mul]
 exact (honour.rule P a ht).du u (fun i=> v i i.property) q
lemma full_mem {D:Support (More n)}{i:Aura n}:D∈fullD i ↔ D.Nonempty∧ D⊆i.val:=by simp [fullD]
end Flaws
end YM.CF.Floral
