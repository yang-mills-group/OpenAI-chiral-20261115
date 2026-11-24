import YM.CF.BProof.Floral.Money
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floral
open Function NormedSpace Filter Metric Lattice Wilson Finset MeasureTheory RG Fock
open Tenant Vow Pastry Skye Scree Cube Mew Spire Tulip Scroll Hake Jet
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{X D Y:Support (More n)}{U:Pane n}{f:ℂ→Pane n→ℂ}{F:ℂ→ Copy n}{a b h L:ℝ}
lemma medal_scale (z:ℂ){F:Copy n}(v:Medal P X D F h a): Medal P X D (z • F) h (‖z‖*a):=by
 obtain ⟨V,A,g,t,u⟩:=v
 refine ⟨⟨fun i j v g=>congrArg (z • ·) (V.same i j v g),fun i=>(V.lit i).smul z,V.keeps.const_smul z,fun i j=>(congrArg (z • ·) (V.gaugeX i j)).trans (map_smul (hueV (tradew n j)) z _).symm⟩,‖z‖ • A,fun i=>mul_nonneg (norm_nonneg _) (g i),fun i w _ y=>⟨Eventually.of_forall fun _=>(fineShape _).allP,fun j=> Pence.σ z ((t i w y).haveP j)⟩,?_⟩
 unfold joinV; simp_rw [Pi.smul_apply,smul_eq_mul,mul_left_comm _ ‖z‖,←mul_sum]; exact mul_le_mul_of_nonneg_left u (norm_nonneg _)
lemma pence_le {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{k:ℕ}{K:E→ℂ}{x:E}(v:Pence k K x a)(h:a≤b):Pence k K x b:= ⟨v.smooth,v.earned.trans h⟩
lemma medal_p {F:Copy n}(p:Medal P X D F h a)(k:1≤h)(U:Orbit n)(u:pingS P.threshold (X\D) U.1)(g:D ⊆ Y)(z:Finset (Dwell n)): Pence P.order (fun i=> chipV z (F (pressQ P Y U.1 i,U.2))) 0 a:=by
 obtain ⟨T,b,h,f⟩:=p.pays; exact pence_le ((h U u g).haveP z) ((le_mul_of_one_le_left (b z) (one_le_pow₀ k)).trans ((single_le_sum (fun j _=>mul_nonneg (pow_nonneg (zero_le_one.trans k) j.card) (b j)) (mem_univ z)).trans f))
lemma iter_rule {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F:ℂ→ E→ℂ}{j:ℕ}(z:E) (u:1<L)(H:∀ v:Fin j→E,Hol (disk L) fun x=>iteratedFDeriv ℝ j (F x) z v)(w:∀ v∈disk L, ContDiffAt ℝ (j:WithTop ℕ∞) (F v) z): Rule fun (x:Points L) c=>‖iteratedFDeriv ℝ j (pick F x) z‖ ≤ c :=by
 let a(v:Fin j→E):ℝ:= ∏ i, ‖v i‖; let V:= {v:Fin j→E// 0<a v}; let Q(v:V)(x:Points L)(c:ℝ):= ‖iteratedFDeriv ℝ j (pick F x) z v.val‖ ≤ c*a v.val
 have h(v:V):Rule (Q v):=by
    have he:= v.property
    refine ((Rule.solo (H v.val)).coin (a v.val)⁻¹ (inv_pos.mpr he)).rose ?_
    intro x c; rw [iter_pup u x z w]; constructor
    · rintro ⟨i,p,w⟩; exact p.trans (by simpa only [Q,mul_comm] using (inv_mul_le_iff₀ he).mp w) -- simp mul_comm tone
    intro p; exact ⟨_,p,(inv_mul_le_iff₀ he).mpr (by rw [mul_comm])⟩
 refine (Rule.max_cost h).rose fun x c=> ⟨fun ⟨k,p⟩=>ContinuousMultilinearMap.opNorm_le_bound k (fun v=>?_ ),fun p=>⟨(norm_nonneg _).trans p,fun v=> ContinuousMultilinearMap.le_of_opNorm_le p v.val ⟩⟩
 by_cases g:0<a v; exact p ⟨v,g⟩; have hk:a v=0:= le_antisymm (le_of_not_gt g) (prod_nonneg fun i _=> norm_nonneg _); change _ ≤ c*a v; have hy:= ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ j (pick F x) z) v; change _ ≤ _*a v at hy; simpa only [hk,mul_zero] using hy
variable (u:1<L)
include u
lemma pence_rule (H:∀ U:Pane n,pingS P.threshold (X\D) U → Hol (disk L) (fun z=> f z U))(w:∀ U:Pane n,pingS P.threshold (X\D) U →∀ z∈disk L,Pence P.order (fun i=> f z (pressQ P Y U i)) 0 a)(p:pingS P.threshold (X\D) U): Rule fun (x:Points L) c=> Pence P.order (pick (fun z i=> f z (pressQ P Y U i)) x) 0 c :=by
 let F(z:ℂ)(i:tangD n):= f z (pressQ P Y U i); obtain ⟨K,v,I⟩:= reach_p (Y:=Y) p
 obtain ⟨r,hr,h⟩:= Metric.mem_nhds_iff.mp (show _∈_ from I.and (Vow.tick (Y:=Y) p)) -- tune
 let M(i:ℕ)(x:Points L):= iteratedFDeriv ℝ i (pick F x) 0
 let B:= Finset.range (P.order+1); let a'(i:ℕ):=(1:ℝ)^i/i.factorial
 have hb(i:ℕ)(s:i∈B):Rule fun (x:Points L) c=> ‖M i x‖≤c:=by
    have hl:i≤P.order:= Nat.le_of_lt_succ (mem_range.mp s)
    exact iter_rule _ u (fun v=>hol_iterated F isOpen_ball isOpen_ball (fun x hx=> H _ (h hx).2) (C:=K*a) (fun x hx z hz=>(h hx).1 _ a fun V u=> w V u z hz) hl _ (mem_ball_self hr) v) (fun z hz=> (w U p z hz).smooth.of_le (by exact_mod_cast hl))
 have he(x:Points L):ContDiffAt ℝ (P.order:WithTop ℕ∞) (pick F x) 0:= match x with 
     | none=> (w U p _ (d1 u)).smooth.sub (w U p _ (d0 u)).smooth 
     | some i=> (w U p _ i.property).smooth
 have hv(i):0<a' i:=by unfold a'; positivity
 refine (Rule.sigma B a' (fun i (x:Points L) c=> ‖M i x‖ ≤ c) (fun i _=>hv i) hb).rose fun x c=> ⟨fun ⟨b,g,t⟩=> ⟨he x,(sum_le_sum (f:=fun j=> a' j *‖M j x‖) (fun j h=>mul_le_mul_of_nonneg_left (g j h) (hv j).le)).trans t⟩, fun q=> ⟨fun j=>‖M j x‖,fun _ _=>le_rfl,q.earned⟩⟩
lemma medal_rule (k:1≤h)(T:∀ z∈disk L,Medal P X D (F z) h a)(H:∀ U:Orbit n,pingS P.threshold (X\D) U.1→ Hol (disk L) fun z=> F z U): Rule fun (x:Points L) c=> Medal P X D (pick F x) h c:=by
 let V:=Finset (Dwell n); let S:= {z:Orbit n × Support (More n)// pingS P.threshold (X\D) z.1.1 ∧ D ⊆ z.2}
 let f(i:V)(x:Points L)(z:S)(t:tangD n):= chipV i (pick F x (pressQ P z.val.2 z.val.1.1 t,z.val.1.2)); let Q(i:V)(x:Points L)(c:ℝ):= 0≤c ∧ ∀ j:S,Pence P.order (f i x j) 0 c
 have ht(i:V): Rule (Q i):=by
    refine Rule.max_cost (F:=fun j (x:Points L) c=>Pence P.order (f i x j) 0 c) fun j=>?_ -- note max_cost pattern
    let g(z)(t:Pane n):= chipV i (F z (t,j.val.1.2)); have he(x):f i x j=pick (fun z i=> g z (pressQ P j.val.2 j.val.1.1 i)) x:=by cases x <;> rfl
    simp_rw [he]; exact pence_rule u (fun y h'=> (chipV i).differentiable.comp_differentiableOn (H (y,j.val.1.2) h')) (fun y k' z v=> medal_p (T z v) k (y,j.val.1.2) k' j.property.2 i) j.property.1
 refine (Rule.sigma Finset.univ (fun i:V=> h^i.card) Q (fun i _=> pow_pos (zero_lt_one.trans_le k) _) (fun i _=> ht i)).rose fun x c=> ?_
 have w: ∃ a, Medal P X D (pick F x) h a:= match x with | none=>⟨a+a,(show Medal P X D (F 1-F 0) h _ from by rw [sub_eq_add_neg]; exact (T _ (d1 u)).plus (Medal.negT (T _ (d0 u))))⟩ | some i=>⟨_,T i i.property⟩ -- choose a+a
 constructor
 · rintro ⟨b,v,t⟩; exact ⟨w.choose_spec.toThemeR,b,fun i=>(v i (mem_univ _)).1,fun y hy Y k=> ⟨Eventually.of_forall fun _=>(fineShape _).allP,fun i=> (v i (mem_univ i)).2 ⟨(y,Y),hy,k⟩⟩, t⟩
 intro p; obtain ⟨b,v,w,t⟩:=p.pays; exact ⟨b,fun i _=> ⟨v i,fun j=> (w j.val.1 j.property.1 j.property.2).haveP i⟩,t⟩
end YM.CF.Floral
