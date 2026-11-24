import YM.CF.Palot.Pent
import YM.CF.Yaw.Flung
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Yaw
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
open Scion PetalP RG Push.AbsoluteSums.Trees
open scoped Classical
variable {ι:Type*}{I N:Type}{B:ℕ}{a δ γ:ℝ}
variable {n:Side} {L U: Support n}
local notation "K"=> Stilo.Harper (Site n)
local notation "K'"=> Track K ℝ
variable {W F:Track (Harper (Site n)) ℝ}
local notation "bay"=>Stilo.bay
def stampQ(n:Side) (T:ℕ)(a:ℝ) : Track (Stilo.Harper (Site n)) ℝ→ₗ[ℝ]ℝ:={toFun:=fun U=>∑ H:Stilo.Harper (Site n),currency T a (Stilo.bay H)*U H,map_add':=fun x y=> by simp [mul_add,sum_add_distrib], map_smul':=fun x y=>by dsimp; simp [mul_left_comm,mul_sum]}
lemma bloom_s(i:K)(x:ℝ):stampQ n B a (Pi.single i x)=currency B a (bay i)*x:=by change (∑ t:K,_)=_; rw [sum_eq_single i]; rw [Pi.single_eq_same]; intro j _ v; rw [Pi.single_eq_of_ne v,mul_zero]; simp
lemma stamp_nonneg(h:0≤W) : 0 ≤ stampQ n B a W:= sum_nonneg (fun i _=> mul_nonneg (Real.exp_pos _).le (h i))
structure Strung (X:Support n)(F:K')(B:ℕ)(a γ:ℝ):Prop where
 hand:0≤F
 spear i:F i ≠ 0→ X⊆ bay i∧i=beamH (bay i)
 pay:stampQ n B a F≤γ
structure KeepsP(X:Support n)(F:K')(B:ℕ)(a γ:ℝ) : Prop where
 high:0≤F
 roads i:F i ≠0→(i=⊥ ∨ (¬Disjoint X (bay i)∧ i=beamH (bay i)))
 tall : stampQ n B a F ≤ γ
lemma Strung.source(x:ℝ)(p:0≤x) : Strung U (Pi.single (beamH U) x) B a (currency B a U*x) :=by
 refine ⟨fun i=>?_,fun i v=>?_,?_⟩
 · rw [Pi.single_apply]; split_ifs; exact p; exact le_rfl
 · rw [Pi.single_apply] at v; split at v; next p'=> rw [p',bay_beam]; exact ⟨Subset.refl _,rfl⟩
   contradiction
 rw [bloom_s,bay_beam]
lemma incline_v(B:ℕ)(a:ℝ)(h:0≤a)(F:Support n):1 ≤ currency B a F:=Real.one_le_exp (by positivity)
lemma KeepsP.holds (h:KeepsP U W B a γ)(p: Strung U F B a δ)(l:0 ≤ a): Strung U (crank W F) B a (γ*δ):=by
 have he(i j:K)(x:W i ≠ 0)(y:F j≠0): U⊆ bay (i⊔j) ∧ i⊔j= beamH (bay (i⊔j)) ∧ currency B a (bay (i⊔j)) ≤ currency B a (bay i)*currency B a (bay j):=by
    obtain ⟨p,u⟩:=p.spear _ y; have ht:=h.roads _ x; rcases ht with rfl|⟨t,v⟩
    · rw [bot_sup_eq]; exact ⟨p,u,le_mul_of_one_le_left (Real.exp_pos _).le (incline_v B a l _)⟩
    have hx:¬Disjoint (bay i) (bay j):= fun r=> t (Disjoint.mono_left p r.symm)
    rw [joinsB]; refine ⟨p.trans subset_union_right, ?_,?_⟩
    · exact (congrArg₂ (· ⊔ ·) v u).trans (boundH _ _ hx)
    obtain ⟨u,p,h⟩:=Finset.not_disjoint_iff.mp hx; unfold Push.AbsoluteSums.Trees.currency; rw [←Real.exp_add,←mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast Corona.meets_sum p h B) l)
 refine ⟨crank_s W F h.high p.hand,fun i f=>?_,?_⟩ -- tune
 · unfold crank Stilo.coal at f; simp only [Finset.sum_apply] at f; obtain ⟨j,w,y⟩:= exists_ne_zero_of_sum_ne_zero f; obtain ⟨v,u,t⟩:= exists_ne_zero_of_sum_ne_zero y; rw [Pi.single_apply] at t; split at t; swap; contradiction
   next k => rw [k]; exact ⟨(he j v (left_ne_zero_of_mul t) (right_ne_zero_of_mul t)).1,(he j v (left_ne_zero_of_mul t) (right_ne_zero_of_mul t)).2.1⟩
 have hp:0≤ stampQ n B a W:= stamp_nonneg h.high; have ht:0≤ stampQ n B a F:=stamp_nonneg p.hand; apply le_trans _ (mul_le_mul h.tall p.pay ht (hp.trans h.tall)); change stampQ _ _ _ _≤ (∑ i,currency B a (bay i)*W i)*∑ i,currency B a (bay i)* F i
 unfold crank Stilo.coal; rw [sum_mul_sum]; simp_rw [map_sum,bloom_s]; apply sum_le_sum; intro i _; apply sum_le_sum; intro j _; by_cases p':W i=0; · simp [p']
 by_cases h': F j=0; · simp [h']
 exact (mul_le_mul_of_nonneg_right (he i j p' h').2.2 (mul_nonneg (h.high _) (p.hand _))).trans (by rw [mul_mul_mul_comm])
lemma Strung.plus_l(h:Strung U W B a γ)(p: Strung U F B a δ): Strung U (W+F) B a (γ+δ):=by
 refine ⟨add_nonneg h.hand p.hand,fun i f=>?_,?_⟩; by_cases g:W i=0; exact p.spear i (fun u=> f (by simp [g,u])); exact h.spear i g; rw [map_add]; exact add_le_add h.pay p.pay -- tune semis
lemma Strung.zero_l : Strung (n:=n) U 0 B a 0:=⟨le_rfl,fun _ p=> (p rfl).elim,(map_zero _).le⟩
lemma Strung.woven{X:ι→K'}{S:Finset ι}{D:ι→ℝ}(p:∀ i∈ S,Strung U (X i) B a (D i)):Strung U (∑ i∈S,X i) B a (∑ i∈S,D i):=by induction S using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact Strung.zero_l| insert i S h ih=> rw [sum_insert h,sum_insert h]; exact (p _ (mem_insert_self ..)).plus_l (ih fun i v=> p i (mem_insert_of_mem v))
lemma Strung.linear (p:Strung U W B a γ){d:ℝ}(h:0≤d): Strung U (d • W) B a (d*γ):=⟨smul_nonneg h p.hand,fun i f => p.spear i (right_ne_zero_of_mul (show d* W i ≠0 from f)),by rw [map_smul]; exact mul_le_mul_of_nonneg_left p.pay h⟩
lemma KeepsP.throne(L:List I)(E:I→K')(D:I→ℝ)(H:∀ i∈ L,KeepsP U (E i) B a (D i))(p:Strung U F B a δ)(v:0≤a): Strung U (crank (payH E L) F) B a ((L.map D).prod*δ) :=by
 induction L with
 | nil=> rw [show payH E []=ownH ℝ K from rfl,crank_L,List.map_nil,List.prod_nil,one_mul]; exact p
 | cons i l ih=> rw [List.map_cons,List.prod_cons,mul_assoc,show payH E (i::l)=crank (E i) (payH E l) from rfl,crank_A]; exact (H i (List.mem_cons_self ..)).holds (ih fun i w=> H _ (List.mem_cons_of_mem _ w)) v
lemma KeepsP.stock(V:PetalP I)(ZH:I→Track (Harper (Site n)) ℝ)(D:I→ℝ)(p:0≤V.led)(u:∀ i:V.slots,V.led i≠0 →∀ j∈ V.roll i,KeepsP U (ZH j) B a (D j))(h:Strung U F B a γ)(v:0≤a): Strung U (crank (V.share ZH) F) B a ((∑ i:V.slots,V.led i *((V.roll i).map D).prod)*γ):=by -- capital ZH collision
 unfold share; rw [ray_s,sum_mul]; apply Strung.woven; intro i _; rw [ray_p,mul_assoc]; by_cases p':V.led i=0; · rw [p',zero_smul,zero_mul]; exact Strung.zero_l
 exact (throne (V.roll i) ZH D (u i p') h v).linear (p i)
end YM.CF.Yaw
