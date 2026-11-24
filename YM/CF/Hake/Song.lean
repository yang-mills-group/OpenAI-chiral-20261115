import YM.CF.Hake.Ply
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f g:E→ℂ}{x:E}{k:ℕ}{a:ℝ}
lemma nob_q (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):noble a k (fun x=> f x * g x) x≤∑ i∈range (k+1), noble a i f x*noble a (k-i) g x:=by
 obtain ⟨U,hU,i,t⟩:= open_patch l; obtain ⟨V,hV,j,p⟩:=open_patch s
 have hw:=i.inter j; have hx:x∈U∩V:= ⟨hU,hV⟩; have ht:=norm_iteratedFDerivWithin_mul_le (t.mono Set.inter_subset_left) (p.mono Set.inter_subset_right) hw.uniqueDiffOn hx (n:=k) le_rfl
 simp_rw [iteratedFDerivWithin_of_isOpen _ hw hx] at ht
 unfold noble
 calc
   _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)
   _ = _:=by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      have hi := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      let j := k-i
      have hh : (k.factorial:ℝ)=k.choose i*i.factorial*j.factorial := by exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi).symm
      rw [show a^k=a^i*a^j by rw [←pow_add]; exact congrArg _ (by unfold j; omega),hh]
      have hr: 0<(k.choose i:ℝ):= Nat.cast_pos.mpr (Nat.choose_pos hi)
      unfold j at *; field_simp
lemma pot_q (h:0≤a)(l:ContDiffAt ℝ (↑k:WithTop ℕ∞) f x)(s:ContDiffAt ℝ (↑k:WithTop ℕ∞) g x):potash a k (fun x=> f x * g x) x≤ potash a k f x *potash a k g x:=by
 let A (i:ℕ):= noble a i f x; let B (i:ℕ):=noble a i g x
 let R:= Finset.range (k+1)
 unfold potash; change (∑ i∈ R,_ ) ≤ (∑ i∈R,A i)* ∑ i∈R,B i; rw [Finset.sum_mul_sum]
 calc
   _ ≤ ∑ i∈ R, ∑ j∈ Finset.range (i+1), A j * B (i-j) := by
      apply sum_le_sum; intro i hi
      have he:i≤k:= Nat.le_of_lt_succ (mem_range.mp hi)
      exact nob_q h (l.of_le (by exact_mod_cast he)) (s.of_le (by exact_mod_cast he))
   _ ≤ _ := by
      let p (i:ℕ):= Finset.antidiagonal i
      let v (d:ℕ×ℕ) := A d.1*B d.2
      simp_rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> A i*B j)]; change (∑ i∈R,∑ d∈ p i, v d)≤_
      rw [← Finset.sum_biUnion, ←Finset.sum_product'] -- tune
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i t n=> mul_nonneg (pos_nob h _) (pos_nob h _)); rintro ⟨i,j⟩ hp
        obtain ⟨l,g,v⟩:=mem_biUnion.mp hp; rw [mem_product]; change l∈range _ at g; change (_,_)∈ Finset.antidiagonal _ at v; simp only [Finset.mem_antidiagonal] at v; simp only [R,mem_range,Prod.fst,Prod.snd] at *; omega
      intro i _ j _ ht; apply disjoint_left.mpr; intro d f g; exact ht ((Finset.mem_antidiagonal.mp f).symm.trans (Finset.mem_antidiagonal.mp g))
variable {C B V:ℝ}{ι J n:Type*}[LinearOrder n][Fintype n]
structure Pence(k:ℕ)(f:E→ℂ)(x:E)(C:ℝ): Prop where
 smooth: ContDiffAt ℝ k f x
 earned: potash 1 k f x ≤C
lemma Pence.const(x:E)(c:ℂ): Pence k (fun _=> c) x ‖c‖:=⟨contDiffAt_const,(pot_const ..).le⟩
lemma Pence.nonneg (h:Pence k f x C):0≤ C:=(sum_nonneg (fun i _=> pos_nob zero_le_one i)).trans h.earned
lemma Pence.germ (h:Pence k f x C)(p:f =ᶠ[𝓝 x] g): Pence k g x C:=⟨h.smooth.congr_of_eventuallyEq p.symm,le_trans (le_of_eq (sum_congr rfl (fun i _=>congrArg (fun u=> _ * ‖u‖) ((p.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds.symm)))) h.earned⟩ -- tune
lemma Pence.pay (h:Pence k f x C):Allows k f x (k.factorial * C):=⟨h.smooth, fun j p=> by simpa using nob_out zero_lt_one le_rfl h.earned j p⟩
lemma Pence.add (h:Pence k f x C)(hg:Pence k g x B): Pence k (f+g) x (C+B) :=by -- notation
 refine ⟨h.smooth.add hg.smooth,(le_trans ?_ (add_le_add h.earned hg.earned)) ⟩
 unfold potash; rw [←sum_add_distrib]; apply sum_le_sum; intro i hp; have hx:i≤k:= Nat.le_of_lt_succ (mem_range.mp hp)
 unfold noble; rw [←mul_add, iteratedFDeriv_add_apply (h.smooth.of_le (by exact_mod_cast hx)) (hg.smooth.of_le (by exact_mod_cast hx))]; apply mul_le_mul_of_nonneg_left (norm_add_le ..) (by positivity)
lemma Pence.twice (h:Pence k f x C)(hb:Pence k g x B):Pence k (f*g) x (C*B):= ⟨h.smooth.mul hb.smooth,(pot_q zero_le_one h.smooth hb.smooth).trans (mul_le_mul h.earned hb.earned (sum_nonneg fun i _=> pos_nob zero_le_one i) h.nonneg)⟩
lemma Pence.σ (c:ℂ)(h:Pence k f x C): Pence k (c • f) x (‖c‖ * C):=(Pence.const x c).twice h
lemma Pence.money {p:Finset ι}{G:ι→ E→ℂ}{B:ι→ℝ}(h:∀ i∈p,Pence k (G i) x (B i)): Pence k (∑ i∈p,G i) x (∑ i∈p,B i):=by
 classical
 induction p using Finset.induction_on with
 | empty => rw [sum_empty,sum_empty, ←show ‖(0:ℂ)‖=0 from norm_zero]; exact Pence.const _ _ -- tune rw occurrences
 | @insert i p u ih=>rw [sum_insert u,sum_insert u]; exact (h _ (mem_insert_self ..)).add (ih fun i t=> h i (mem_insert_of_mem t)) -- tune
abbrev Band(E n:Type*)[LinearOrder n] := E→ FC n
abbrev SongF (F:E→FC n)(i:Finset n): E→ℂ:=fun x=>crumb (F x) i
abbrev Raid(n:Type*)[LinearOrder n]:= Finset n→ℝ
structure Woody (k:ℕ)(F:E→FC n)(x:E)(C:Raid n):Prop where
 own :∀ᶠ y in 𝓝 x,spanP n (F y)
 haveP(i:Finset n): Pence k (SongF F i) x (C i)
variable {F G:E→FC n}{c d:Raid n}
lemma Woody.p (h: Woody k F x c):0 ≤c:=fun i=> (h.haveP i).nonneg
lemma Woody.germ(h: Woody k F x c)(ht:F=ᶠ[𝓝 x] G): Woody k G x c:=⟨by filter_upwards [ht,h.own] with i g a; rw [←g]; exact a, fun i=> (h.haveP i).germ (ht.fun_comp (fun x=> crumb x i))⟩
lemma Woody.addP (h:Woody k F x c)(p:Woody k G x d):Woody k (F+G) x (c+d):=by
 exact ⟨by filter_upwards [h.own,p.own] with i g r; exact sumB g r,fun i=> (h.haveP i).add (p.haveP i)⟩ -- tune
lemma Woody.empty(x:E):Woody (n:=n) k 0 x 0:=by
 refine ⟨Eventually.of_forall fun _=> (show spanP n 0 by unfold spanP; simp [crumb]), fun i=> ?_⟩; change Pence k (fun _=> 0) x 0; rw [←show ‖(0:ℂ)‖=0 from norm_zero]; exact Pence.const _ _
lemma Woody.sumV {S:Finset ι}{G:ι→ E→FC n}{B:ι→Raid n}(p:∀ i∈S, Woody k (G i) x (B i)): Woody k (∑ i∈S,G i) x (∑ i∈S,B i):=by
 classical
 induction S using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty]; exact Woody.empty _
 | @insert i p u ih=>rw [sum_insert u,sum_insert u]; exact addP (p _ (mem_insert_self ..)) (ih fun a t=> p a (mem_insert_of_mem t))
lemma Woody.chit (s: Finset n)(h:Pence k f x C): Woody k (fun x=>f x • poke s) x (Pi.single s C):=by
 refine ⟨Eventually.of_forall fun _=> spanS (spanPt _) _,fun i=>?_ ⟩; unfold SongF; simp_rw [crumb_scale, Pastry.chip]; by_cases hp:i=s; · rw [if_pos hp,hp,Pi.single_eq_same]; simpa
 rw [if_neg hp, Pi.single_eq_of_ne hp]; simpa using Pence.const (k:=k) x (0:ℂ)
lemma Woody.uniV(x:E) : Woody (n:=n) k 1 x (Pi.single ∅ 1):=by
 have ht:= Woody.chit (∅:Finset n) (Pence.const (k:=k) x (1:ℂ))
 simp only [one_smul,poke,Poly.tag_void,norm_one] at ht; exact ht
lemma Woody.ride (c':ℂ)(h:Woody k F x c)(p:‖c'‖=1):Woody k (c' • F) x c:=by
 refine ⟨?_,fun i=>?_ ⟩
 · filter_upwards [h.own] with i g; exact spanS g _
 exact Eq.mp (congrArg (fun c=> Pence k (c' • SongF F i) x c) (by rw [p,one_mul]: ‖c'‖ * c i=c i)) ((h.haveP i).σ c') -- tune deadline
abbrev skirtB (c d:Raid n)(i j : Finset n): Raid n := if Disjoint i j then Pi.single (i∪j) (c i*d j) else 0
def skirt (c d:Raid n): Raid n:=∑ i:Finset n,∑ j:Finset n,skirtB c d i j
lemma Woody.pairP (h: Woody k F x c)(hp:Woody k G x d): Woody k (F*G) x (skirt c d):=by
 let M(i j:Finset n)(x:E): FC n:= SongF F i x • poke i * (SongF G j x • poke j); let L:= ∑ i:Finset n,∑ j: Finset n,M i j
 have hv:L =ᶠ[𝓝 x] F*G:=by filter_upwards [h.own,hp.own] with x p g; simp only [L,M, Finset.sum_apply]; rw [←sum_mul_sum]; exact congrArg₂ (·*·) p.symm g.symm
 have he(i j:Finset n): Woody k (M i j) x (skirtB c d i j):= by
    unfold skirtB; split_ifs with g; swap; · rw [show M i j=0 from funext fun v=> by unfold M; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,poke,poke,Poly.tag_mul,if_neg g,smul_zero,smul_zero]; rfl]; exact Woody.empty _
    apply Woody.germ (Woody.ride (Poly.sail i j) (Woody.chit _ ((h.haveP i).twice (hp.haveP j))) (Poly.sail_size ..)); refine Eventually.of_forall fun v=>?_
    unfold M; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,poke,poke,Poly.tag_mul,if_pos g]; simp [smul_smul,mul_comm,mul_assoc,mul_left_comm]
 exact Woody.germ (Woody.sumV (fun i _=> Woody.sumV (fun j _=>he i j))) hv
end YM.CF.Hake
