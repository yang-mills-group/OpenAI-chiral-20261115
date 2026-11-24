import YM.CF.Fixed.Voltage.Address
/-!
Global flag address adjustment. Holds limit-kicking.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Fixed.Voltage
open Function NormedSpace Filter Metric Finset Lattice Wilson SU Scree Skye Fock Lat Cube MeasureTheory Vow RG Rue Spire Scroll
open Vow Ione Beau Salt Push.BetaTransport
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{x a b h u v w:ℝ}(P:BudgetPoint)(D:Support (More n)){R Q:ForceBudget n}{E E':RegBudget n}
variable {K:ℕ}{τ:Sweep n→Prop}
local notation "N"=> More n
local notation "A"=> deck_F P D
noncomputable def visorP (P:BudgetPoint) (F:Copy n)(j:Force n) :Copy n:=if j.val.1.val.2=univ then hours P j.val.2 (fareH n • F) else 0
noncomputable def visorCost (P:BudgetPoint) (n:Side)(b:ℝ):ℝ:= Fintype.card (Force n)*P.mass (univ:Support (More n)) (fareX 0 P (univ:Support (More n))*(fareH n*b))
noncomputable def Speed (F:Copy n):Prop:= ∀ s:Sweep n,∀ U,JetS s.s s.charge (detX s.s) U→∀ V:Orbit n,Injective (priorP V.2)→ F (flashA s V.1,bun s V.2)= tintY s U (F V)
lemma visor_Budget (F:Copy n)(v:∀ D:Support (More n),Metered P D F w b)(u:1 ≤ w)(t:Speed F):Dark Utrue (visorP P F) P w (visorCost P n b):=by
 have hv:= (v ∅).holds (zero_le_one.trans u); let x:=fareX 0 P (univ:Support N)*(fareH n*b); have hx:0≤x:=mul_nonneg (health_f ..) (mul_nonneg (fareH_pos _).le hv)
 let ψ(j:Force n):ℝ:= if j.val.1.val.2=univ then x else 0; refine ⟨⟨ψ,fun i=>?_ ,fun i=>?_⟩,fun s S T g X V o K=>?_⟩
 · unfold ψ visorP; split; swap; exact Vale.rinsed ..
   rename_i h; let G:=fareH n • F; let D:=i.val.2; have hp:= (v D).stow (fareH n); let hv':= deck_sure P D G; have ht:=hp.meter; rw [abs_of_pos (fareH_pos _)] at ht; rw [←h] at ht hv'; unfold x; rw [←h]; exact Medal.preserves ht hv' (zero_le_one.trans u) 0
 · apply le_trans (b:=∑ _i:Force n,P.mass (univ:Support N) x); swap; · exact Eq.le (by simp [visorCost,x])
   refine sum_le_sum fun j _=>?_ ; split; swap; · exact mass_live _ _ hx
   unfold ψ; split; rename_i h; rw [h]; unfold BudgetPoint.mass; rw [mul_zero]; exact mass_live _ _ hx
 let W:Orbit n:=(V,o); let Y:Orbit n:=(flashA s V,bun s o); have he:(moveForce s X).val.1.val.2=univ ↔_:= full_K s X.val.1.val.2; unfold visorP; by_cases h:X.val.1.val.2=univ; rw [if_pos h,if_pos (he.2 h)]; swap; · rw [if_neg h,if_neg (mt he.1 h)]; exact (map_zero _).symm
 let D:=X.val.2; have hp: Y.1∈ deck_F P (moveForce s X).val.2 ↔W.1∈ deck_F P D:= deck_work P D s V; by_cases hy:W.1∈deck_F P D; swap; · rw [shut_F P D _ W hy,shut_F P (moveForce s X).val.2 _ Y (mt hp.1 hy),map_zero]
 rw [unveil_F P D _ W hy,unveil_F P (moveForce s X).val.2 _ Y (hp.2 hy),Pi.smul_apply,Pi.smul_apply,map_smul]; exact congrArg _ (t s T g W K)
lemma visor_nonzero (F:Copy n)(j:Force n)(V:Orbit n)(u:Scree.clamp P j (visorP P F j) V ≠ 0): j.val.1.val.2=univ:=by by_contra! h; apply u; unfold Scree.clamp visorP; rw [if_neg h]; split <;> rfl
private lemma alone_F (s:Finset (Force n))(v:s.card≠1)(K: flagTuple s D)(jok:Force n)(p:jok ∈ s) : jok.val.1.val.2 ≠ univ:=by -- auto
 intro l; obtain ⟨i,u,k⟩:= exists_mem_ne (show 1 < s.card from lt_of_le_of_ne (Finset.one_le_card.mpr ⟨_,p⟩) v.symm) jok
 have h:Disjoint i.val.1.val.2 jok.val.1.val.2:= K.2 u p k; rw [l] at h; exact Finset.disjoint_left.mp h i.val.1.property (mem_univ _)
private theorem mask_tend (K F:ForceBudget n)(j:Force n)(V:Orbit n): Scree.clamp P j ((K+F) j) V= Scree.clamp P j (K j) V + Scree.clamp P j (F j) V:=by unfold Scree.clamp;split; rfl; exact (zero_add ..).symm
noncomputable def prismD {D:Support N} (g: D.Nonempty) (i:Seat n):Force n:= ⟨(fullSlot i,D),g,subset_univ _⟩
noncomputable abbrev weightF (Q:ForceBudget n) (V:Orbit n) (j: Finset (Force n)) :Cipher n:= if flagTuple j (flags P.threshold V.1) then ∏ i∈j, Scree.clamp P i (Q i) V else 0
lemma fuel_formula (F:ForceBudget n)(V:Orbit n):fueled P F V=∑ i:Finset (Force n),weightF P F V i:=by unfold fueled weightF; congr!
lemma visor_term (s:Finset (Force n))(v: s.card≠1)(F:Copy n)(K:ForceBudget n)(V:Orbit n): weightF P (K+visorP P F) V s=weightF P K V s:=by
 unfold weightF; split; swap; rfl
 rename_i t; apply prod_congr rfl; intro j h; rw [mask_tend, Classical.not_not.mp (show ¬ Scree.clamp P j (visorP P F j) V ≠0 from mt (visor_nonzero P F j V) (alone_F (flags P.threshold V.1) s v t j h)),add_zero] -- tune
lemma visor_at (j:Force n)(g:j.val.2=D)(F:Copy n)(V:Orbit n)(v:V.1∈ A) : let t:=j.val.1.val.2=univ; weightF P (R+visorP P F) V {j}-weightF P R V {j}= if t then fareH n • F V else 0:=by
 dsimp only; have hv: flags P.threshold V.1=D:=v.2; unfold weightF; have he:flagTuple {j} (flags P.threshold V.1):=by unfold flagTuple; rw [singleton_biUnion,hv,g]; exact ⟨rfl, by simp⟩ -- tune
 rw [if_pos he,if_pos he,prod_singleton,prod_singleton, mask_tend,add_sub_cancel_left]; unfold visorP; by_cases h:j.val.1.val.2=univ; swap
 · rw [if_neg h,if_neg h]; unfold Scree.clamp; split<;> rfl
 rw [if_pos h,if_pos h]; have hk:boundF j P V.1:= by unfold boundF; rw [h,g]; exact deck_budget P D _ v
 unfold Scree.clamp; rw [if_pos hk,unveil_F P j.val.2 _ V (g.symm ▸ v)]; rfl
lemma visor_take(F:Copy n)(g:D.Nonempty)(V:Orbit n)(v:V.1∈A): fueled P (R+visorP P F) V-fueled P R V=F V:=by
 classical
 let f(J:Finset (Force n)):=weightF P (R+visorP P F) V J-weightF P R V J; let q(o:Seat n):Finset (Force n):= {prismD g o}; let X:=Finset.univ.image q; rw [fuel_formula,fuel_formula,←sum_sub_distrib]; change (∑ i, f i)=F V; have he( j:Finset (Force n))(k:j∉X): f j=0:=by
   by_cases b:j.card=1; swap; · unfold f; rw [visor_term P j b]; ring
   obtain ⟨a,rfl⟩:=Finset.card_eq_one.mp b; by_cases t:a.val.2=D; swap; · unfold f weightF; have hl:¬flagTuple {a} (flags P.threshold V.1):=fun h=> t ((singleton_biUnion ..).symm.trans (h.1.trans v.2)); rw [if_neg hl,if_neg hl,sub_self]
   unfold f; rw [visor_at (R:=R) P D a t F V v,if_neg]; intro h; apply k; exact mem_image.mpr ⟨a.val.1.val.1,mem_univ _,by unfold q; congr 1; exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl h.symm)) t.symm)⟩
 have hi:Injective q:=fun i j p=> congrArg (fun a:Force n=>a.val.1.val.1) (Finset.singleton_inj.mp p)
 have hx(i):f (q i)=fareH n • F V:= (visor_at (R:=R) P D (prismD g i) rfl F V v).trans (if_pos (show (prismD g i).val.1.val.2=univ from rfl))
 rw [←sum_subset (s₁:=X) (subset_univ _) (fun i _=>he i)]; unfold X; rw [sum_image (by intro a _ b _ h; exact hi h)]; simp_rw [hx,sum_const,card_univ]; rw [←Nat.cast_smul_eq_nsmul ℝ]; apply smul_inv_smul₀ (show fairH n≠0 by unfold fairH; positivity)
end YM.CF.Fixed.Voltage
