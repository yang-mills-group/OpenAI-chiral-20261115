import YM.SU5.FiniteGaugeData.Trigonal.Loir
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option linter.unusedSimpArgs false
namespace YM.CF.Window.Trigo
open Function Filter Finset Metric
open Laurent Lattice Next.Free Bloch Fir Lat ArchiveK Largo WithLp MeasureTheory Complex
open scoped Topology BigOperators Set Pointwise InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra μFin
set_option quotPrecheck false
open Fock Rush
-- all probe slots using their actual early-stage hinge frequency. Tax receipt works in each generation. kernel scalar spin part.
abbrev Spins(b:Bool):Finset SpinIdx:= if b then plusHalf else plusHalfᶜ
private lemma spin_x(b:Bool)(p:SpinIdx): p∉ Spins b ↔ p∈ Spins (!b):=by cases b <;> simp [Spins]
def axle (b:Bool)(p:Momentum): Op SpinIdx:= if b then -zen p else (-zen p)ᵀ
lemma feeR(b:Bool):∃ f:Momentum →ₗ[ℂ] Op SpinIdx,⇑f=axle b:=by
 let H:Momentum→ₗ[ℂ] Op SpinIdx:= ⟨⟨zen,zenP⟩,fun a p=> zenS p a⟩; cases b; swap; · exact ⟨-H,rfl⟩
 -- typo f= coercion explicit
 exact ⟨ ⟨⟨fun x:Momentum=> (-zen x)ᵀ, fun x y=>by rw [zenP,neg_add, Matrix.transpose_add]⟩,fun x y=>by dsimp only; rw [zenS,←smul_neg,Matrix.transpose_smul]; rfl⟩,rfl⟩
private lemma cpHalf: Aop =cutM plusHalf:= Adef.trans raising.symm
private lemma skew_key (p: Momentum)(j b:SpinIdx)(z:Bool)(h:j∈ Spins z)(t:b∈ Spins z) : zen p j b=0:=by
 have he:= Matrix.ext_iff.mpr (zenA p) j b; rw [cpHalf,mul_sub,mul_one,cutM,Matrix.diagonal_mul,Matrix.sub_apply,Matrix.mul_diagonal] at he -- order Matrix.mul/app? `mul_` etc
 cases z <;> simp only [Spins,if_true,Bool.false_eq_true,if_false, mem_compl] at * -- proof for upper with plus or bot
 all_goals simp [h,t] at he; (first| exact he| exact he.symm)
lemma ax_spin (z:Bool)(p:Momentum)(i j:SpinIdx)(h:i∈ Spins z)(t:j∈ Spins z): axle z p i j=0:=by
 cases z <;> (first| exact (Matrix.transpose_apply ..).trans (by rw [Matrix.neg_apply,skew_key p _ _ _ t h,neg_zero])| exact (Matrix.neg_apply ..).trans (by rw [skew_key p _ _ _ h t,neg_zero])) -- tune
lemma ax_unit(b:Bool)(p:Momentum)(h:pass p≠0): IsUnit (axle b p):=by
 have ht: IsUnit (algebraMap ℂ (Op SpinIdx) (-pass p)):= (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr h)).map _; let A:=-zen p; have hx:A*A= _ := (neg_mul_neg ..).trans (zenSq p); rw [show prodM p p=pass p from (by simp [pass,prodM,sq])] at hx
 have h1:IsUnit A:=(((Commute.refl A).isUnit_mul_iff).1 (show IsUnit (A*A) from by rw [hx,←Algebra.algebraMap_eq_smul_one]; exact ht)).1
 cases b; · apply (Matrix.isUnit_iff_isUnit_det ..).mpr; exact Matrix.isUnit_det_transpose A ((Matrix.isUnit_iff_isUnit_det _).1 h1)
 exact h1
abbrev Chamber (b:Bool):= Cover × (Spins b : Type)
local notation "Fst" b:max=> Chamber b
abbrev rotor (b:Bool)(u d:SpinIdx)(x:Cover):ℂ:= scout (fun p=> axle b (slurp p) d u) x
def levy (x:Chamber true)(y:Chamber false):= rotor true (x.2.val) y.2.val (y.1-x.1)
-- rank pores for all selection layouts
variable (b:Bool)
local notation "Σₓ"=> Spins b
private def player(f:Momentum→ₗ[ℂ] Op SpinIdx)(u v:SpinIdx): Momentum→ₗ[ℂ]ℂ:= (Matrix.entryLinearMap ℂ ℂ u v |>.comp f) -- def tune
#print axioms ax_unit
#print axioms ax_spin
private lemma scout_c {A:E4→ℂ}(a:ℂ)(x:Cover):scout (a • A) x=a*scout A x:=by
 unfold scout; simp_rw [Pi.smul_apply,smul_comm _ a,integral_smul]; exact smul_comm ..
-- if finite number of independent input charges cannot make finitely-sustained sunset. Every frame satisfies.
abbrev Perron (x:Fst b) (y:Fst (!b)) :ℂ:= rotor b (x.2.val) y.2.val (y.1-x.1)
lemma Alpine(S T:Finset Cover)(A: Cover→ SpinIdx→ℂ)(p:∀ x∉T,∀ i∈ Spins (!b), ∑ y∈ S,∑ j∈ Spins b,A y j* rotor b j i (x-y)=0): ∀ x∈S,∀ j∈ Spins b,A x j=0:=by
 obtain ⟨F,Fh⟩:=feeR b; let G(d u:SpinIdx):= player F d u; let Y(d:SpinIdx)(x:Cover):=∑ j∈Spins b,A x j • (G d j)
 obtain ⟨a,hA,U⟩:= brush_sep; let p':= brushQ (a+a); have gp(d u:SpinIdx)(p:Momentum) : axle b p d u= G d u p:= by unfold G player; rw [←Fh]; rfl
 have he(d:SpinIdx)(h:d∈Spins (!b)):∀ x∉T, scout (Limb S (Y d)) x=0:=by
    intro x hx; have hz:= p x hx d h; rw [←hz, scout_v]; refine sum_congr rfl (fun i _=> ?_); let V(j:SpinIdx):E4→ℂ:= A i j • (G d j∘ slurp)
    have ht(j): Integrable (V j) μF:=(Loan _).smul _; have hb(w:E4) : (Y d i) (slurp w)= ∑ j∈Spins b,V j w:=by unfold Y; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; rfl
    rw [show Y d i∘slurp= fun p=>∑ j∈ Spins b,V j p from funext hb, scout_sum _ V (fun j _=>ht _)]; refine sum_congr rfl fun j _=>?_ ; rw [show scout _ (x-i)=_ from (scout_c (A:=G d j ∘ slurp) (A i j) (x-i))]; unfold rotor; simp_rw [gp]; rfl
 have hp: IsUnit (axle b p'):=ax_unit _ _ (by unfold p'; rw [spendQ]; exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (show a+a ≠0 from by rw [←two_smul ℝ a]; exact smul_ne_zero (by norm_num) hA))))
 intro x hx; let f : SpinIdx→ℂ:= fun i=> if i∈ Spins b then A x i else 0; have hh: (axle b p') *ᵥ f=0:=by
    funext i; unfold Matrix.mulVec dotProduct; change ∑ j:SpinIdx,_=0; rw [← sum_subset (f:=fun j:SpinIdx=> axle b p' i j*f j) (subset_univ (Spins b))]; swap; · intro j _ t; unfold f; rw [if_neg t,mul_zero]
    by_cases g:i∈ Spins b; · exact sum_eq_zero fun j t=>by rw [ax_spin b _ _ _ g t,zero_mul]
    have ht:= royalty S T (Y i) (he i ((spin_x ..).1 g)) U x hx; unfold Y at ht; simp only [LinearMap.sum_apply,LinearMap.smul_apply] at ht; rw [← ht]; exact sum_congr rfl fun j t=>by rw [gp]; unfold f; rw [if_pos t]; exact mul_comm ..
 have h:f=0:=Matrix.mulVec_injective_iff_isUnit.mpr hp (by rw [hh, Matrix.mulVec_zero]); intro j k; simpa only [f,Pi.zero_apply,k,ite_true] using congrFun h j
lemma rotor_z (x:Cover)(i j:SpinIdx) : rotor true i j x= spiral (emitX x) j i:=by
 unfold rotor; rw [←starQuote]; let L:= (Matrix.entryLinearMap ℂ ℂ j i).toContinuousLinearMap; exact scout_we L rain_Int x
-- final U.F. arbitrary Finset input.
lemma bytes(S:Finset (Chamber b))(T:Finset Cover)(v:Chamber b→ℂ)(p:∀ i:Chamber (!b),i.1∉T→ ∑ z∈S,v z*Perron b z i=0): ∀ z∈S,v z=0:=by
 classical
 let U:= S.image Prod.fst; let f(i:Cover)(j:SpinIdx):ℂ:= if h:j∈ Spins b then if (i,(⟨j,h⟩:↥(Spins b)))∈ S then v (i,⟨j,h⟩) else 0 else 0
 have he:= Alpine b U T f (fun i hi j hj=>?_ ); swap -- interleaved have ?_ inside `have :=` doesn't provide goal? tune
 · let x: Chamber (!b):=(i,⟨j,hj⟩); rw [←p x hi]
   have hp: S ⊆ U ×ˢ (univ:Finset (Spins b)):= fun z p=> mem_product.mpr ⟨mem_image_of_mem _ p,mem_univ _⟩; let C (z:Chamber b):= if z∈ S then v z * Perron b z x else 0; rw [show ∑ z∈S, v z*Perron b z x=∑ z∈ S,C z from sum_congr rfl fun i p=> (if_pos p).symm]; rw [Finset.sum_subset hp (by intro i _ h; exact if_neg h), Finset.sum_product]; refine sum_congr rfl fun i _=>?_ ; rw [←Finset.sum_coe_sort (Spins b)]; refine sum_congr rfl fun l _=>?_ ; by_cases p:(i,l)∈S <;> simp [f,p,C,x,Perron,l.property]
 rintro ⟨x,j,hx⟩ p; specialize he _ (show x∈U from mem_image_of_mem Prod.fst p) j hx; unfold f at he; rw [dif_pos hx,if_pos p] at he; exact he
lemma per_sum(x:Fst true)(y:Fst false): levy x y = -Perron false y x:=by
 unfold levy Perron; rw [show rotor false _ _ (x.1-y.1)=rotor true x.2.val y.2.val (x.1-y.1) from rfl, rotor_z, rotor_z, show y.1-x.1= -(x.1-y.1) from Eq.symm (neg_sub ..), emit_neg,spiral_other,Matrix.neg_apply] -- tune
#print axioms Alpine
#print axioms bytes
end YM.CF.Window.Trigo
