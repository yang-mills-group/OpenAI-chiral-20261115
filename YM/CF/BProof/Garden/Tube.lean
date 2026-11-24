import YM.CF.BProof.Garden.Queen
/-! Coefficient reading for J (complex). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Garden
open Function Filter Fock NormedSpace Finset Align Wick Double Pastry
open scoped Topology Matrix MatrixOrder InnerProductSpace Kronecker BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] {s p q:Finset I}{C:Op I}
def alloy (s:Finset I) : Finset (Finset I):= s.powerset.filter (fun i=> Even i.card)
abbrev bodyJ (s:Finset I)(C:Op I):ℂ:= ‖pairWave (square s C)‖
def coeffJ (s:Finset I)(C:Op I)(t:Finset I)(A:FC I):ℂ:= star (inner ℂ (tiara s C t) (acts A (vacuum I)) / (bodyJ s C)^2)
def flakeJ (s:Finset I)(C: Op I)(A:FC I)(i:Finset I):= coeffJ s C i A • star (crown C i)
def opJ (s:Finset I)(C:Op I)(A:FC I):FC I:= ∑ i∈alloy s, flakeJ s C A i
@[simp] lemma mem_alloy (s t:Finset I): t∈alloy s ↔ t⊆s∧Even t.card:=by simp [alloy]
lemma ownsJ (h:Commute C (cutM s))(A:FC I): Sector s false (opJ s C A):= by apply Sector.sumS; intro i hi; obtain ⟨g,p⟩:= (mem_alloy ..).mp hi; have ht:= crown_owns h g; rw [decide_eq_false (not_not.mpr p)] at ht; exact ht.contr.scale _
lemma bodyne (s:Finset I)(C:Op I): bodyJ s C≠0:=Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le (wave_lower _)).ne' -- tune
@[fun_prop] lemma square_cont(s:Finset I):Continuous (square s):=by unfold square; fun_prop
@[fun_prop] lemma bodyCont(s:Finset I): Continuous (bodyJ s):=by unfold bodyJ; fun_prop
@[fun_prop] lemma tiara_cont(s i:Finset I): Continuous (fun C:Op I=>tiara s C i):=by unfold tiara; fun_prop
@[fun_prop] lemma coeff_cont (s i:Finset I) : Continuous (fun p:Op I×FC I=> coeffJ s p.1 i p.2):=by unfold coeffJ; fun_prop (disch:= intro x; exact pow_ne_zero _ (bodyne _ _)) -- tune
@[fun_prop] lemma opJ_cont(s:Finset I): Continuous (uncurry (opJ s)):=by unfold opJ uncurry flakeJ; apply continuous_finsetSum; intro i _; exact (coeff_cont s i).smul (continuous_star.comp ((crown_cont i).comp continuous_fst))
def crownU (s:Finset I)(C:Op I):FC I:=Matrix.of (fun i j=> if j⊆ s then ((bodyJ s C)⁻¹ • tiara s C j).ofLp i else (basisKet j).ofLp i)
lemma crown_leaf (s:Finset I)(C:Op I)(i:Finset I): acts (crownU s C) (basisKet i)=if i⊆s then (bodyJ s C)⁻¹ • tiara s C i else basisKet i:=by
 apply PiLp.ext; intro j; rw [basis_act]; by_cases h:i⊆s<;> simp only [h,crownU, Matrix.of_apply, ↓reduceIte]
lemma crown_star(m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C): crownU s C ∈ unitary (FC I):=by
 let A:=crownU s C
 have he{p q:Finset I}(g:p⊆s)(w:¬q⊆s): inner ℂ (acts A (basisKet q)) (acts A (basisKet p))=0:=by rw [show A=crownU s C from rfl,crown_leaf,crown_leaf,if_neg w,if_pos g,inner_smul_right,basis_inner,tiara_zone h g q w,mul_zero]
 have ht:star A*A=1:=by
   ext i j; rw [←basis_act (star A*A) i j,←basis_inner,act_mul,←act_inner,star_star]; by_cases g:i⊆s
   · by_cases w:j⊆s; swap; · rw [← inner_conj_symm,he g w,map_zero,Matrix.one_apply_ne (by rintro rfl; contradiction)]
     unfold A; rw [crown_leaf,crown_leaf,if_pos g,if_pos w,inner_smul_left,inner_smul_right]; by_cases d:i=j; · subst j; rw [Matrix.one_apply_eq,inner_self_eq_norm_sq_to_K,tiara_norm m h x g]; change star ((bodyJ s C)⁻¹)*((bodyJ s C)⁻¹*(bodyJ s C)^2)=1; rw [star_inv₀,show star (bodyJ s C)=bodyJ s C from (by simp [bodyJ])]; rw [pow_two,←mul_assoc (bodyJ s C)⁻¹ (bodyJ s C) (bodyJ s C), inv_mul_cancel₀ (bodyne _ _),one_mul, inv_mul_cancel₀ (bodyne _ _)]
     rw [Matrix.one_apply_ne d,tiara_dice m h x g w d,mul_zero,mul_zero]
   by_cases w:j⊆s; rw [he w g,Matrix.one_apply_ne (by rintro rfl; contradiction)]; unfold A; rw [crown_leaf,crown_leaf,if_neg g,if_neg w]; simp [Matrix.one_apply]
 exact ⟨ht,mul_eq_one_comm.mp ht⟩
variable {A:FC I}(m:C∈unitary _)(h:Commute C (cutM s))(x:Cᵀ= -C)(g:Sector s false A)
include h g
lemma scoringJ (i:Finset I) : inner ℂ (acts (crownU s C) (basisKet i)) (acts A (vacuum I)) • acts (crownU s C) (basisKet i)=if i∈alloy s then star (coeffJ s C i A) • tiara s C i else 0:=by -- no x,m
 rw [crown_leaf]; by_cases p:i⊆s; swap; · rw [if_neg p,if_neg (by simp [p]),basis_inner,homeZone g i p,zero_smul]
 rw [if_pos p,inner_smul_left]; by_cases t:Even i.card
 · rw [if_pos (by simp [p,t]),coeffJ, star_star]; rw [smul_smul]; congr 1; change star ((bodyJ s C)⁻¹)*_*_= _; rw [star_inv₀, show star (bodyJ s C)=bodyJ s C from (by simp [bodyJ])]; ring
 rw [if_neg (by simp [t]),tiara,← plump_vac,←act_mul]; let P:=crown C i * plump s C; have hh: Sector s true (crown C i):=by simpa only [decide_eq_true t] using crown_owns h p
 have hl: Sector s true (star P * A):=((hh.mul (plump_here ..)).contr).mul g; have hw:inner ℂ (acts P (vacuum I)) (acts A (vacuum I))=0:=by nth_rw 1 [← star_star P]; rw [act_inner,←act_mul,vacuum,basis_inner,basis_act]; exact hl.odd_lost _; -- maybe scope
 rw [hw,mul_zero,zero_smul]
include m x
theorem testedJ : acts (star (opJ s C A)) (pairWave (square s C))=acts A (vacuum I):=by
 let y:=acts A (vacuum I); let k:=vacuum I; let U:UNI (Finset I):=⟨crownU s C,crown_star m h x⟩; let G(i:Finset I):= star (coeffJ s C i A) • tiara s C i; have he: acts (star (opJ s C A)) (pairWave (square s C))=∑ i, if i∈alloy s then G i else 0:=by
    unfold opJ flakeJ; rw [star_sum,act_sum]; simp only [star_smul,star_star,act_smul]; rw [←sum_filter,filter_mem_eq_inter, univ_inter]; rfl -- tune
 rw [he]; simp_rw [show G=fun i=> star (coeffJ s C i A) • tiara s C i from rfl,← scoringJ h g]; change ∑ i, inner ℂ (acts U.val (basisKet i)) y • (acts U.val (basisKet i))=y; have hp(i:Finset I): inner ℂ (acts U.val (basisKet i)) y=(acts (star U.val) y).ofLp i:=by nth_rw 1 [←star_star U.val]; rw [act_inner,basis_inner]
 simp_rw [hp, ← map_smul]; rw [←map_sum,basis_expand,act_starUnit]
theorem convertJ(f:A*berth s=A) : star (opJ s C A) * plump s C = A:=by
 have hx:= ((ownsJ h A).contr).mul (plump_here s C); have he: Sector s false (star (opJ s C A)*plump s C):=hx; have hp:=berth_test he g (by rw [act_mul,plump_vac,testedJ m h x g]); rwa [mul_assoc,plump_id,f] at hp
omit g in
lemma coeffJ_bound(i:Finset I)(hi:i⊆s): ‖coeffJ s C i A‖ ≤ ‖acts A (vacuum I)‖:=by
 have hp:=wave_lower (square s C); have hx:=zero_lt_one.trans_le hp; let u:=acts A (vacuum I); unfold coeffJ; rw [norm_star,norm_div,norm_pow]; rw [show ‖bodyJ s C‖=‖pairWave (square s C)‖ from (by simp only [bodyJ, Complex.norm_real,Real.norm_of_nonneg hx.le])]; rw [div_le_iff₀ (pow_pos hx _)]; apply (norm_inner_le_norm ..).trans; rw [tiara_norm m h x hi,mul_comm _ ‖acts A (vacuum I)‖]; exact mul_le_mul_of_nonneg_left (le_self_pow₀ hp (by omega)) (norm_nonneg _)
omit m h x g in
lemma flakeJ_id(C:Op I)(i:Finset I): star (crown C i)=(((i.sort (· ≤ ·)).reverse).map (fun j=> printT (spear C j))).prod:=by
 unfold crown; generalize (i.sort (· ≤ ·))=l; induction l with| nil=> simp| cons i l ih=> simp [ih,thorn] -- tune star comm issue
end YM.CF.BProof.Garden
