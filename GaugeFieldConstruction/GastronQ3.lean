import GaugeFieldConstruction.GattQ3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 60000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tenant Branch XGarden.MastTin Ladder3
variable (F:Factor3 n)(Q:LeaseQ γ n)
section pay
variable (a c d:ℝ)(h:γ→ℝ)
local notation "Z"=> F.H.val.2
local notation "Ω"=> Branch.rent
local notation "κ"=> AV3 Q F
local notation "V" i:max=> (core3 Q F i).val.2
local notation "B_T" p:max=> LeadQ Z Q.H p
lemma card_cap (i: AV3 Q F): (V i).card≤ F.H.val.2.card+∑ j:Fin i.1.val.1,(Q.X (i.2.val j)).card:= (Finset.card_union_le ..).trans (Nat.add_le_add_left (Finset.card_biUnion_le ..) _)
lemma rent_Q (x: AV3 Q F)(v:0≤a): rent a (V x) ≤ rent a Z *∏ j:Fin x.1.val.1, rent a (Q.X (x.2.val j)):=by
 unfold Branch.rent; rw [←Real.exp_sum,←Real.exp_add]; apply Real.exp_monotone
 rw [←Finset.mul_sum, ←mul_add]; apply mul_le_mul_of_nonneg_left _ v; norm_cast; exact card_cap F Q x
structure KPower (a c:ℝ)(h:γ→ℝ):Prop where
   pos:0≤h
   spend(z: Seat n): ∑ i:γ with z∈Q.H i, h i*Branch.rent a (Q.X i)≤ c -- needs parentheses
   edge(i): h i≠0→Grove (terr (More n)) (Q.X i)
structure BasePower (p:ℝ):Prop where
   pos :0≤p
   grow:p≠0→Grove (terr (More n)) F.H.val.2
variable (r:KPower Q a c h)(v:0<a)(p t:ℝ)(t':0≤t)(w:0≤p)(t0:0≤c)
local notation "G"=> clouds Q.H Z
lemma ξᵣ (b d:ℕ) : ‖discount b d‖ ≤ 1:=by
 unfold discount; rw[norm_inv,norm_mul,norm_natCast,norm_natCast]; exact inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos _) (by exact_mod_cast Nat.factorial_pos _)) -- tune
lemma κπ (i: AV3 Q F):i.1.val.1+i.1.val.2≤2:=((specs₃ ..).mp i.1.property).trans (fade_sz _)
include r t' w
lemma spaceG (i:AV3 Q F):0≤tank3 Q F t p h i:=by unfold tank3 zcost3; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) w) t') (prod_nonneg fun _ _=>r.pos _)
omit t' w
lemma radd_Q : (∑ i∈ G,h i * rent a (Q.X i))≤ (F.H.val.2.card:ℝ)*c :=by
 let Y(i):=h i*rent a (Q.X i); have he : (∑ i∈G,Y i) ≤ ∑ z∈Z, ∑ i:γ with z∈Q.H i,Y i:=by
    let X:= fun j=> Q.H j
    have hv:0≤ Y:=fun i=>mul_nonneg (r.pos _) (Real.exp_pos _).le
    simp_rw[show ∀ z: Seat n,(∑ i:γ with z∈Q.H i,Y i)=∑ j:γ,(if z∈X j then Y j else 0) from (fun z=> Finset.sum_filter ..)] -- tune binder
    rw [sum_comm]; unfold clouds; rw[sum_filter]; refine sum_le_sum fun i _=>?_; split
    next h=> obtain ⟨b,t,g⟩:= Finset.not_disjoint_iff.mp h; refine le_trans (a:=Y i) ?_ (single_le_sum (f:=fun z:Seat n=>if z∈X i then Y i else 0) (fun j _=> ite_nonneg (hv i) le_rfl) t); exact (if_pos g).symm.le
    apply sum_nonneg; exact fun i _=> ite_nonneg (hv _) le_rfl
 calc _ ≤ _ := he
      _ ≤ _ := by exact (sum_le_sum (fun i (p:i∈Z)=> r.spend i)).trans_eq (by rw[sum_const,nsmul_eq_mul])
include t' w t0 v
local notation "dρ"=> rent a
abbrev overflow₃ (d c:ℝ) := (1+d⁻¹*c)
lemma shore_A (d':BD3 F): (∑ i:Heart F.H Q.H d'.val.1,tank3 Q F t p h ⟨d',i⟩* rent a (core3 Q F ⟨d',i⟩).val.2) ≤ t*4*overflow₃ a c ^ 2 * (p*rent (3*a) Z):=by
 let b:=d'.val.1; let d:=d'.val.2; have hd:b+d≤ 2 := ((specs₃ ..).1 d'.property).trans (fade_sz _)
 let M:= B_T b; let B(i):= h i*rent a (Q.X i)
 -- bound $4 P t per.F rated
 have hi(i:Heart F.H Q.H b): tank3 Q F t p h ⟨d',i⟩* rent a (core3 Q F ⟨d',i⟩).val.2 ≤ (4*p*t*dρ Z)*∏ j:Fin b,B (i.val j):=by
    let X:= rent a Z *∏ j:Fin b,rent a (Q.X (i.val j)); have hx:0≤X:=mul_nonneg (Real.exp_pos _).le (prod_nonneg fun _ _=>(Real.exp_pos _).le)
    refine le_trans (mul_le_mul ?_ (rent_Q F Q a _ v.le) (Real.exp_pos _).le ?_) (le_of_eq (a:=(4*p*t*(∏ j:Fin b,h (i.val j)))*X) ?_) -- order
    · unfold tank3 zcost3; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ w) t') (prod_nonneg fun _ _=>r.pos _)
      have he: (2:ℝ)^(d+b)≤ 4:= (pow_le_pow_right₀ (by norm_num) (by omega:d+b ≤ 2)).trans (by norm_num)
      exact (mul_le_of_le_one_left (by positivity) (ξᵣ ..)).trans he
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) w) t') (prod_nonneg fun _ _=>r.pos _)
    unfold B X; rw [Finset.prod_mul_distrib]; ring
 let U:= overflow₃ a c; let Y:= U* dρ Z
 have hu:1≤ dρ Z:=Real.one_le_exp (mul_nonneg v.le (Nat.cast_nonneg _)); have hY:1≤ Y:= one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (mul_nonneg (inv_pos.mpr v).le t0)) hu
 have hp:M= Finset.univ.filter (fun i:Fin b→γ=>∀ j,i j∈ G):=rfl
 let Z₀:= (∑ i∈G,B i)
 have hZ:0≤ Z₀:=sum_nonneg fun _ _=>mul_nonneg (r.pos _) (Real.exp_pos _).le
 have hZ': Z₀≤ Y:=by
    let d':ℝ:=F.H.val.2.card; have h0:d'≤ a⁻¹*(dρ Z):=by
       apply (le_inv_mul_iff₀ v).2; exact le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _)
    have h0':=mul_le_mul_of_nonneg_right h0 t0; apply (radd_Q F Q a c h r).trans (h0'.trans ?_); unfold Y U overflow₃; nlinarith only[hu]
 have f:(∑ i:Heart F.H Q.H b, ∏ j:Fin b,B (i.val j))≤ Y^2:=by
    have he : (∑ i:Heart F.H Q.H b, ∏ j:Fin b,B (i.val j))= Z₀^b :=by
       change ∑ i:↥M,_= _
       rw [← sum_subtype M (p:=fun i=>i∈M) (fun i=>Iff.rfl) (fun i=>∏ j:Fin b,B (i j))]
       rw [←show ∏ j:Fin b,Z₀=Z₀^b from (by simp),hp, sum_filter (s:=univ)]
       -- Prod sum with zeros for clipped
       rw [show Z₀= ∑ i:γ,(if i∈ G then B i else 0) from (by unfold Z₀; exact (sum_filter _ _).trans (by apply sum_congr rfl; intro i _; by_cases w:i∈G <;> simp_all [clouds]))]; rw [Fintype.prod_sum]; apply sum_congr rfl; intro i w; split
       next g=> exact Finset.prod_congr rfl fun j _=> Eq.symm (if_pos (g j))
       next h=> push Not at h; obtain ⟨j,g⟩:= h; exact (prod_eq_zero (mem_univ j) (if_neg g)).symm
    rw[he]; exact (pow_le_pow_left₀ hZ hZ' _).trans (pow_le_pow_right₀ hY (by omega))
 refine (sum_le_sum (fun i _=>hi i)).trans ?_; rw [←mul_sum]; apply (mul_le_mul_of_nonneg_left f (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) w) t') (Real.exp_pos _).le)).trans_eq
 unfold Y U; have hv: rent a Z * rent a Z ^ 2= rent (3*a) Z:=by unfold Branch.rent; rw [←Real.exp_nat_mul,←Real.exp_add]; norm_num; ring_nf
 rw[←hv]; unfold Branch.rent; ring
end pay
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
