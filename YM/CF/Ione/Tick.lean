import YM.CF.Ione.Rake
import YM.CF.Tye.Spin
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Ione
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Urn Hake Pastry Salt Hive Vow Skye Scion Levier Spire Scree Stilo
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n](b r t c:Bool)(U V:UNI n)
set_option quotPrecheck false
lemma cribP(A:ribbon n)(i:Finset (LeanV n)): crumb (paintR b r U A).val i=∑ j:Finset (LeanV n), (quantU (n:=LeanV n) (spice U r)).val i j*cSignX (b.xor r) (crumb A.val j):=by
 change (sings (b.xor r) _ A.val) i _=_; rw [singT,twist_formula]; change (quant ((spice U r).val)* _*star (quant ((spice U r).val))) _ _= _; rw [←basis_act (quant (spice U r).val * windX (b.xor r) A.val * star (quant (spice U r).val)) i ∅,act_mul,show basisKet (∅:Finset (LeanV n))=vacuum _ from rfl,remove_vac_pair,act_mul,act_at]; unfold Matrix.mulVec dotProduct; apply sum_congr rfl; intro j _; apply congrArg (fun x:ℂ=> quant (spice U r).val i j*x); rw [vacuum,basis_act]; cases b.xor r<;> rfl
variable {N:Side}(s:Sweep N)
local notation "Tz"=> siteU (castX s) s.charge (spinU s.charge s.s) N
local notation "dL"=> (detX s.s)
open Nacre
abbrev praise(s:Sweep N):= spice (siteU (castX s) s.charge (spinU s.charge s.s) N) (detX s.s)
abbrev hail_Q(s:Sweep N):= quantU (n:=Dwell N) (praise s)
abbrev cod_A(i:Dwell N):Seat N:=node i.2.1.1
local notation "Yh"=> (hail_Q s).val
local notation "Dk"=> Finset (Dwell N)
lemma roseQ(X:Cipher N)(i:Dk):crumb (suit_Y s X).val i=∑ j:Dk,Yh i j * payZ s (crumb X.val j):= cribP _ _ _ X i
lemma sign0 (g:Bool): cSignX g 0=0:=by cases g<;>simp [cSignX]
lemma spice_E(W:UNI n)(u:Bool)(i j:LeanV n)(t:W.val i.2 j.2=0): (spice W u).val i j=0:=by
 obtain ⟨p,i⟩:=i; obtain ⟨q,j⟩:=j; change W.val i j=0 at t; rw [Urn.cream]; split; swap; rfl
 cases q<;>cases u<;>simp [crib,Pastry.thread,ccU,filmG,t]
lemma price_Q(i j:Dwell N)(v:(praise s).val i j≠0):boxA s (cod_A i)=cod_A j:=Tye.birth_l i.2 j.2 (castX s) (spinU s.charge s.s) s.charge (mt (spice_E (Tz) dL i j) v)
abbrev abode(X:Dk):=X.image cod_A
lemma roof_x(X Y:Finset n)(A:Op n)(h:∀ i j,A i j≠0→ (i∈X ↔ j∈Y)):cutM X.powerset* quant A=quant A*cutM Y.powerset:=by rw [←quantCut,←quantCut,←quant_mul,←quant_mul]; congr 1; ext i j; by_cases v:A i j=0; simp [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal,v]; simp [cutM,Matrix.diagonal_mul,Matrix.mul_diagonal,h i j v,mul_comm]
lemma seat_Y(X:Support (More N)): cutM (camp (actY s X)).powerset * (Yh)=(Yh)*cutM (camp X).powerset:=by apply roof_x; intro i j v; simp only [camp,mem_filter,mem_univ,true_and,actY]; rw [mem_map_equiv]; change boxA s (cod_A i)∈X ↔ cod_A j∈X; rw [show _= _ from price_Q s i j v]
lemma nearE(X:Support (More N))(i j:Dk)(v:Yh i j≠0)(w:j⊆camp X):i⊆camp (actY s X):=by
 have h:= Matrix.ext_iff.mpr (seat_Y s X) i j; rw [cutM,cutM,mul_diagonal,diagonal_mul,if_pos (mem_powerset.mpr w),mul_one] at h
 by_contra hp; rw [if_neg (mt mem_powerset.mp hp),zero_mul] at h; exact v h.symm
lemma nearV(i j:Dk)(v:Yh i j≠0):i⊆camp (actY s (abode j)):=nearE s _ i j v (fun x p=>mem_filter.mpr ⟨mem_univ _,mem_image_of_mem _ p⟩)
lemma inkE(i j:Dk)(v:Yh i j≠0):i.card=j.card:=Classical.byContradiction fun h=>v (quant_grade _ _ _ h)
lemma rich_F(X:Support (More N))(A:Cipher N)(q:Flour (camp X) A.val): Flour (camp (actY s X)) (suit_Y s A).val:=by
 let Z:=suit_Y s A; change Flour _ Z.val; refine ⟨fun i=> crumb Z.val i,Eq.trans (fineShape Z).allP (Eq.symm (Finset.sum_subset (Finset.subset_univ _) ?_))⟩
 intro i _ v; dsimp only; rw [show crumb Z.val i=0 from ?_,zero_smul]; rw [show crumb Z.val i=_ from roseQ s A i]; apply sum_eq_zero; intro j _; by_contra h; have k:= left_ne_zero_of_mul h
 have he:j∈ Wheat (camp X):= Classical.byContradiction fun p=> h (by rw [q.door p]; unfold payZ; rw [sign0,mul_zero])
 let p:=mem_filter.mp he; exact v (mem_filter.mpr ⟨mem_powerset.mpr (nearE s X i j k (mem_powerset.mp p.1)),by rw [inkE s i j k]; exact p.2⟩)
lemma end_Y(i j:Dk)(o:Seat N)(v:Yh i j≠0):endL ((boxA s).symm o) i≤endL o j:=by
 apply Finset.sup_le; intro x p; have hp:= (mem_filter.mp (nearV s i j v p)).2; rw [actY,mem_map_equiv] at hp; obtain ⟨y,w,z⟩:=mem_image.mp hp; change separation _ (cod_A x)≤ _; rw [←sitT s,Equiv.apply_symm_apply,←show cod_A y=(boxA s) (cod_A x) from z]; exact Finset.le_sup (f:=fun i:Dwell N=>separation o (cod_A i)) w
lemma tune_L(i j:Dk)(o:Seat N)(P:RG.BudgetPoint)(v:Yh i j≠0)(h:ℝ)(p:0≤h):tariff P ((boxA s).symm o) h i≤tariff P o h j:=by rw [Scree.tariff,Scree.tariff,inkE s i j v]; gcongr; exact end_Y s i j o v
end YM.CF.Ione
