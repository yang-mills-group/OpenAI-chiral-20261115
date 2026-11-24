import YM.CF.Reef.Tes
import YM.CF.Laic.Hope
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Reef
open Cube Function Filter NormedSpace Lattice Wilson Lat Rush Fock Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Nacre Laic Matrix Finset
open scoped Topology InnerProductSpace Matrix MatrixOrder Kronecker ContDiff BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N:Side}
abbrev diva:Shape:=incX 1
abbrev axS:UNI SpinIdx:=⟨spinJ,spinJ_unitary⟩
abbrev axle(N:Side):=prepU diva axS (xtra true) N
def rally(N:Side):Op (Single N)→L[ℝ] Op (Single N):= (show Op (Single N)→ₗ[ℝ] Op (Single N) from ⟨⟨fun X=>twist (axle N) (cc X),fun a b=>by rw [cc_add,map_add]⟩,fun a b=>by change twist _ (cc (a • b)) = a • twist _ _; rw [cc_rsmul,map_smul]⟩).toContinuousLinearMap
lemma rally_p (X:Op (Single N)): rally N X=sings true (axle N) X:=rfl
lemma stanza_d{n f:Side}(G:Ratio n f): Shape.broad G diva=diva:=by simp [diva, Shape.broad, incX]
lemma stir_d(U:Bkg (More N)): stir (xtra true) diva U=echo U:=by unfold stir diva incX; simp; rfl
lemma ventU(a:Shape)(U:UNI SpinIdx):ccU (prepU a U inert N)=prepU a (ccU U) inert N:=by
 have he:ccU (mealU a U inert N)=mealU a (ccU U) inert N:=by
    apply Subtype.ext; ext ⟨i,p,u⟩ ⟨j,q,v⟩; change cc (jump _ (fun i:Site N=> a.payA i • (U.val ⊗ₖ (1:Op SU.Slot)))) _ _=jump _ (fun i=>a.payA i • (cc U.val ⊗ₖ (1:Op SU.Slot))) _ _; simp only [cc_apply,jump_apply]; split; next h=> simp [Matrix.one_apply]; split <;> simp; exact Or.inl (a.real_payA _) -- tune
    rw [star_zero]
 apply Subtype.ext; ext ⟨⟨i,u⟩,p⟩ ⟨⟨j,v⟩,q⟩; exact Matrix.ext_iff.mpr (Subtype.ext_iff.mp he) (i,u,p) (j,v,q)
lemma rally_m(a:Shape)(X: Op (Single N)): ZoneH a (rally N X)=rally N (ZoneH a X):=by
 let U:=prepU a (spinX a.s) inert N; let W:=axle N
 have he: U*W=W*ccU U:=by
    have hx: joinX a diva=a ∧ joinX diva a=a:= by simp [joinX, diva, incX]
    unfold U; rw [show W=prepU diva axS inert N from rfl,ventU,kio,kio,hx.1,hx.2]
    rw [show spinX a.s*axS=axS*ccU (spinX a.s) from Subtype.ext (bud_s a.s).justice]
 have ht:rally N (ape N a X)=ape N a (rally N X):=by
    change twist W (cc (twist U X))=twist U (twist W (cc X)); rw [← twin, he,twin,twist_formula U,cc_mul, cc_mul, cc_star]; rfl
 rw [zone_c,zone_c]; unfold Thera.jazz; split; · rw [←ht, map_neg]; congr 1; change star (twist W (cc _))= twist W (cc (star _)); rw [cc_star, map_star] -- tune
 exact ht.symm
private lemma axle_i(x:Site N):(lagX 0).payA x=1:=by
 have hx:= infT x (0:Cover); simp only [map_zero,add_zero] at hx; have ht:=add_eq_left.mp hx; have hh: periods N (natural x)=0:= (nsmul_right_injective (M:=Cover) N.property.ne' (by simpa only [smul_zero])); rw [lag_p]; simp [Rush.wind,hh,Rush.fee]
def twinH : Equiv.Perm SpinIdx:= Equiv.swap 0 1 * Equiv.swap 2 3
def twinHop (N:Side):Equiv.Perm (HopK N):= Equiv.prodCongr (Equiv.refl _) twinH
def twinE (N:Side):Equiv.Perm (Single N):=Equiv.prodCongr (twinHop N) (Equiv.refl _)
def glare(i:SpinIdx):ℝ:= if i=0 ∨ i=2 then 1 else -1
lemma glance(i j:SpinIdx): spinJ i j= if j=twinH i then ↑(glare i) else 0:=by
 have h:twinH (0:SpinIdx)=1∧twinH 1=0∧twinH 2=3∧ twinH 3=2:=by decide
 rcases h with ⟨h,i',t,u⟩; fin_cases i<;> fin_cases j <;> simp (config := {decide:=true}) [*,spinJ,glare] 
lemma bin_p(i j: Single N): (axle N).val i j=if j=twinE N i then ↑(glare i.1.2) else 0:=by
 obtain ⟨⟨i,a⟩,v⟩:=i; obtain ⟨⟨j,b⟩,w⟩:=j
 change jump (Tofu (lagX 0) N) (fun i=> (lagX 0).payA i • (spinJ ⊗ₖ (1:Op SU.Slot))) (i,a,v) (j,b,w)= _; rw [jump_apply,axle_i,one_smul, Matrix.kroneckerMap_apply, glance,Matrix.one_apply]
 rw [show (Tofu (lagX 0) N) i=i from by change Shape.mills (lagX 0) _ _=_; rw [lag_i,map_zero,add_zero]]; change _= if (⟨(j,b),w⟩ : Single _) = ((i,twinH a),v) then (↑(glare a):ℂ) else 0; by_cases hi:j=i<;> by_cases hw:v=w<;> by_cases he:b=twinH a<;>simp [hi,hw,he,Ne.symm]
lemma riot_p(X:Op (Single N))(i j:Single N): rally N X i j= (glare i.1.2 * glare j.1.2) • star (X (twinE N i) (twinE N j)):=by
 rw [show rally N X= twist (axle N) (cc X) from rfl,twist_formula, mul_apply]; have he(k): star (axle N).val k j=star ((axle N).val j k):=rfl
 rw [sum_eq_single (twinE N j),he,bin_p, if_pos rfl,mul_apply]
 rotate_left -- subgoals
 · intro k _ h; rw [he,bin_p, if_neg h,star_zero,mul_zero]
 · simp
 rw [sum_eq_single (twinE N i),bin_p,if_pos rfl]; simp [Complex.real_smul]; ring; intro k _ h; rw [bin_p, if_neg h,zero_mul]; simp
lemma relay_n(X: Op (Single N)): rally N (rally N X)=X:=by
 have hx(i:SpinIdx): glare i*glare (twinH i)= -1 ∧ twinH (twinH i)=i:=by fin_cases i<;> simp [glare,twinH,SpinIdx,Equiv.swap_apply_def]; -- tune
 have ht(i:Single N):twinE N (twinE N i)=i:= Prod.ext (Prod.ext rfl (hx i.1.2).2) rfl
 ext i j; rw [riot_p,riot_p,ht,ht, star_smul,star_star, smul_smul,star_trivial]; rw [mul_mul_mul_comm]; change (glare _*glare (twinH i.1.2)*(glare _*glare (twinH j.1.2))) • _ = _; rw [(hx _).1,(hx _).1]; simp
end YM.CF.Reef
