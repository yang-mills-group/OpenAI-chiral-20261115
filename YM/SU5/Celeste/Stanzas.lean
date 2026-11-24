import YM.SU5.Celeste.Hammock
/-! # Flat comparisons BEFORE pruning. tools. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Lamour.Bridge.Celeste
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed
open Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
-- cluster via `forest_WAKE`
section
variable {I:Type*} [LinearOrder I][Fintype I]
  {S T:Finset I} {E F:Op I}
lemma pf_agree (e:Eᵀ= -E)(p:Fᵀ= -F)(q:Grass S T)(g:∀ i∈ S,∀ j∈S,E i j=F i j) : pf E S=pf F S:=by
 induction S using Finset.strongInductionOn with
 | _ S ih=> by_cases u:S.Nonempty
            · let i:= S.min' u; let Z:=S.erase i; have ht:i∈S:= min'_mem S u; let h:Z⊂ S:= erase_ssubset ht; let hh: Flies i Z:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase tj)) (mem_erase.mp tj|>.1.symm); -- tune min'_le
              rw [show S=insert i Z from (insert_erase ht).symm,flair e hh,flair p hh]; refine sum_congr rfl fun j w=>?_ ; let hv:=Z.erase j; let U:=erase_subset j Z; let z:Z⊆ S:=erase_subset ..; have hx:hv⊆S:= Finset.Subset.trans U z; rw [show pf E hv=_ from ih _ (Finset.ssubset_of_ssubset_of_subset (erase_ssubset w) z) (grass_sub q hx subset_rfl) (fun i l j y=> g i (hx l) j (hx y)),g _ ht _ (z w)] -- let abbreviation rewrites?
            simp [not_nonempty_iff_eq_empty.mp u,pf,paired_vac]
lemma pf_fold (e:Eᵀ= -E)(p: Grass S T)(g:∀ i∈S,∀ j∈T, E i j=0): pf E (S∪T)=pf E S*pf E T:=by
 induction S using Finset.strongInductionOn with
 | _ S ih=>
   by_cases u:S.Nonempty
   · let i:=S.min' u; let Z:= S.erase i; have ht:i∈S:=min'_mem S u; have hp:Flies i Z:=fun j tj=>lt_of_le_of_ne (min'_le _ _ (mem_of_mem_erase tj)) ((mem_erase.mp tj).1.symm)
     have h: S=insert i Z:= (insert_erase ht).symm; rw [h,insert_union,flair e (show Flies i (Z∪T) from fun j w=>(mem_union.mp w).elim (hp j) (p i ht j)), flair e hp]; have hz:Z⊆S:=erase_subset ..; have hv:=grass_sub p hz (subset_refl T); have hh:= grass_freed hv; rw [sum_union hh, sum_eq_zero (s:=T) (fun j tj=> by rw [g _ ht _ tj,zero_mul]),add_zero,sum_mul]; refine sum_congr rfl fun j v=>?_ ; have hw:Z.erase j ⊆S:= Finset.Subset.trans (erase_subset j Z) hz; rw [erase_union_distrib, erase_eq_of_notMem (fun l=> disjoint_left.mp hh v l), ih _ (Finset.ssubset_of_ssubset_of_subset (erase_ssubset v) hz) (grass_sub p hw subset_rfl) (fun i e j tj=> g i (hw e) j tj),grass_crown hv v]; ring
   rw [not_nonempty_iff_eq_empty.mp u,empty_union, show pf E ∅=1 from paired_vac _,one_mul] -- tactic
lemma pf_tree (e:Eᵀ= -E)(p: Grass S T)(f:Fᵀ= -F)(g:∀ i∈ S,∀ j∈ S, E i j= F i j)(q:∀ i∈ T,∀ j∈ T,E i j=F i j)(u:∀ i∈ S,∀ j∈T,F i j=0): pf F (S∪T)=pf E S*pf E T:=by
 rw [pf_fold f p u,pf_agree e f p g,pf_agree e f (T:=∅) (S:=T) (by simp [Grass, Flies]) q]
variable {n:Type*} [LinearOrder n][Fintype n][Nonempty n]
lemma raw_add (b:I→Bool)(f:I→ Ket n)(q: Grass S T):rawT b f (S∪T)=rawT b f S*rawT b f T:=by
 have ht(K:Finset I)(i:I)(h:Flies i K): rawT b f (insert i K)=creed (b i) (f i)*rawT b f K:=by rw [rawT,sort_insert _ (fun x v=>(h x v).le) (Flies.out h),Pannier.Chancel.fo,List.map_cons,List.prod_cons]; rfl
 induction S using Finset.induction_on_min with
 | empty=> simp [show rawT b f ∅=1 from (by simp [rawT,Pannier.Chancel.fo])]
 | insert i A v ih=> rw [insert_union,ht (A∪T) i (fun j t=> (mem_union.mp t).elim (v j) (q i (mem_insert_self ..) j)),ht A i v, ih (grass_sub q (subset_insert ..) subset_rfl),mul_assoc]
local notation "♡"=> Fin 2 ×ₗ n
def fieldPair (Z:Op ♡):Op (Fin 2 ×ₗ n):= Matrix.of fun i j=> if (ofLex i).1=(ofLex j).1 then Z i j else 0
lemma field_sym (Z:Op (Fin 2 ×ₗ n))(p:Zᵀ= -Z): (fieldPair Z)ᵀ= -(fieldPair Z):=by
 ext i j; have ht:Z j i= -Z i j:= congr_fun (congr_fun p i) j; unfold fieldPair; by_cases e:(ofLex i).1=(ofLex j).1; rw [Matrix.transpose_apply,Matrix.neg_apply,Matrix.of_apply,Matrix.of_apply]; rw [if_pos e,if_pos e.symm]; exact ht; simp [e,Ne.symm e]
def clusterPay (d:ℕ)(z:ℝ):ℝ:= plumeE (2*d) ((↑(2*d):ℝ)+1+z) z (2*d)
lemma cluster_non {d:ℕ}{v:ℝ}(h:0≤v): 0≤clusterPay d v:= plume_non (d:=2*d) (show 0≤ (↑(2*d):ℝ)+1+v from by positivity) h
variable {B L Z:Op n} {X Y T S R D:Finset n} {d:ℕ}{p q:Wave n}
  (h:Clad B (cutM T) 1 1 Z)(u:L=laneP (cutM T) 1 Z)(e:Sea B p)(r:Sea (cutM T) q)
variable {v w:ℝ} (z:0≤v)(o:0≤w)
include h u e r z o
lemma cluster_loose (lx:X.card ≤ d)(ly:Y.card ≤ d)(s:S⊆ X)(t:R⊆Y)
    (g:∀ i j:n,‖ray L T i j‖≤v) (f:∀ i∈X,∀ j∈Y,‖ray L T i j‖≤ w):
    ‖alleyR q p (tome T S*tome T R)-alleyR q p (tome T S)*alleyR q p (tome T R)‖≤ w*clusterPay d v:=by
 let K:= Hail (bass (I:=Fin 2) T) vpf L; let E:=fieldPair K; let k0:= (0:Fin 2); let k1:= (1:Fin 2); let A:= carton k0 S; let F:= carton k1 R; let P:= A ∪ F; have hl:k0 < k1:=by decide
 have hK:Kᵀ= -K:=hail_turn ..; have he: Eᵀ= -E:= field_sym _ hK; let U:=alleyR q p; let W (S:Finset (Fin 2 ×ₗ n)):= rawT (bass T) vpf S
 have hp (a:Finset (Fin 2 ×ₗ n)): U (W a)= pf K a:=armed_pay _ _ a h u r e (fun j=>seedTrim ..); have hz:Grass A F:=carton_grass _ _ _ _ hl; have ht(D:Finset n)(j:Fin 2): ∀ i∈ carton j D,∀ k∈carton j D, K i k=E i k:=by
    intro i p k q; unfold E fieldPair; simp only [Matrix.of_apply, (urn ..).1 p|>.1, (urn ..).1 q|>.1,ite_true] -- lemma syntax?
 have hq(i j: Fin 2)(a b:n): K (nestV i a) (nestV j b)=ray L T a b:=rfl
 have hg(i j: Fin 2)(p:i≠j)(X Y:Finset n):∀ v∈ carton i X,∀ w∈ carton j Y,E v w=0:=by intro v t k q; unfold E fieldPair; simp only [Matrix.of_apply,(urn ..).1 t|>.1,(urn ..).1 q|>.1,if_neg p]
 have hv:= pf_tree hK hz he (ht S k0) (ht R k1) (hg _ _ hl.ne S R)
 have hx:P.card≤2*d:=by unfold P; rw [card_union_of_disjoint (grass_freed hz),show A.card=S.card from card_map _,show F.card=R.card from card_map _,two_mul]; exact Nat.add_le_add ((card_le_card s).trans lx) ((card_le_card t).trans ly)
 have ha: X.card ≤d:=lx; rw [←carton_comm k0 T S,←carton_comm k1 T R,←raw_add _ _ hz]; change ‖U (W P)-U (W A)*U (W F)‖ ≤ _; rw [hp,hp,hp,←hv]
 have h0(i j: Fin 2 ×ₗ n): ‖K i j‖≤v:=g _ _; have h1(i j: Fin 2 ×ₗ n): ‖E i j‖≤v:=by unfold E fieldPair; rw [Matrix.of_apply]; split; apply h0; simpa using z
 change ‖pf K P-pf E P‖≤_; refine shawl (show 1≤ ((↑(2*d):ℝ)+1+v) from by linarith [Nat.cast_nonneg (α:=ℝ) (2*d)]) o z hK he (warp_bound (2*d) hx z fun i _ j _=>h1 i j) (fun i _ j _=>h0 i j) ?_ (2*d) hx (2*d) subset_rfl hx
 have hh(i: Fin 2 ×ₗ n)(p:i∈A)(j)(q:j∈F): ‖K i j-E i j‖≤w:=by rw [hg _ _ hl.ne S R _ p _ q,sub_zero]; exact f _ (s ((urn ..).1 p|>.2)) _ (t ((urn ..).1 q|>.2))
 intro i p j q; rcases mem_union.mp p with p|p <;> rcases mem_union.mp q with q|q
 · rw [ht _ _ i p j q,sub_self,norm_zero]; exact o
 · exact hh i p j q
 · rw [show K i j-E i j= -(K j i-E j i) from (by rw [show K i j= -K j i from congr_fun (congr_fun hK j) i,show E i j= -E j i from congr_fun (congr_fun he j) i]; abel),norm_neg]; exact hh j q i p
 rw [ht _ _ i p j q,sub_self,norm_zero]; exact o
lemma clusterPrice (lx:X.card ≤ d)(ly:Y.card ≤ d)(A C:FC n)(tX: Fine T X false A)(tY:Fine T Y false C)(g:∀ i j:n,‖ray L T i j‖≤v) (f:∀ i∈X,∀ j∈Y,‖ray L T i j‖≤ w):
 ‖alleyR q p (A*C)-alleyR q p A*alleyR q p C‖≤ 2^(2*d)*‖A‖*‖C‖*(w*clusterPay d v):=by
 let F:=alleyR q p; let U(x y:FC n):= F (x*y)-F x*F y; obtain ⟨a,F₁,A0⟩:=farm_bill tX; obtain ⟨c,F₂,B0⟩:=farm_bill tY
 let cl:=w*clusterPay d v; have hc:0≤cl:=mul_nonneg o (cluster_non z); let V:= ‖A‖; let K:= ‖C‖; change ‖U A C‖≤ _*V*K*cl
 have hum(Z J:FC n)(c a:ℂ): U (c • Z) (a • J)= c*a*U Z J:=by unfold U; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,map_smul,map_smul]; simp only [smul_eq_mul]; ring
 rw [show U A C=∑ i∈ X.powerset,∑ j∈ Y.powerset,a i*c j*U (tome T i) (tome T j) from (by rw [A0,B0]; simp_rw [← hum]; unfold U; rw [sum_mul]; simp_rw [mul_sum,map_sum,sum_mul,mul_sum,sum_sub_distrib])]; apply (norm_sum_le ..).trans
 apply le_trans (b:=∑ _∈ X.powerset,∑ _∈ Y.powerset,V*K*cl) (sum_le_sum ?_) ?_
 · intro i p; refine (norm_sum_le ..).trans (sum_le_sum (fun j q=>?_ )); rw [norm_mul,norm_mul]; exact mul_le_mul (mul_le_mul (F₁ i (mem_powerset.mp p)) (F₂ j (mem_powerset.mp q)) (norm_nonneg _) (norm_nonneg _)) (cluster_loose h u e r z o lx ly (mem_powerset.mp p) (mem_powerset.mp q) g f) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
 simp only [sum_const, card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat];
 calc _ ≤ 2^d*((2:ℝ)^d*(V*K*cl)):=by have h0:0≤ V:=norm_nonneg _; have h1:0≤K:=norm_nonneg _; gcongr <;> norm_num
      _=_:= by rw [two_mul,pow_add]; ring
end
variable {N:Side}{S T:Finset (Seat N)} {p q₀ j:ℕ}{M:Tulip.Male}{K:Op (Single N)} -- N implicit? add
variable (h:1≤j)(t:Kea.Pad j N)
local notation "Ⓣ"=> Tset N
lemma ray_here (i k:Single N)(A:Op (Single N))(p:A i k=0)(q:A k i=0): ray A (Tset N) i k=0:=by change fern (shadeK (Tset N) i) _ A _ _=0; unfold fern; split; rfl; split; simp [basis_inner,basis_act,p]; simp [basis_inner,basis_act,q] -- if syntax
lemma RayCold (h:Glaze.Ranged p K)(e:Distant (p+1) S T)(i k)(g:i∈modesIn N S)(v:k∈modesIn N T): ray K (Tset N) i k=0:= ray_here i k K (h i k (e _ ((modes_at ..).1 g) _ ((modes_at ..).1 v))) (h k i (Distant.symm e _ ((modes_at ..).1 v) _ ((modes_at ..).1 g)))
include h t in
lemma alley_one(x:Wave (Single N))(u:Sea (spar j M (1:Pane N)) x):alleyR (mateK N) x 1=1:=by
 replace u: Sea (Kea.Dofu N (Kea.field (Kea.too N) j M)) x:= (coasting t M) ▸ u
 have he:= shines (pitch M h t.1).1 x (mateK N) u (tickB N); rw [skyGlow,quant_one,act_one] at he; exact (show (inner ℂ (mateK N) x)⁻¹*inner ℂ _ (acts (1:FC (Single N)) x)=_ from (by rw [act_one, inv_mul_cancel₀ he]))
abbrev Heather (w:ℝ)(d p:ℕ)(C ε:ℝ)(j:ℕ)(N:Side):Prop:=∀ M:Tulip.Male,∀ S T:Finset (Seat N),S.card≤d →T.card ≤d → Distant (p+1) S T →∀ (x Y: FC (Single N))(q:Wave (Single N)),‖x‖≤C → ‖Y‖≤C →Fine (Tset N) (modesIn N S) false x→Fine (Tset N) (modesIn N T) false Y→Sea (spar j M (1:Pane N)) q → let E:=alleyR (mateK N) q; ‖E (x*Y)-E x*E Y‖≤ε
include h in
lemma fragments(p:ℕ)(C:ℝ)(u:0≤C)(e:ℝ)(z:0<e):∃ w:ℕ,∀ᶠ N:Side in atTop,Even N.val→Heather 0 p w C e j N :=by
 obtain ⟨x,v,hq,k⟩:= stockyard h; let d:=180*p; let A:= 2^(2*d)*(C*C)*clusterPay d x; let τ:=e/(A+1); have hx:0≤ A:=by unfold A; have ht:=cluster_non (d:=d) v.le; positivity
 have hp: 0<τ:=by unfold τ; positivity
 obtain ⟨a,w,h0⟩:=k τ hp; refine ⟨w,?_⟩; filter_upwards [eventually_ge_atTop (⟨a+1,by omega⟩:Side),ownsHalo h] with N h₀ τX m M S T lx ly r X Q y hX hQ SX TY Hy; let L:=lake N j M; let V:= Tset N; have ht:=τX m; obtain ⟨K,p₁,p₂⟩:= h0 ht.1 (by change a+1 ≤ N.val at h₀; omega) M; have hu:= hq m M; let K':=Kea.Dofu N (lakeK N j M); have he:=touchP N; intro E
 have h' : ‖E (X*Q)-E X*E Q‖≤2^(2*d)*‖X‖*‖Q‖*(τ*clusterPay d x):=clusterPrice (Z:=K') ((coasting ht.1 M).symm ▸ he ▸ (pitch M h m).1) (L:=L) (he ▸ (pitch M h m).2) Hy (he ▸ tickB N) v.le hp.le ((acreage ..).trans (Nat.mul_le_mul_left _ lx)) ((acreage ..).trans (Nat.mul_le_mul_left _ ly)) _ _ SX TY (fun i t=> Wat.ray_p (W:=univ) (P:=L) (fun k _=> (hu k).1) (fun k _=> (hu k).2) V i t (mem_univ _)) (fun i ti k tk=> by apply (ray_toll (d:=0) (j:=0) (P:=L) (L:=K) (W:=univ) (ε:=τ) (fun k _=>(p₂ k).1) (fun k _=>(p₂ k).2) le_rfl V i k (mem_univ _)).trans'; rw [RayCold p₁ r i k ti tk,sub_zero]) -- binder j conflict implicit L partially
 apply h'.trans; apply le_trans (b:=2^(2*d)*C*C*(τ*clusterPay d x)) ?_ ?_
 · have hL:= cluster_non (d:=d) v.le; gcongr
 have hτ:τ*(A+1)=e:= div_mul_cancel₀ _ (by positivity); apply le_trans (b:=τ*A) (le_of_eq (by unfold A; ring)) ?_; linarith
end YM.CF.Lamour.Bridge.Celeste
#print axioms YM.CF.Lamour.Bridge.Celeste.clusterPrice
#print axioms YM.CF.Lamour.Bridge.Celeste.fragments
