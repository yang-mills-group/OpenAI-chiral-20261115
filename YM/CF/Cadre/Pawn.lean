import YM.CF.Cadre.Dash
import YM.CF.Cadre.Byte
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
-- formal flow coefficients packed locally autonomous per volume and parameter
open PowerSeries
variable {M:Type*}[CommRing M][Algebra ℝ M]
abbrev lace(A M:Type*):= leaf A→ Finset A→ PowerSeries M
abbrev Rinse(A M: Type*):=leaf A→ Finset A→ leaf A→ M→ M
abbrev grate (K:Rinse A M)(Z:lace A M)(X:ΣA)(U:Finset A)(Y:ΣA)(F:ΣG):PowerSeries M:=mk fun n=> K X U Y (coeff n (∏ j∈F, Z j (U∩j.val)))
variable (K:Rinse A M)(X: Palot.leaf A)(Z:lace A M)
abbrev rill (f:Finset ΣG)(X:ΣA)(D:Finset A)(Y:ΣA):PowerSeries M:=∑ G∈ drum X Y D ∩ f, grate K Z X D Y G
abbrev stepL (X:ΣA)(D:Finset A):=∑ Y:ΣA,rill K Z univ X D Y
lemma rils(i:ℕ)(l:Finset ΣG): coeff i (rill K Z l X D Y) = ∑ F∈drum X Y D ∩ l, K X D Y (coeff i (∏ j∈F,Z j (D∩j.val))):=by unfold rill grate; rw [map_sum]; exact sum_congr rfl fun _ _=> by rw [coeff_mk]
lemma ore(i:ℕ):coeff i (stepL K Z X D)=∑ Y:ΣA,∑ F∈drum X Y D, K X D Y (coeff i (∏ j∈F,Z j (D∩j.val))):=by unfold stepL; rw [map_sum]; refine sum_congr rfl fun i' _=>?_ ; rw [rils,inter_univ]
lemma tamp {V: lace A M}{n:ℕ}(W:∀ X:ΣA,∀ D:Finset A,∀ i≤n,coeff i (Z X D)=coeff i (V X D)) : coeff n (stepL K Z X D)=coeff n (stepL K V X D):=by
 rw [ore,ore]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro F g; rw [coeff_prod,coeff_prod]; apply congrArg (K X D i); apply sum_congr rfl; intro s p; apply prod_congr rfl; intro y q; exact W _ _ _ ((single_le_sum (fun j _=> Nat.zero_le (s j)) q).trans_eq (mem_finsuppAntidiag.mp p).1)
-- primitive integral
abbrev ham(U: PowerSeries M)(z:M):PowerSeries M:= mk fun i => i.casesOn z fun i=>((i:ℝ)+1)⁻¹ • coeff i U -- tune
lemma tick_r(A:PowerSeries M)(z:M):coeff 0 (ham A z)=z:=by unfold ham; rw [coeff_mk]; rfl
lemma sprig(A: PowerSeries M)(z:M)(i:ℕ):coeff (i+1) (ham A z)=((i:ℝ)+1)⁻¹ • coeff i A:=by unfold ham; rw [coeff_mk]
lemma tide(A: PowerSeries M)(z:M):derivative M (ham A z)=A:=by
 ext n; rw [coeff_derivative,mul_comm,sprig]; rw [show (n+1:M)=↑(n+1:ℕ) by push_cast; rfl, ←nsmul_eq_mul, ←Nat.cast_smul_eq_nsmul ℝ]; push_cast; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
variable (z: leaf A→ Finset A→ M)
-- coefficient recursion
local notation "Ψ"=> leaf A→Finset A→ M
def ramp(K:Rinse A M) (z:leaf A→Finset A→ M):ℕ→Ψ
 | 0=>z
 | n+1=>fun X D=>((n:ℝ)+1)⁻¹ • coeff n (stepL K (fun X D=> mk fun i=> if h:i ≤ n then ramp K z i X D else 0) X D)
termination_by i=>i
def chip(K:Rinse A M)(z:leaf A→Finset A→ M):lace A M:=fun X D=>mk fun i=> ramp K z i X D
lemma peel:chip K z X D= ham (stepL K (chip K z) X D) (z X D):=by
 ext n; cases n
 · rw [tick_r,chip,coeff_mk,ramp];
 rename_i i; rw [sprig,chip,coeff_mk,ramp]; apply congrArg; apply tamp; intro x y j h; simp only [chip,coeff_mk,dif_pos h]
lemma dash : derivative M (chip K z X D)=stepL K (chip K z) X D:=by nth_rw 1 [peel D K X]; rw [tide] -- order
lemma peg : coeff 0 (chip K z X D)=z X D:= by rw [peel,tick_r]
-- boot only kernel-only empty G. Remaining grates. Expose decomposition. Need K maps 0 to0
abbrev front (X:ΣA)(D:Finset A): PowerSeries M:=∑ Y:ΣA,rill K (chip K z) (farW A) X D Y
lemma pingT (s:∀ x b y,K x b y 0=0) : stepL K Z X D = (if D.Nonempty then 0 else C (K X ∅ X 1))+ ∑ Y:ΣA,rill K Z (farW A) X D Y:=by
 have he(Y:ΣA):∅∈drum X Y D ↔ X=Y∧D=∅:=by rw [drum_p]; simp [flow,robe, Subtype.ext_iff,and_comm]
 have hv(Y:ΣA):drum X Y D∩ farW A=(drum X Y D).erase ∅:= by
    ext i; rw [mem_inter,mem_erase]; change _∧_ ↔ _∧_; unfold farW; rw [show (i∈ univ.filter (fun G:ΣG=>G.Nonempty)) ↔_ from mem_filter]; simp only [mem_univ,true_and,Finset.nonempty_iff_ne_empty,and_comm]
 unfold stepL rill; simp_rw [inter_univ,hv]; by_cases t:D.Nonempty
 · rw [if_pos t,zero_add]; apply sum_congr rfl; intro i _; rw [erase_eq_of_notMem (fun q=>t.ne_empty ((he _).mp q).2)]
 rw [if_neg t]; have h:D=∅:= Finset.not_nonempty_iff_eq_empty.mp t
 have ht(Y:ΣA): (∑ G∈drum X Y D, grate K Z X D Y G)= (if Y=X then PowerSeries.C (K X ∅ X 1) else 0)+ ∑ G∈(drum X Y D).erase ∅, grate K Z X D Y G:=by
    split_ifs with p; · rw [←add_sum_erase _ _ ((he _).mpr ⟨p.symm,h⟩)]; congr 1; ext i; simp only [grate,coeff_mk,prod_empty,h,p, coeff_C,coeff_one]; split; rfl; rw [s] -- tune
    rw [erase_eq_of_notMem fun t=>p (((he Y).mp t).1.symm),zero_add]
 simp_rw [ht,sum_add_distrib]; simp
abbrev nutL(K:Rinse A M)(z:leaf A→Finset A→ M): lace A M:=fun X D=> ham (front K z X D) 0
lemma park (s:∀ x b y,K x b y 0=0) : let y:=fun i:ℕ=>if i=1∧ D=∅ then K X ∅ X 1 else 0
 chip K z X D= C (z X D)+ mk y+ nutL K z X D:=by
 intro y; ext n; simp_rw [map_add]; cases n
 · rw [peg,tick_r,coeff_mk]; simp [y]
 rename_i i; nth_rw 1 [peel]; rw [sprig,pingT D K X _ s,nutL,sprig,map_add,coeff_mk]; unfold front; rw [coeff_C,smul_add]; unfold y; by_cases p:i=0
 · subst i; by_cases h:D.Nonempty; · simp [h,h.ne_empty]
   simp [h,Finset.not_nonempty_iff_eq_empty.mp h]
 by_cases h:D.Nonempty <;> simp [h,p,coeff_C]
end YM.CF.Cadre
