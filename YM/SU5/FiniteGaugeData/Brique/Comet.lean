import YM.SU5.FiniteGaugeData.Brique.Cellar
import YM.SU5.FiniteGaugeData.Brique.Frequency
/-! # thickness purchase: rare (1-p) columns with upper node pinned but all others sampled adaptively
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Tenant Fock Fock.Brique Tulip Dial Fir Ember Buffered Branch
attribute [local instance] opCStarAlgebra
variable {N : Side} {k d w:ℕ} {e r b:ℝ}
local notation "Μ" => Single N
set_option quotPrecheck false
abbrev atSites (S:Finset (Site N)):= matterSet N S
local notation "Φ" x:max => atSites x
local notation "ϕ" x:max => cutM (atSites x)
@[simp] lemma sites_eq (x:Single N)(S:Finset (Site N)): x∈ atSites S ↔ x.1.1∈ S:= mem_matterSet ..
-- card enumeration untouched. 
def implant (S:Finset (Site N))(A:Op (Single N)):Op (Single N):= cutM (atSites S)*A*cutM (atSites S)
variable {A P Q:Op (Single N)} {S V:Finset (Site N)}
lemma implant_left (S:Finset (Site N))(A:Op (Single N)): Cellar (Φ S) (implant S A):=by
 constructor
 · unfold implant; simp only [←mul_assoc,cut_meet, inter_self]
 unfold implant; rw [mul_assoc _ (ϕ S) (ϕ S),cut_meet,inter_self]
lemma implant_apply (i j:Single N): implant S A i j=if i.1.1∈S∧ j.1.1∈S then A i j else 0:=by
 unfold implant cutM; by_cases h:i.1.1∈ S <;> by_cases g:j.1.1∈ S <;> simp_all [Matrix.mul_diagonal, Matrix.diagonal_mul]
lemma implant_sub (S:Finset (Site N))(A B:Op (Single N)): implant S (A-B)=implant S A- implant S B:=by simp only [implant,mul_sub,sub_mul]
lemma implant_cut (S:Finset (Site N))(A: Op (Single N)): ‖implant S A‖ ≤ ‖A‖:=by
 refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg ((ϕ S) * A)) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg A) ((cutM_idp _).norm_le _))))
lemma cell_slot_eq (S:Finset (Site N))(p:S⊆V): Φ S ⊆ Φ V := by simp [Finset.subset_iff]; intro i j; exact p j
lemma slots_append (S T:Finset (Site N)): Φ (S∪T)=Φ S ∪ Φ T:=by ext; simp
lemma slots_disjoint (S T:Finset (Site N))(h:Disjoint S T):Disjoint (Φ S) (Φ T):=by
 refine Finset.disjoint_left.mpr ?_; intro _ a b; exact Finset.disjoint_left.mp h ((sites_eq ..).mp a) ((sites_eq ..).mp b)
lemma Pins_cell (S:Finset (Site N))(A:Op (Single N)):Cellar (Φ S) (∑ i∈S, implant {i} A):=by
 induction S using Finset.induction_on with
 | empty=> rw [sum_empty]; exact Cellar.no_room _
 | @insert i T p ih=> rw [sum_insert p]; exact ((implant_left {i} A).stock (cell_slot_eq _ (singleton_subset_iff.mpr (mem_insert_self ..)))).add (ih.stock (cell_slot_eq _ (subset_insert ..)))
lemma Pins_bill (p:0≤r)(S:Finset (Site N))(A:Op (Single N))(t:∀ j∈S,‖implant {j} A‖≤ r) : ‖∑ i∈S, implant {i} A‖≤ r:=by
 induction S using Finset.induction_on with
 | empty=> simpa
 | @insert i T h ih=> rw [sum_insert h]; exact duo_max (implant_left {i} A) (Pins_cell T A) (slots_disjoint _ _ (Finset.disjoint_singleton_left.mpr h)) (t i (mem_insert_self ..)) (ih fun j e=> t j (mem_insert_of_mem e))
lemma Pins_apply (S:Finset (Site N))(A:Op (Single N))(i j: Single N): (∑ x∈ S,implant {x} A) i j = if i.1.1∈S ∧ j.1.1=i.1.1 then A i j else 0:=by
 rw [Matrix.sum_apply]; simp_rw [implant_apply,mem_singleton]; by_cases h: j.1.1=i.1.1
 · simp [h]
 rw [if_neg (fun g=> h g.2)]; refine sum_eq_zero fun x _=>if_neg fun p=>h (p.2.trans p.1.symm)
-- for Sparse, all x≠y modes orth kin. radius `R` required.
def Sparse (D:ℕ)(S:Finset (Site N)):= (S:Set (Site N)).Pairwise fun x y => D < separation (node x) (node y)
lemma Sparse.install (u:Neighbor w P)(v:Sparse w S): implant S P= ∑ i∈ S, implant {i} P:=by
 ext i j; rw [implant_apply,Pins_apply]; by_cases p:i.1.1∈ S; swap; · simp [p]
 by_cases b:j.1.1=i.1.1; · simp [p,b]
 by_cases h:j.1.1 ∈ S
 · have ht:=neighbor_iff u i j (v (show i.1.1∈ (S:Set (Site N)) from p) h  (Ne.symm b)); simp [p,b,h,ht]
 simp [p,b,h]
lemma combined (u:Neighbor w P)(h: ‖P-Q‖≤ e)(v: Sparse w S)(t:0 ≤ r)(g:∀ i∈ S,‖implant {i} Q‖ ≤ r) : ‖implant S Q‖ ≤ r+2*e:=by
 let D:=implant S; have he(x:Finset (Site N)):‖implant x P-implant x Q‖ ≤ e := by rw [←implant_sub]; exact (implant_cut ..).trans h
 have hp: ∀ i∈S,‖implant {i} P‖ ≤ r+e :=fun i p=>by linarith only [g i p,(norm_sub_norm_le ..).trans (he {i})]
 have he':0≤ e:=(norm_nonneg _).trans h
 have hP: ‖implant S P‖ ≤ r+e:= (by rw [v.install u]; exact Pins_bill (add_nonneg t he') _ _ hp)
 have z:=norm_sub_rev (implant S Q) (implant S P); linarith only [hP,(norm_sub_norm_le ..).trans (z.trans_le (he S))]
lemma coords (k:ℕ)(hk:1≤k)(M:Male)(t:0≤r)(u:r ≤ pilotB N k M ∧ pilotB N k M ≤1-r)(x:Site N): ‖implant {x} (funde k M N 1)‖ ≤ 1-r:=by
 let D:=implant {x} (funde k M N 1); have hx: r≤1:=by linarith only [u.1,u.2]
 let A(i j: Single N):=if i=j then 1-r else 0
 have hU :∀ i j:Single N,‖D i j‖ ≤ A i j:=by
    intro i j; obtain ⟨⟨i,a⟩,k'⟩:=i; obtain ⟨⟨j,b⟩,l'⟩:=j; unfold A D; rw [implant_apply]; simp only [mem_singleton]; by_cases h:i=x∧ j=x; swap; · rw [if_neg h,norm_zero]; split; exact sub_nonneg.mpr hx; exact le_rfl
    obtain ⟨hx',hy⟩:=h; subst i j -- tune
    rw [if_pos ⟨rfl,rfl⟩,sell_diag k hk]; simp only [Prod.mk.injEq,true_and]; split
    next v=>
        obtain ⟨u₁,u₂⟩:= u; split; next t'=> rw [Complex.norm_real, Real.norm_of_nonneg (t.trans u₁)]; exact u₂
        rw [show 1-(pilotB N k M:ℂ)= ((1-pilotB N k M:ℝ):ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 1-pilotB N k M)]; linarith
    next v=> rw [norm_zero]
 apply Branch.schur A D _ (sub_nonneg.mpr hx) hU <;> (intro i; simp [A])

lemma shroom (S:Finset (Site N)):atSites S= modesIn N (S.image node):=by
 ext; simp [Tenant.needle.eq_iff] -- needle may not injective def?
lemma Neighbor.adj (h:Neighbor w A): Neighbor w (star A):= neighbor_entry fun i j t=>by rw [Matrix.star_apply,neighbor_iff h j i ((separation_comm ..).symm ▸ t),star_zero] -- orientation
lemma implant_early (Q:Op Μ) (S:Finset (Site N))(h:‖implant S Q‖≤ 1-e)(t:0<e): IsUnit (1-implant S Q) := isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt h (by linarith))
section
variable (S:Finset (Site N))(Q:Op (Single N)) (u:IsUnit (1-implant S Q)) (T:Support (More N))
local notation "Ε" => 1-implant S Q -- everywhere operator, not compressed inverse!
local notation "Δ" => (1-implant S Q)⁻¹
local notation "Κ" => cutM (modesIn N T)
include u
lemma implant_inv (h:‖implant S Q‖≤ 1-e)(t:0<e): ‖(1-implant S Q)⁻¹‖≤e⁻¹:=by
 have he: Δ=1+implant S Q*Δ:= by
    have hu:= (live u).1; rw [sub_mul,one_mul] at hu; exact eq_add_of_sub_eq hu
 have hz:= norm_add_le (1:Op Μ) (implant S Q*Δ); rw [←he,norm_one] at hz; rw [←one_div e, le_div_iff₀ t]; nlinarith only [hz,(norm_mul_le (implant S Q) Δ).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))]
omit u in
lemma unit_com {n:Type*}[DecidableEq n][Fintype n]{Q X:Op n}(t:Commute X Q)(h:IsUnit Q):Commute X Q⁻¹:=by
 let G:=Q⁻¹; change X*G=G*X; calc
    _ = G*Q*(X*G) := by rw [show G*Q=1 from (live h).2,one_mul]
    _ = G*(X*(Q*G)) := by rw [mul_assoc G, ←mul_assoc Q,←t.eq, mul_assoc X]
    _ = _:=by rw [show Q*G=1 from (live h).1,mul_one]
lemma implant_basis : Commute (ϕ S) Δ:=by
 have he : Commute (ϕ S) (Ε):=by
    change _*(1-implant _ _)= (1-implant _ _)*_; rw [sub_mul,mul_sub,(implant_left ..).leftP,(implant_left ..).rightP,one_mul,mul_one]
 exact unit_com he u
-- Marker construction re-synth from a full set of sparse seeds. Exact pins on all atSites S. This leaves **all** unlike lower coordinates on seeds exactly untouched. use only ns boost, no price per activated mark!
def SampleOp : Op Μ:= Κ*(1-Q) * (ϕ S)* Δ*(ϕ S)
lemma pins_value (h:S.image node ⊆ T): (ϕ S)*SampleOp S Q T=ϕ S := by
 let X:=ϕ S; have hx:ϕ S*Κ=X:= by rw [shroom,cut_meet,inter_eq_left.mpr (modes_monotone h)]; exact (congrArg cutM (shroom S)).symm
 let Y:=implant S Q; have he: (ϕ S)*(1-Q)*(ϕ S) = (1-Y)*X:=by
    rw [mul_sub, mul_one,sub_mul,(show ϕ S * ϕ S=ϕ S from (cutM_idp _).1),sub_mul (1: Op Μ) Y, one_mul, (show Y*X=Y from (implant_left ..).rightP)]; rfl
 unfold SampleOp; simp only [←mul_assoc]; rw [hx, show X=ϕ S from rfl,he]; change (1-implant S Q)*X*Δ*X=X; rw [mul_assoc _ X, (implant_basis S Q u).eq,←mul_assoc _ Δ,(live u).1,one_mul]; exact (cutM_idp _).1
lemma sample_size (h:‖implant S Q‖≤ 1-e)(t:0<e)(g:IsStarProjection Q): ‖SampleOp S Q T‖ ≤ e⁻¹:=by
 let X:= ϕ S; unfold SampleOp; have hp(A B:Op Μ)(h: ‖A‖ ≤1)(g:‖B‖≤1): ‖A*B‖≤1:= (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) h).trans g)
 have he: ‖Κ*(1-Q)*X‖ ≤1:= hp _ _ (hp _ _ ((cutM_idp _).norm_le _) (g.one_sub.norm_le _)) ((cutM_idp _).norm_le _); exact (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans (implant_inv S Q u h t))))
omit u in
lemma sample_region : Κ*SampleOp S Q T= SampleOp S Q T:=by unfold SampleOp; simp only [←mul_assoc,cut_meet,inter_self]
-- volume uniform tilt approximation via lower candidate horizon
lemma sample_spill (h: Lattice.halo w (S.image node)⊆T)(hu:‖implant S Q‖≤1-e)(t:0<e)(g:IsStarProjection Q)(p:∃ B, Neighbor w B ∧ ‖B-Q‖ ≤ b):‖Q*SampleOp S Q T‖ ≤ b*e⁻¹:=by
 obtain ⟨Y,hX,hY⟩:=p
 let U:=Κ; let X:=ϕ S; let E:= (1-Q)*X; let P:= SampleOp S Q T
 have he: Q*P = (Q*(U*E-E))*Δ*X:=by
    rw [mul_sub,show Q*E=0 by unfold E; rw [←mul_assoc,Porth g,zero_mul],sub_zero]; simp only [E,P,X,U,SampleOp,mul_assoc]
 have ht:X=(ϕ S):=rfl; have hx: U*Y*X=Y*X:=by -- adj neighbor, t⋆
    have hX:= Neighbor.adj hX (A:=Y); have hw:= hX _ _ h; rw [←shroom] at hw; have hi:=congrArg star hw; simp only [star_mul,star_star,(cutM_idp _).2.star_eq] at hi; exact mul_assoc U Y X ▸ hi -- eq transport direction
 have hl: U*X=X:=by
    have hS: S.image node⊆T:= Subset.trans (halo_subset ..) h; unfold X U; rw [shroom,cut_meet,inter_eq_right.mpr (modes_monotone hS)]
 have hp: ‖U*E-E‖ ≤ b:=by
    have H:(1-U)*Y*X=0:=by rw [sub_mul,sub_mul,one_mul, hx,sub_self] -- tune
    rw [show U*E-E = (1-U)*(Q-Y)*X from (by unfold E; rw [mul_sub (1-U), sub_mul ((1-U)*Q) _ X, H,sub_zero,sub_mul _ Q,one_mul,mul_sub,←mul_assoc U, hl, sub_mul (1:Op Μ) U,one_mul,sub_mul]; abel)] -- tune
    refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).one_sub.norm_le _)).trans ((norm_sub_rev _ _).trans_le hY))))
 rw [show Q*_=_ from he]; refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _)).trans ((norm_mul_le ..).trans ?_)); apply mul_le_mul _ (implant_inv S Q u hu t) (norm_nonneg _) ((norm_nonneg _).trans hp); exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (g.norm_le _)).trans hp)
-- also preserves custom algebra of Slots when T gauged. need proof in next module. 
end
end YM.CF.Window.Brique
