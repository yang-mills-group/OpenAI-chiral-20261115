import YM.SU5.Lamour.Crystal
/-! # local power gain. At site keeper. Practice on same reader α. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Lamour.Bridge
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Scree CF.Pannier.Damask Buffered Branch Tenant Skye Pannier.Chancel Brace Velvet Hours Flare Cliplet RG Reed Py.Rate.Pannier
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N: Side}{j d r n k a w s t:ℕ}{ε ξ δ z l v θ γ ζ μ τ ν C B b:ℝ}{M:Tulip.Male}{U: Loom N}
variable {I:Type*}[Fintype I][LinearOrder I](L: Finset I) {D:Finset I}(o:I→ Seat N)(S:I→Finset (Seat N))(F:I→Mark N)
/-- any allowable ordering. -/
def cartMark: Mark N:=fun x=> fo (fun i=> F i x) (L.sort (·≤·))
lemma firstMin {n:Type*}[LinearOrder n][Fintype n] (F:I→ FC n)(L:Finset I)(i:I)(h:Flies i L): fo F ((insert i L).sort (· ≤ ·))= F i*fo F (L.sort (· ≤ ·)):=by rw [sort_insert _ (fun x e=>(h x e).le) (Flies.out h)]; rfl
lemma cartMark_ins (i:I) (h:Flies i L):cartMark (insert i L) F=F i*cartMark L F:=funext fun x=> firstMin _ L _ h -- tune
lemma stowM (h:∀ i∈L,AtSupport false (S i) (F i)): AtSupport false univ (cartMark L F):=by
 induction L using Finset.induction_on_min with
 | empty=> rw [show cartMark ∅ F=1 from funext fun x=>by rw [cartMark]; simp [Pannier.Chancel.fo]]; exact AtSupport.oneM _
 | insert i T d ih=> rw [cartMark_ins T F i d]; exact ((h i (mem_insert_self ..)).mono (subset_univ _)).mulM (ih (fun i p=>h i (mem_insert_of_mem p)))
lemma cutThrough (f:Tulip.Male)(x:Fields N)(S T:Finset (Seat N))(F G:Mark N)(u:AtSupport false S F)(v:AtSupport false T G):Commute (F x) (G x):=by
 let H(W: FC (Single N)):= Fine (Tset N) (modesIn N univ) false W
 have h: H (F x):= flightPhys _ univ S u (subset_univ _) _; have ht:H (G x):=flightPhys _ univ T v (subset_univ _) _; unfold Commute SemiconjBy; rw [show _= _ from h.sign_com ht]; simp [Sector.grainB]
lemma parcel_trick (M:Tulip.Male) (x:Fields N) (D:I→Prop)[DecidablePred D][DecidablePred fun i=> ¬D i] (h:∀ i∈L,AtSupport false (S i) (F i)): cartMark L F x=cartMark (L.filter D) F x*cartMark (L.filter fun i=>¬D i) F x:=by
 induction L using Finset.induction_on_min with
 | empty=> simp [cartMark,Pannier.Chancel.fo]
 | insert i T p ih=>
    let J:= T.filter D; let C':= T.filter fun i=> ¬ D i; let k:= ih (fun i v=> h i (mem_insert_of_mem v)); rw [cartMark_ins T F i p,Pi.mul_apply,k]; simp_rw [filter_insert]; by_cases v:D i
    · rw [if_pos v, if_neg (not_not.mpr v),cartMark_ins J F i (Flies.sub p (filter_subset ..)),Pi.mul_apply,mul_assoc]
    rw [if_neg v, if_pos v, cartMark_ins C' F i (Flies.sub p (filter_subset ..)),Pi.mul_apply, ←mul_assoc,show F i x*cartMark J F x= _ from (cutThrough M _ _ _ _ _ (h i (mem_insert_self ..)) (stowM J S F (fun i ti=> h i (mem_insert_of_mem (mem_filter.mp ti).1)))).eq,mul_assoc]
lemma mold_cart (h:0≤ C)(p:0<z)(q:z≤1)(x:Fields N)(H:∀ i∈L,LocalTune j d r ε ζ C B N M (F i) (o i) (S i)): ‖modifyB (tickA _) z (cartMark L F x)‖≤ (C*(2*(flowCost z+1))^d)^L.card:=by
 let A:= moldP (Kea.cut_t N) p; have hp:=flow_pos p
 induction L using Finset.induction_on_min with
 | empty=> change ‖A _‖≤ _; simp [cartMark,Pannier.Chancel.fo]
 | insert i T e ih=>
    change ‖A _‖≤ _; rw [cartMark_ins T F i e, Pi.mul_apply,map_mul,card_insert_of_notMem (Flies.out e),pow_succ']; apply (norm_mul_le ..).trans; have ht:= H i (mem_insert_self ..); have he:‖A (F i x)‖≤ C*(2*(flowCost z+1))^d:=by apply (mold_bill (P:=tickA N) (Kea.cut_t N) p q (ht.range.allV x)).trans; gcongr; exact ht.units x; linarith; exact ht.issued -- tune order
    exact mul_le_mul he (ih (fun i u=> H i (mem_insert_of_mem u))) (norm_nonneg _) (by positivity)
def frostFilter (T:Finset (Seat N))(o:I→Seat N)(s:ℕ)(i:I): Prop := o i∈ Lattice.halo s T
variable (H:Optic j n k d v ε θ l C B)(q:Procurement j a δ)(W:Warrant r s γ ζ τ)(roof: Roof N μ δ t U)
omit H q W roof in
lemma cold_spots (x:Pane N)(s:ℕ)(P:Finset (Seat N))(v:0<v) -- remove unused
  (Q:∀ i∈L, o i∈ S i)(Y:∀ i∈L,∀ j∈L,i≠j→Distant (k+1) (S i) (S j))(V:Finset I)(A:D⊆L)(c:∀ i∈D,frostFilter (flags τ x) o s i): (D.card:ℝ) ≤ (4*((2*s+1:ℕ):ℝ)^4)*flakes τ x:=by
 have he:Set.InjOn o L:=by intro i vi j vj u; by_contra h; have ht:=Y _ vi _ vj h (o i) (Q i vi) (o j) (Q j vj); rw [u,separation_self] at ht; omega
 let E:= flags τ x; have hD: D.image o ⊆ Lattice.halo s E:=image_subset_iff.mpr c
 have hh:= Corona.halo_size E s
 rw [←card_image_of_injOn (he.mono A)]; let K:=(roughness τ x).card*4 * ((s+s+1)^4); have ht: (Lattice.halo s E).card ≤ K:= by apply hh.trans; apply Nat.mul_le_mul; exact flag_coat x τ; gcongr <;> omega
 apply (show ((D.image o).card:ℝ) ≤ (K:ℝ) from Nat.cast_le.mpr ((card_le_card hD).trans ht)).trans_eq; unfold K flakes; push_cast; ring
-- helper fee
def winterFee (d w:ℕ)(B C z:ℝ):ℝ:= Real.log (1+(C*(2*(flowCost z+1))^d)/B)*4*((2*w+1:ℕ):ℝ)^4
include H q W roof
theorem launch (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(g:0≤C)(lB:0<B)(Hp:∀ j'∈ L, LocalTune j d r ε ζ C B N M (F j') (o j') (S j'))(p0:∀ x∈L,∀ y∈L,x≠y →Distant (k+1) (S x) (S y))(y:Wave (Single N))(f:Sea (spar j M (U x)) y):
 let P:= U x; let A:= spar j M P; let G:=tickA N;
 Yep ((z*v)⁻¹*flowCost z) (acts (star (cartMark L F (x.1,P))) (mateK N)) y (Real.exp (trade A G z+ winterFee d (((r+s)+1)+t) B C z * flakes τ x.1 + L.card*Real.log B)) :=by
 classical
 intro P A G; let e:=r+s+1+t; let b:= flags τ x.1; let Y:= frostFilter b o e; let D:=L.filter Y; let E:= L.filter fun z=> ¬ Y z; let F':= cartMark D F (x.1,P); have he:=parcel_trick L S F M (x.1,P) Y (fun i v=>(Hp i v).range)
 let hm(x)(d:x∈E):= (mem_filter.mp d).1; have ha(i)(v:i∈ E): Disjoint (BlockP e (o i)) b:= by
    apply disjoint_left.mpr; intro x h l; exact (mem_filter.mp v).2 (halo_spec.mpr ⟨_,l,(separation_comm ..).trans_le (blocks_test.mp h)⟩)
 have hw:= poised H q W roof H₁ h p z0 z1 c a' x hx ht o S F E (fun i h=> Hp i (hm i h)) (fun i hi j hj=> p0 _ (hm i hi) _ (hm j hj)) ha y f F';
 let V:= trade A G z; have hv:=flow_pos z0; let C':=C*(2*(flowCost z+1))^d; let κ:= 1+C'/B; have hy:0≤C':=by unfold C'; positivity
 have hs:1≤κ:=le_add_of_nonneg_right (by positivity); let J:=κ^D.card; let v0:=winterFee d e B C z; let l0:=L.card*Real.log B
 rw [show cartMark L F (x.1,P)=F' * fo (fun i=>F i (x.1,P)) (E.sort (·≤·)) from he]; apply hw.weigh; swap; · have hy:=H.genuine; exact (show 0≤(z*v)⁻¹*flowCost z from by positivity)
 have hh:L.card=D.card+E.card:=by rw [Finset.card_filter_add_card_filter_not]; -- names
 have hp':0<κ:=lt_of_lt_of_le one_pos hs; have hD:B^D.card* B^E.card=B^L.card:= by rw [←pow_add,hh]
 have hl:C'≤ B*κ:=by unfold κ; field_simp; nlinarith
 have hz: ‖modifyB G z F'‖*B^E.card ≤ J* B^L.card:=by
    have ha:= pow_le_pow_left₀ hy hl D.card; apply (mul_le_mul_of_nonneg_right ((mold_cart D o S F g z0 z1 (x.1,P) (r:=r) (fun i ti=>Hp i (mem_filter.mp ti).1)).trans ha) (pow_nonneg lB.le E.card)).trans_eq; rw [mul_pow,mul_comm (B^D.card),mul_assoc,hD]
 apply (mul_le_mul_of_nonneg_right hz (Real.exp_pos V).le).trans; change J*B^_*Real.exp V≤ Real.exp (V + v0*flakes τ x.1 +l0); have hK:=cold_spots (τ:=τ) L o S x.1 e b H.genuine (fun i w=>(Hp i w).pin) p0 E (show D⊆L from filter_subset ..) (fun i ti=> (mem_filter.mp ti).2)
 let η:= D.card* Real.log κ; have hx':η≤ v0*flakes τ x.1 := (mul_le_mul_of_nonneg_right hK (Real.log_nonneg hs)).trans_eq (by unfold v0 winterFee κ C'; ring)
 apply le_trans _ (Real.exp_le_exp_of_le (add_le_add_left (add_le_add_right hx' V) l0)); unfold J; nth_rw 1 [←Real.exp_log hp']; nth_rw 1 [←Real.exp_log lB]; rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]; unfold l0 η; exact (Real.exp_monotone (Eq.le (by ring)))
end YM.CF.Lamour.Bridge
#print axioms YM.CF.Lamour.Bridge.launch
