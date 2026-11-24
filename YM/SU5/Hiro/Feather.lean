import YM.SU5.Lamour.Poise
import YM.SU5.Lamour.Matinee

/-! # Flex mark budget. Adapts Crystal,Matinee,Poise,Updraft,Savory. Keep HERE real ℓ² Wick global error by taking uniform access estimates on CURVED arguments too. Does not require pointwise-CAR proximity or even control of derivative of color factor. This frees perturbative curvature probes which change on arbitrarily small gauge scales on which not enough curvature aperture dilation is left. `ε` parameter basis same for convenience.
-/

/-! # Crystalline Moth. neighborhood & geometry.
 For caller wanting only first orientation, condition even both links near; from flag-free solve for both.
-/
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
variable {N: Side}{j d r n k a w:ℕ}{ε ξ δ z l v θ γ ζ μ τ ν C B:ℝ}{M:Tulip.Male}{U: Loom N}
structure Flex (j d r:ℕ)(ε ζ C B:ℝ)(N:Side)(M:Male)(F:Mark N)(o:Seat N)(S:Finset (Seat N)):Prop where
 color: covariant F
 range: AtSupport false S F
 units: ∀ X:Fields N,‖F X‖≤ C
 pin : o ∈ S
 border : S⊆BlockP r o
 issued : (modesIn N S).card≤ d
 reads: ∀ X:Fields N, Rightful S X.1 1 ζ→Rightful S X.2 1 ζ→ ∃ x,Sea (spar j M (1:Pane N)) x∧ ‖alleyR (mateK N) x (F X)‖≤ B/4
variable {o:Seat N}{S:Finset (Seat N)}{F:Mark N}{P V:Pane N}{s t u:ℕ}
local notation "Ⲙ" => Lattice.halo
variable (H:Optic j n k d v ε θ l C B)(q:Procurement j a δ)(W:Warrant r s γ ζ τ)(roof: Roof N μ δ t U)
-- from DIRTY split all clean
include H q W roof
lemma feather (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(L:Flex j d r ε ζ C B N M F o S)(g:Disjoint (BlockP (((r+s)+1)+t) o) (flags τ x.1)):
 let D:= modesIn N S; let P:=U x; let A:=here N j z M P; let V:= slant (cutM (Tset N)) A z
 (Bun (ray V (Tset N)) D D l)∧(∀ X:Finset (Seat N),Distant (k+1) X S→Bun (ray V (Tset N)) (modesIn N X) D v)∧
 (∀ i∈ D, ‖acts (wish (tickA N) A z (shadeK (Tset N) i)) (basisKet i)‖ ≤ v) ∧ (∀ X: Wave (Single N), Sea A X → ‖F (x.1,P)‖*(4*v)*(4*l)^d + ‖boomR X (cutM_idp (Tset N)) z0 (F (x.1,P))‖≤ B):= by
 let R:=r+s; let Y:= R+1; let ω:=stampG o x.1; let Λ:=BlockP R o; let A':=Lattice.gauge ω (U x); let P':=Lattice.gauge ω x.1; let G:= flags τ x.1; have he: S ⊆ Λ:= subset_trans L.border (Corona.halo_mono (Nat.le_add_right ..) subset_rfl)
 have hy: Agrees Λ (U x) x.1:=fledged roof Λ x hx (Disjoint.mono_left (by apply subset_trans (fit (subset_refl Λ)); exact Corona.halo_mono (Nat.add_le_add_right (Nat.le_add_right R 1) t) subset_rfl) g)
 have hr:Agrees Λ A' P':= tied _ _ _ _ _ hy (fun _ _=> rfl) -- EqOn
 have hc: Rightful Λ P' 1 (min γ ζ):= W ht (Disjoint.mono_left (Corona.halo_mono (Nat.le_add_right Y t) subset_rfl) g)
 have hh:= rect hc hr; intro D P A V; have hg: Guard P δ:= roof.paid x; have hW:Guard A' δ:= hg.cov ω
 have hp:= purchase q z0 z1 H₁ p c a' hW (loft_rightful (P:=A') hh (min_le_left ..) (show (Ⲙ s S)⊆Λ from fit L.border)) M;
 have hv:= q.audit (M:=M) p; obtain ⟨n0,hT,m_⟩:= Optic.reach H H₁ h S hv hg z0 z1 ω hp; have hV:V=sill N j M z P:=by unfold V; rw [←touchP]; rfl
 rw [hV]
 refine ⟨n0,hT,m_,fun X p=>?_⟩
 let F':= F (x.1,P)
 let γ:=tradew N ω
 let f0:Fields N:=(x.1,P); let x1:=simultaneous ω f0
 let Z':= acts (quantU γ).val X
 have hZ:Sea (here N j z M A') Z':=by unfold A' here; rw [account_cov hv hg ω z0 z1]; exact lifted γ p
 have hgX: F x1=twist (quantU γ) (F f0):= L.color ω f0
 have hv1: Rightful S x1.1 1 ζ:=loft_rightful hc (min_le_right ..) he; have hv2: Rightful S x1.2 1 ζ:= loft_rightful hh (min_le_right ..) he
 have hρ:=H.port S (F x1) (F x1) (L.units x1) (by rw [sub_self,norm_zero]; exact H.zephyr.le) L.issued (L.range.allV x1) (L.range.allV x1) H₁ hv hW z0 z1 hp (L.reads x1 hv1 hv2) Z' hZ
 rw [hgX, twist_norm] at hρ; rw [show boomR Z' (cutM_idp (Tset N)) z0 (twist (quantU γ) (F f0)) = boomR X (cutM_idp (Tset N)) z0 (F f0) from held (cutM_idp _) (gauge_frostT ω) z0 X (F f0)] at hρ; exact hρ
variable {I:Type*}[Fintype I][LinearOrder I]
include H q W roof
lemma comrade (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(o:I→Seat N)(S:I→Finset (Seat N))(F:I→Mark N)(i:Finset I)(H0:∀ j'∈ i, Flex j d r ε ζ C B N M (F j') (o j') (S j'))(p0:∀ x∈i,∀ y∈i,x≠y →Distant (k+1) (S x) (S y))(g: ∀ j ∈i,Disjoint (BlockP (((r+s)+1)+t) (o j)) (flags τ x.1))(y:Wave (Single N))(f:Sea (spar j M (U x)) y)(Z:FC (Single N)):
 let P:= U x; let A:= spar j M P; let G:=tickA N;
 Yep ((z*v)⁻¹*flowCost z) (acts (star (Z*fo (fun i=>F i (x.1,P)) (i.sort (· ≤ ·)))) (mateK N)) y (‖modifyB G z Z‖*(B^i.card)*Real.exp (trade A G z)):=by
 intro P A G; let V:= here N j z M P; let S':= fun i'=> modesIn N (S i'); let ℓ(v)(x:v∈ i):= (H0 v x).range; have hg:=fun j hj=> feather H q W roof H₁ h p z0 z1 c a' x hx ht (H0 j hj) (g j hj)
 unfold G; rw [touchP, ←prod_const B (s:=i)]; let Y':= cutM (Tset N); have he : IsStarProjection A:=(q.audit p).projection _ (roof.paid x);  -- tune
 have hp:V=draft A Y' z:=by unfold V here; rw [touchP]
 refine Trees S' _ i he f.2 f z0 z1 (tick_cut N) _ Z rfl H.genuine H.low (wind_flight S i p0) H.lip d (fun j w=> (H0 j w).issued) (fun j w=> (H0 j w).range.allV _) ?_ ?_ ?_ (fun _=>B) ?_ -- d shadow fix
 · intro j w; let X:= Z; rw [←hp]; intro y v; let ht:= (hg j w).2.1 _ (flown S i p0 j w) y v; exact ht.trans' (sum_le_sum_of_subset_of_nonneg (flown_modes S _) (fun _ _ _=> by positivity))
 · intro j w; rw [←hp]; exact (hg j w).1
 · intro j w; let hc:= (hg j w).2.2.1; rw [←hp, ←touchP]; exact hc
 intro j w; rw [←hp]; exact (hg j w).2.2.2
variable (L: Finset I)(o:I→ Seat N)(S:I→Finset (Seat N))(F:I→Mark N)
omit H q W roof
lemma flexCart (h:0≤ C)(p:0<z)(q:z≤1)(x:Fields N)(H:∀ i∈L,Flex j d r ε ζ C B N M (F i) (o i) (S i)): ‖modifyB (tickA _) z (cartMark L F x)‖≤ (C*(2*(flowCost z+1))^d)^L.card:=by
 let A:= moldP (Kea.cut_t N) p; have hp:=flow_pos p
 induction L using Finset.induction_on_min with
 | empty=> change ‖A _‖≤ _; simp [cartMark,Pannier.Chancel.fo]
 | insert i T e ih=>
    change ‖A _‖≤ _; rw [cartMark_ins T F i e, Pi.mul_apply,map_mul,card_insert_of_notMem (Flies.out e),pow_succ']; apply (norm_mul_le ..).trans; have ht:= H i (mem_insert_self ..); have he:‖A (F i x)‖≤ C*(2*(flowCost z+1))^d:=by apply (mold_bill (P:=tickA N) (Kea.cut_t N) p q (ht.range.allV x)).trans; gcongr; exact ht.units x; linarith; exact ht.issued -- tune order
    exact mul_le_mul he (ih (fun i u=> H i (mem_insert_of_mem u))) (norm_nonneg _) (by positivity)
include H q W roof
theorem lance (H₁:Kea.Pad j N)(h:n≤N.val)(p:a≤N.val)(z0:0<z)(z1:z≤1)(c: ClothQ a j δ z ε γ s)(a':Closen j z ε)(x:Orbit N)(hx: τ≤μ)(ht:2*((r+s)+1)<(More N).val)(g:0≤C)(lB:0<B)(Hp:∀ j'∈ L, Flex j d r ε ζ C B N M (F j') (o j') (S j'))(p0:∀ x∈L,∀ y∈L,x≠y →Distant (k+1) (S x) (S y))(y:Wave (Single N))(f:Sea (spar j M (U x)) y):
 let P:= U x; let A:= spar j M P; let G:=tickA N;
 Yep ((z*v)⁻¹*flowCost z) (acts (star (cartMark L F (x.1,P))) (mateK N)) y (Real.exp (trade A G z+ winterFee d (((r+s)+1)+t) B C z * flakes τ x.1 + L.card*Real.log B)) :=by
 classical
 intro P A G; let e:=r+s+1+t; let b:= flags τ x.1; let Y:= frostFilter b o e; let D:=L.filter Y; let E:= L.filter fun z=> ¬ Y z; let F':= cartMark D F (x.1,P); have he:=parcel_trick L S F M (x.1,P) Y (fun i v=>(Hp i v).range)
 let hm(x)(d:x∈E):= (mem_filter.mp d).1; have ha(i)(v:i∈ E): Disjoint (BlockP e (o i)) b:= by
    apply disjoint_left.mpr; intro x h l; exact (mem_filter.mp v).2 (halo_spec.mpr ⟨_,l,(separation_comm ..).trans_le (blocks_test.mp h)⟩)
 have hw:= comrade H q W roof H₁ h p z0 z1 c a' x hx ht o S F E (fun i h=> Hp i (hm i h)) (fun i hi j hj=> p0 _ (hm i hi) _ (hm j hj)) ha y f F';
 let V:= trade A G z; have hv:=flow_pos z0; let C':=C*(2*(flowCost z+1))^d; let κ:= 1+C'/B; have hy:0≤C':=by unfold C'; positivity
 have hs:1≤κ:=le_add_of_nonneg_right (by positivity); let J:=κ^D.card; let v0:=winterFee d e B C z; let l0:=L.card*Real.log B
 rw [show cartMark L F (x.1,P)=F' * fo (fun i=>F i (x.1,P)) (E.sort (·≤·)) from he]; apply hw.weigh; swap; · have hy:=H.genuine; exact (show 0≤(z*v)⁻¹*flowCost z from by positivity)
 have hh:L.card=D.card+E.card:=by rw [Finset.card_filter_add_card_filter_not]; -- names
 have hp':0<κ:=lt_of_lt_of_le one_pos hs; have hD:B^D.card* B^E.card=B^L.card:= by rw [←pow_add,hh]
 have hl:C'≤ B*κ:=by unfold κ; field_simp; nlinarith
 have hz: ‖modifyB G z F'‖*B^E.card ≤ J* B^L.card:=by
    have ha:= pow_le_pow_left₀ hy hl D.card; apply (mul_le_mul_of_nonneg_right ((flexCart D o S F g z0 z1 (x.1,P) (r:=r) (fun i ti=>Hp i (mem_filter.mp ti).1)).trans ha) (pow_nonneg lB.le E.card)).trans_eq; rw [mul_pow,mul_comm (B^D.card),mul_assoc,hD]
 apply (mul_le_mul_of_nonneg_right hz (Real.exp_pos V).le).trans; change J*B^_*Real.exp V≤ Real.exp (V + v0*flakes τ x.1 +l0); have hK:=cold_spots (τ:=τ) L o S x.1 e b H.genuine (fun i w=>(Hp i w).pin) p0 E (show D⊆L from filter_subset ..) (fun i ti=> (mem_filter.mp ti).2)
 let η:= D.card* Real.log κ; have hx':η≤ v0*flakes τ x.1 := (mul_le_mul_of_nonneg_right hK (Real.log_nonneg hs)).trans_eq (by unfold v0 winterFee κ C'; ring)
 apply le_trans _ (Real.exp_le_exp_of_le (add_le_add_left (add_le_add_right hx' V) l0)); unfold J; nth_rw 1 [←Real.exp_log hp']; nth_rw 1 [←Real.exp_log lB]; rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add,←Real.exp_add]; unfold l0 η; exact (Real.exp_monotone (Eq.le (by ring)))
end YM.CF.Lamour.Bridge
#print axioms YM.CF.Lamour.Bridge.lance
