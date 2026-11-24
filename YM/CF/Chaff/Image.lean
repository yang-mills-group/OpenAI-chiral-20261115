import YM.CF.Chaff.Night
import YM.CF.Hype.Ace
import YM.CF.Ione.Mesh
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
variable {r Y V x μ b θ C' ρ:ℝ}
open Gloss Maize Ione Salt Hive Vow
section gen
variable {α:Type*}[DecidableEq α][Fintype α]
lemma sumH {Y:Type*}[AddCommMonoid Y](F:Scree.Hub N→Y): ∑ i:Scree.Hub N,F i=∑ S:Support (More N),∑ i:S,F ⟨(i.val,S),i.property⟩:=by
 let q(zi:Σ (S:Support (More N)), (S:Finset (Seat N))):Scree.Hub N:=⟨(zi.2.val,zi.1),zi.2.property⟩ -- tune
 let e:(Scree.Hub N)≃(Σ (S:Support (More N)), (S:Finset (Seat N))):={ toFun:=fun i=>⟨i.val.2,i.val.1,i.property⟩, invFun:=q,left_inv:=fun _=>rfl,right_inv:=fun i=>by rcases i with ⟨i,x⟩; rfl }
 rw [Finset.sum_sigma']; exact (Equiv.sum_comp e.symm F).symm -- tune
lemma drillL {I J:Type*}[Fintype I][Fintype J][LinearOrder J](F:I→ℂ): ∑ i,hollow (n:=J) (F i)=hollow (∑ i,F i):=by apply Subtype.ext; change (Dough J).val (∑ i:I,hollow (F i))= _; rw [map_sum]; exact (sum_smul ..).symm
private lemma fazo (w:Scree.Hub Λ): w.val.2= w.val.2:=rfl
end gen
variable {F:Oil (e:=e) m B}{w:Stamp m B→ℝ}
variable(t': ∀ i:Stamp m B,Inscribed K e n i H (F i) (w i))(wC:∀ i,hitE (4*b) w i ≤ C)(hf: MotionY F)
include t' A pH v l hf
variable (M:Nice n P e K C' θ)(u:1 ≤ H)(u0:0 ≤Y)(u1:0≤r)(u2:r≤1)(u3:0 ≤ V)(u4:0≤ μ)(u5:μ*mealz≤ b)(u6:Y*H⁻¹≤r*μ)(T':∀ (n:ℕ)(C:ℝ),0 ≤ C → payP P n*(composeCost P.order C (riseH P n))+C ≤ V*(Real.exp (b*n)*C))(bq:0<b)(y0:4*P.B<(Domain m B).val)(hQ:2*P.supportExponent*(Fief.tileN 3)≤ b*(P.B:ℝ))
include M u u0 u1 u2 u3 u4 u5 u6 T' bq y0 hQ wC
local notation "Ψ"=>MarkF p R F P
local notation "Yq"=> HopeN P b V r θ
lemma hubCost : IncX (fun i=> i∈ Set.range (netB m B)) (MarkF p R F P) P Y (HopeN P b V r θ*C):=by -- Prop lam T tune
 let T:=neatP (N:=Λ) P; let F':=itemsF p R F P; let w'(i:Scree.Hub Λ):= cliff (m:=m) P b (w i.val.2) θ μ r i.val.2; let v'(i:Scree.Hub Λ):= |δWeight Λ i| *w' i; have he(i:Scree.Hub Λ):PressB P (T i) (F' i) Y (v' i):= Ione.scale_E P (Burn_p p (t' _) A pH v l i.val.1 i.property M u u0 u4 u1 u2 u6 u5 y0) _
 refine ⟨(Larch.feat_v _ _ _ _ _ _ (fun i _=>he i) ?_).weight,fun s z x hx X V=>?_⟩
 · intro i; change ∑ j:Scree.Hub Λ with (T j).val.1=i,P.mass (T j).val.2 (v' j)≤ _; rw [sum_filter,sumH]; apply le_trans _ (mul_le_mul_of_nonneg_left (wC i) (hope_ng u3 u1)); unfold hitE hit0; rw [sum_filter,mul_sum]; apply sum_le_sum; intro S _; change ∑ x:S, (if x.val=i then P.mass (taleX P S) (_ * cliff (m:=m) P b (w S) θ μ r S) else 0) ≤ _
   split_ifs with hv
   · let x:S:= ⟨i,hv⟩; rw [sum_eq_single x,if_pos (show x.val=i from rfl)]; swap; · intro q _ y; rw [if_neg]; exact fun v=> y (Subtype.ext v)
     swap; · simp
     have h:x.val∈ S:=hv; let U:=w S; by_cases z:w S=0; · refine le_of_eq ?_; unfold BudgetPoint.mass; rw [z]; simp only [cliff]; unfold composeCost taxH; split<;>simp [composeCost] -- tune
     apply le_trans _ (told_S (μ:=μ) S u3 (t' S).pos bq u1 ((t' S).grove z) (T' _ _ (t' S).pos) hQ); unfold BudgetPoint.mass; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply mul_le_of_le_one_left
     · unfold cliff; have hp:=P.threshold_pos; have hf:0 ≤ w S:= (t' S).pos; refine add_nonneg (ψtax _ _ hf _) ?_; unfold rent payP riseH composeCost; positivity
     have ht: (1:ℝ) ≤ S.card:= Nat.one_le_cast.mpr (card_pos.mpr ⟨_,h⟩); change |(S.card:ℝ)⁻¹| ≤1; rw [abs_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ ht
   rw [sum_eq_zero,mul_zero]; intro x _; rw [if_neg (show x.val ≠ i from fun v=>hv (v ▸ x.property))]
 obtain ⟨i,e⟩:=z; subst s; rw [star_M p A pH v l i F hf _ t' V]; exact (Ione.tama _ x hx _).symm
omit M u u0 u1 u2 u3 u4 u5 u6 T' bq y0 hQ wC hf
include u
lemma κZ(g:1≤K): F ∅=0:=by
 have h:=t' ∅; have ht:w ∅=0:=by by_contra p; exact Finset.not_nonempty_empty (by exact Phase.populated (h.grove p))
 funext i; apply Ione.pimp_Q; intro j; have hh:= floorQ h g i j u; rw [ht,mul_zero] at hh; exact norm_le_zero_iff.mp hh
lemma φs_A {z:Briar m B e}(k:1≤K)(r:pingS P.threshold univ z.val)(W:Briar m B e→ Cipher Λ)(U:∀ i,W i=∑ j,F j i) :
 exponentL P Ψ z.val=W z - hollow (Pastry.pane (W (floorP m B p))):=by
 let M:=neatP (N:=Λ) P; let Z:=itemsF p R F P; have he(i:Scree.Hub Λ): numbE P.threshold i.val.2 (Ψ i) z.val= Ψ i z.val:= Set.indicator_of_mem (show z.val ∈ {U:Pane Λ|pingS P.threshold i.val.2 U} from grow_b (subset_univ _) r) _
 unfold exponentL; simp_rw [he]; change ∑ i:Scree.Hub Λ, (∑ j:Scree.Hub Λ with M j=i,Z j) z.val= _; simp_rw [Finset.sum_apply]; rw [sum_fiberwise_of_maps_to (g:=M) (s:=(univ:Finset (Scree.Hub Λ))) (t:=univ) _ (fun i=> Z i z.val)] -- tune
 swap; · simp
 rw [sumH,U,U (floorP ..),pane_f,← drillL,←sum_sub_distrib]; apply sum_congr rfl; intro V _; by_cases hV:V=∅ 
 · subst V; have hh:=κZ A pH v l t' u k; simp only [hh]; change ∑ x:(∅:Finset (Site ξ)),_=0-hollow (Pastry.pane 0); rw [show Pastry.pane (0:Cipher Λ)=0 from rfl,show hollow _=(0:Cipher Λ) from (by apply Subtype.ext; exact zero_smul ..),sub_zero];  simp
 have hp:0< V.card:=card_pos.mpr (nonempty_iff_ne_empty.mpr hV); simp_rw [Z,itemsF, Pi.smul_apply,δWeight]; rw [base_P p (t' V) A pH v l z.val (grow_b (subset_univ _) r) (fun _ _ _=>rfl),sum_const];  rw [card_univ,Fintype.card_coe,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
end YM.CF.Chaff
