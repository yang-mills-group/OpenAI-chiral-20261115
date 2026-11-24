import YM.CF.Levier.Wicker
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
variable {p x d r:ℝ}{g v:Bool}{C:Seal (Site (More P))→Toll κ}{F: Seal (Site (More P))→ Raw (cro G e) (Iota G)}
abbrev NoteS(G:Ratio N P)(e:ℝ):Type:= Seal (Site (More P))→Raw (cro G e) (Iota G)
def coda (F:NoteS G e)(Y:Seal (Site (More P))):=perch G e k (F (toRoar G k⁻¹ Y))
variable (u:ℕ)
def OccuS(G:Ratio N P)(e:ℝ)(g v:Bool)(u:ℕ)(p d r:ℝ)(F: NoteS G e) : Prop:= ∃ C: Seal (Site (More P))→ Toll (Iota G),(∀ S,Suite (badge _) (pinH G e g) (pinH G e v) S (C S) (F S))∧incline (hall G e) u p (fun _=>r) d C -- notation todo
variable {e G u}
lemma OccuS.sum{I:Type*}(s:Finset I)(F:I→NoteS G e)(m:I→ℝ)(h:∀ i∈s, OccuS G e g v u p d (m i) (F i)) : OccuS G e g v u p d (∑ i∈s,m i) (fun S x=>∑ i∈s,F i S x):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; refine ⟨_,fun S=> Suite.free _,fun _=>?_⟩; simp [saleM]
 | @insert i s k ih=>
    obtain ⟨C,q,y⟩:=h i (mem_insert_self i s); obtain ⟨V,B,H⟩:=ih fun j w=>h j (mem_insert_of_mem w); simp only [sum_insert k]; refine ⟨_,fun S=> (q S).plus (B S),fun i=> ?_⟩; simp_rw [saleM,Pi.add_apply, mul_add,sum_add_distrib]; simp_rw [mul_add,sum_add_distrib]; exact add_le_add (y _) (H _)
lemma OccuS.pay (a:ℂ)(h:OccuS G e g v u p d r F): OccuS G e g v u p d (‖a‖*r) (fun S x=> a • F S x):=by
 obtain ⟨C,q,z⟩:= h; refine ⟨_,fun S=> (q S).accel a,fun i=>?_⟩; simp_rw [saleM, mul_left_comm _ ‖a‖]; -- tune
 simp_rw [← mul_sum,mul_left_comm _ ‖a‖]; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (z _) (norm_nonneg _)
variable (G e)
variable {I:Type*} [Fintype I](π:I→Bool→I) -- π notation
abbrev accent :Bool:= detX k.s
abbrev Meter (I:Type*) (G:Ratio N P)(e:ℝ):= I→NoteS G e
variable (T:Meter I G e)
-- left action assign old t -> target t⊕r
abbrev modeT (i:I):= coda G e k (T (π i (accent k)))
def pic := ((Fintype.card (Sweep N):ℝ)⁻¹ :ℂ)
def ced(i:I)(S:Seal (Site (More P)))(x:cro G e):= pic (N:=N) • ∑ k:Sweep N,modeT G e k π T i S x
include h
lemma fee_m(X:ℂ)(m:ℝ)(S:Op κ): toSpin G k ((m:ℂ) • S)=(m:ℂ) • toSpin G k S:=by unfold toSpin steer; rw [singT,win_c,twist_scalar]; unfold cSignX; split; rw [Complex.star_def,Complex.conj_ofReal]; rfl; rfl -- tune
lemma OccuS.palp(p':OccuS G e g v u p d r F)(hp:0≤p): OccuS G e g v u p d (population*r) (coda G e k F):=by obtain ⟨C,H,Y⟩:=p'; refine ⟨wheelS G k C,fun S=> ?_,spoke G h e k C u p d r Y (fun S=> (H S).nonn) hp⟩; let P:=pivot G h e k _ _ _ _ _ (H (toRoar G k⁻¹ S)); rw [wish_inv G h] at P; exact P
lemma mete(Q: ∀ i, OccuS G e g v u p d r (T i))(hp:0≤p)(i:I): OccuS G e g v u p d (population*r) (ced G e π T i):=by
 let L(k:Sweep N):= modeT G e k π T i; let X:(S:Sweep N)→ _:=fun k=> OccuS.palp G h e k (Q (π i (accent k))) hp; let f: ℝ:=(Fintype.card (Sweep N):ℝ)⁻¹; unfold ced; apply (show ‖pic (N:=N)‖*(∑ _ :Sweep N,population*r)=population*r from ?_) ▸ OccuS.pay (pic (N:=N)) (OccuS.sum univ L _ fun i _=> X i); simp only [pic,Complex.norm_real, norm_inv, Real.norm_natCast,sum_const,card_univ,nsmul_eq_mul]; rw [←mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=Sweep N)), one_mul] -- tune
end YM.CF.Levier
