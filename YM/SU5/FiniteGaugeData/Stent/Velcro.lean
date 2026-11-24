import YM.SU5.FiniteGaugeData.Stent.Puff
import YM.SU5.FiniteGaugeData.Strata.Rivka
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
namespace Succulent
open Strata
variable (R:Patch)
local notation "κ"=> Lattice.Order
-- exactly two route choices. BOTH have positive measure
abbrev stairW(i j:Axis):Walk := [negDir i,negDir i,negDir j,negDir j]
abbrev dogwalk:Walk:=stairW 0 1
abbrev birdwalk:Walk:= stairW 1 0
lemma Cap (o:κ):growAge o=dogwalk ∨ growAge o=birdwalk:=by
 let p(i:Axis):Bool:= decide (i=(0:Axis) ∨ i=1)
 let S(i:Axis):= straight i ((-(2•rune):Cover) i -(0:Cover) i); have he(i:Axis):¬ p i=true→ S i=[]:= fun v=>by
    unfold S; unfold straight; rcases (by simpa [p] using v : i≠0 ∧ i≠1) with ⟨u,t⟩; simp [rune,u,t]
 have h(l:List Axis):l.flatMap S=(l.filter p).flatMap S:=by induction l with | nil=>rfl| cons i l ih=> by_cases q:p i=true <;> simp [q,ih,he] -- negative `Bool`?
 let Y:= allAxes o; have hv:(Y.filter p).Perm [(0:Axis),1]:= by
    have ht:((List.finRange 4).filter p)=[0,1]:=by unfold p; decide -- p revert? let p includes none;o R ; use `rfl`?
    rw [←ht]; exact (Equiv.Perm.map_finRange_perm o).filter p -- tune
 have h₁:S 0=[negDir 0,negDir 0]:=by unfold S; decide -- relies
 have h₂:S 1=[negDir 1,negDir 1]:=by unfold S; decide -- relies
 change Y.flatMap S=_ ∨ Y.flatMap S=_; rw [h]; rcases List.perm_pair.mp hv with ht|ht; · left; simp only [ht,List.flatMap_cons,List.flatMap_nil,List.append_nil,h₁,h₂]; rfl
 right; simp only [ht,List.flatMap_cons,List.flatMap_nil,List.append_nil,h₁,h₂]; rfl
lemma dog_p : growAge 1=dogwalk:= by decide
lemma bird_p : growAge (Equiv.swap (0:Axis) 1)=birdwalk:= by decide
noncomputable def Woods : Finset Lattice.Order:= univ.filter fun i=> growAge i=dogwalk
noncomputable def massP :ℝ:= (Woods.card:ℝ)/(Fintype.card Lattice.Order:ℝ)
noncomputable def massL :ℝ:= ((Woodsᶜ:Finset Lattice.Order).card:ℝ)/(Fintype.card Lattice.Order:ℝ)
private lemma mpos :0<(Fintype.card Lattice.Order:ℝ):=by positivity
lemma leaning : 0 < massP∧ 0 < massL∧ massP+massL=1:=by
 have he:Woods.Nonempty:=⟨1,mem_filter.mpr ⟨mem_univ _,dog_p⟩⟩; have h: (Woodsᶜ:Finset Lattice.Order).Nonempty:=by refine ⟨Equiv.swap (0:Axis) 1,mem_compl.mpr ?_⟩; intro a; exact (by decide:birdwalk≠dogwalk) (bird_p.symm.trans (mem_filter.mp a).2)
 have hx:(Woods.card:ℝ)+(Woodsᶜ:Finset Lattice.Order).card=(Fintype.card Lattice.Order:ℝ):=by exact_mod_cast card_add_card_compl Woods
 refine ⟨div_pos (by exact_mod_cast card_pos.mpr he) mpos,div_pos (by exact_mod_cast card_pos.mpr h) mpos,?_⟩; unfold massP massL; rw [←add_div,hx,div_self mpos.ne']
local notation "η"=> nodeC (specialM R.L)
local notation "Q" x:max=> (matter x).val
abbrev doorG (p:Walk)(U:LinksC):= travel U (nodeC (specialM R.L)) p
abbrev SpanM(U:LinksC):= doorG R dogwalk U * (doorG R birdwalk U)⁻¹
noncomputable def Sarong (x:SU.E): Op SU.Slot:= (massP • (matter x).val) +(massL • 1)
noncomputable def CashNotch (x:SU.E):ℂ:= (Sarong x).det * star (Sarong x).det
lemma LouvreModulo (U:LinksC): Louvre R U= Sarong (SpanM R U)* (Q (doorG R birdwalk U)):=by
 let A:= doorG R dogwalk U; let B:= doorG R birdwalk U
 have hp: ∑ i:Lattice.Order,(Q (Shadow R i U))= (Woods.card:ℝ) • (Q A) + ((Woodsᶜ: Finset Lattice.Order).card:ℝ) • (Q B):=by
    rw [← Finset.sum_add_sum_compl Woods]; refine congrArg₂ (·+·) ?_ ?_; · rw [sum_congr rfl (g:=fun _=> (matter A).val) (fun i p=> (by unfold Shadow; rw [(mem_filter.mp p).2])), sum_const, Nat.cast_smul_eq_nsmul]
    rw [sum_congr rfl (g:=fun _=> (Q B)) (fun i p=>by unfold Shadow; rw [(Cap i).resolve_left (fun e=> mem_compl.mp p (mem_filter.mpr ⟨mem_univ _,e⟩))]),sum_const,Nat.cast_smul_eq_nsmul]
 have hx : (Q (SpanM R U)) * Q B=Q A:=by rw [← show ∀ u v:UNI SU.Slot,(u*v).val=u.val*v.val from fun _ _=>rfl, ←map_mul, inv_mul_cancel_right] -- right spell orientation
 unfold Louvre Sarong; rw [hp,add_mul,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,hx,one_mul]; rw [smul_add,smul_smul,smul_smul, inv_mul_eq_div,inv_mul_eq_div]; rfl -- scalar.RX
lemma officials (U:LinksC): Nylon R U= CashNotch (SpanM R U):=by unfold Nylon CashNotch; rw [LouvreModulo,Matrix.det_mul,show (matter _).val.det=1 from triple_det _,mul_one] -- ambiguous first
lemma careful : Continuous CashNotch:=by
 have he:Continuous Sarong:= (show Continuous (fun x:SU.E=>massP • (matter x).val) from matter_cont.const_smul (massP)).add continuous_const; exact he.matrix_det.mul he.matrix_det.star
private lemma combos : CashNotch 1=1:=by rw [CashNotch,Sarong,map_one,show (massP • (1:UNI SU.Slot).val+ massL • (1:Op SU.Slot))= (1:Op SU.Slot) from (add_smul ..).symm.trans (by rw [leaning.2.2,one_smul]; rfl),Matrix.det_one,star_one,mul_one]
lemma chargeSlot (i:SU.Slot): z^(SU.charge i)≠1:=fun p=>by have hx:=z_prim.dvd_of_pow_eq_one _ p; unfold SU.charge at hx; split at hx <;> norm_num at hx -- z ambiguity photons
private lemma away : ‖CashNotch SU.central‖ < 1:=by
 let H:= Sarong SU.central; let f(i:SU.Slot):ℂ:= massP • (SU.z^(SU.charge i))+ massL • 1; have h(i:SU.Slot):‖f i‖ <1:= norm_combo_lt_of_ne (by rw [norm_pow, SU.z_n, one_pow]) (by rw [norm_one]) (chargeSlot i) leaning.1 leaning.2.1 leaning.2.2
 have ht:H=Matrix.diagonal f:=by unfold H Sarong; rw [by_charge]; ext i j; by_cases e:i=j<;> simp [f,e] -- `matter` unfolds, by_charge fails
 have he:‖H.det‖<1:=by rw [ht,Matrix.det_diagonal,norm_prod]; let i: SU.Slot:= Classical.arbitrary _; rw [←Finset.mul_prod_erase _ _ (mem_univ i)]; exact (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=> (h i).le))).trans_lt (h i) -- order
 change ‖H.det*star _‖<1; rw [norm_mul,norm_star]; exact (mul_le_of_le_one_right (norm_nonneg _) he.le).trans_lt he
lemma WidePay(c:ℂ):∀ᵐ i∂SU.group.probHaar,CashNotch i ≠ c:=by
 let f(i:SU.E):= CashNotch i - c; have hx:∃ i, f i≠0:=by by_contra! p; have hp:=sub_eq_zero.mp (p 1); have ht:=sub_eq_zero.mp (p SU.central); change CashNotch 1=c at hp; rw [combos] at hp; apply away.ne; rw [ht,←hp,norm_one]
 suffices he:∀ᵐ i∂SU.group.probHaar,f i≠0 from he.mono fun i h p=> h (sub_eq_zero.mpr p)
 apply Strata.tent f (careful.sub continuous_const) _ hx; intro x W U t v; unfold f CashNotch; have h (j l: SU.Slot): AnalyticAt ℝ (fun y=> Sarong (U* Strata.fly x W y) j l) t:=by
    unfold Sarong; simp only [Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]; exact (((analyticAt_const).mul (Seal.wire x U W t j l)).add analyticAt_const)
 have he: AnalyticAt ℝ (fun y=> (Sarong (U*Strata.fly x W y)).det) t:=by
    simp_rw [Matrix.det_apply]; apply Finset.analyticAt_fun_sum; intro i e; rcases Int.units_eq_one_or i.sign with q|q <;> rw [q]; swap; · simp_rw [Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul]; apply AnalyticAt.neg; exact univ.analyticAt_fun_prod fun i' _=> h _ _
    simp_rw [Units.smul_def,Units.val_one,one_smul]; exact univ.analyticAt_fun_prod fun i' _=> h _ _
 exact (he.mul ((starL' ℝ).toContinuousLinearMap.analyticAt .. |>.comp he)).sub analyticAt_const -- star lambda eq? `.toContinuous...`
#print axioms Cap
#print axioms officials
#print axioms WidePay
end Succulent
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
