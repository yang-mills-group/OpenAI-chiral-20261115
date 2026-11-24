/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import GaugeFieldConstruction.Rupiah
import YM.CF.Prism.Homic
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 45000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open FlightFlux Fluxim
open Labels Source Source.Drops Analysis MultiNext.SignedSource Mom Pattern
open Cube
namespace Axon
local notation "GS"=> SU.group
open AnalyticBridge VerifiedReset Next.Foundations Taxi Lenten Flot
variable {n:Side} {P: BudgetPoint}{X:Scree.Hub n}{Q:InkD n}{T:tangD n}{a c:ℝ}{p w m:ℕ}
open PhysicalNext.JointLoad Heir Lyre Banjo Analysis Siete
variable {b s r:ℝ}{k l:ℕ}
-- 4-sheet release; next budget uses estimates before late L. additional affine coeff bound used later developed separately.
def Footmark (P:BudgetPoint)(X:Scree.Hub n) (s b:ℝ)(x:tangD n):Prop:=∃ f:Fin 4 → tangD n, x=∑ i:Fin 4,f i ∧ ∀ i:Fin 4, Sized (s*b^(i.val+1)) (f i) P X.val.1 ∧ (i.val<3 → Blade (i.val+1) X (f i))
variable (p₀:PressB P X Q a c)(z:0≤a)(uX:Nonwrapping X.val.2 X.val.1)(uH:10 ≤ (More n).val)(H:VanishGE Q P X.val.1 w)(w':w ≤ 5)
local notation "Xₚ"=> X.val.2
local notation "aₚ"=> X.val.1
lemma payφ (x:tangD n)(p:0 ≤ b)(q:b≤1)(t:1≤ s)(h:Footmark P X s b x): Sized (4*s*b) x P aₚ := by
 obtain ⟨f,e,l⟩:=h; have hs:0≤ s:= zero_le_one.trans t; refine ⟨by positivity,fun j=>?_⟩
 let L:= width P aₚ j; have hv:0≤ L:= (Lyre.width_pos ..).le; rw [e,Finset.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun i=> s*b*L) (fun i _=>?_)).trans_eq ?_); · exact ((l i).1.2 j).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one p q (show 1≤ i.val+1 from Nat.le_add_left 1 i.val)).trans_eq (pow_one _)) hs) hv)
 simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]; unfold L; ring -- tune
include p₀ z uX uH H w'
lemma ghostCoin (x: Fin m→ tangD n)(W:∀ i,Footmark P X s b (x i))(p:0 ≤ b)(q:b≤1)(t:1≤ s)(l:m≤6): ‖iteratedFDeriv ℝ m (term Q) 0 x‖ ≤ (4*s)^6 * b^(w+1) * c:=by -- w shadow fix
 choose f h hh using W; let F:= iteratedFDeriv ℝ m (term Q) 0; change ‖F x‖≤ _; rw [funext h,F.map_sum]
 let C:= b^(w+1)*c -- tune w implicit
 apply le_trans (norm_sum_le ..); apply (sum_le_sum (g:=fun i => s^m * C) _).trans
 · simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow, Nat.cast_ofNat]; rw [←mul_assoc ((4:ℝ)^m),←mul_pow] -- tune pattern
   have hp: 0≤C:=by unfold C; have ht:=skim p₀ z; positivity
   rw [mul_assoc ((4*s)^6)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) l) hp
 intro i _; let y(j: Fin m):= f j (i j); let v(j:Fin m):=(i j).val+1; change ‖F y‖ ≤ _
 by_cases u:∑ j,v j ≤ w -- shadow
 · rw [show F y=0 from fossilP p₀ z uX uH H w' v _ (fun _=>by unfold v; omega) (fun i h=> (hh i _).2 (show _ from (by unfold v at h; omega))) u, norm_zero]; unfold C; have ht:=skim p₀ z; have hz:0≤ s:=zero_le_one.trans t; positivity
 have hv := seals (eraF _ _ p₀ z 1 (ping_f P _)) y (fun j=>s*b^(v j)) (l.trans P.order_ge) (fun i=>(hh i _).1)
 apply hv.trans; rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,Finset.prod_const,card_univ,Fintype.card_fin]; unfold C; rw [←mul_assoc]; have hx:0≤ s^m:=pow_nonneg (zero_le_one.trans t) _
 exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one p q (Nat.succ_le_of_lt (not_le.mp u))) hx) (skim p₀ z)
omit p₀ z uX uH H w'
def Chamber (X:Scree.Hub n)(P:BudgetPoint)(x:tangD n):Prop:=(∀ i, Mom.needed X.val.2 i→ ‖x i‖≤1∧Lyre.width P X.val.1 i≤1)∧∀ t∈ Set.Icc (0:ℝ) 1,pingS P.threshold X.val.2 (increment 1 (t • x))
lemma tile_c {x:tangD n}(p:Chamber X P x)(y:ℝ)(h:y ∈ Set.Icc (0:ℝ) 1):∀ i, Mom.needed Xₚ i→ ‖(y • x) i‖≤1∧ Lyre.width P aₚ i ≤ 1:=by
 intro i u; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg h.1]; exact ⟨mul_le_one₀ h.2 (norm_nonneg _) (p.1 i u).1,(p.1 i u).2⟩
include p₀ z uX uH H w'
abbrev xHoch(k:ℕ):ℝ:= (multip k).choose
lemma loam_money (x:tangD n)(p:0 ≤ b)(q:b≤1)(t:1≤ s)(v:Footmark P X s b x)(e:Chamber X P x)(Y: Fin m→tangD n)(f:∀ i,Footmark P X s b (Y i))(l:m≤6)(i:ℝ)(r:i∈ Set.Icc (0:ℝ) 1): ‖iteratedFDeriv ℝ m (term Q) (i • x) Y‖≤ ((7-m:ℕ):ℝ)*( xHoch 6 * (4*s)^6 * b^(w+1)*c):=by
 have ha(L:ℕ)(hL:L ≤6)(i:ℝ)(r:i∈Set.Icc (0:ℝ) 1):ContDiffAt ℝ (L:WithTop ℕ∞) (term Q) (i • x):=(stirring 1 (i • x) (fun i j h=>congrArg Pastry.pane (p₀.term i j h)) c (eraF Q X p₀ z _ (e.2 i r))).of_le (Nat.cast_le.mpr (hL.trans P.order_ge))
 have hG:0≤ c:=skim p₀ z; let xz:=b^(w+1); let A:=4*s; have hs:0≤A:= mul_nonneg (by norm_num) (zero_le_one.trans t); let U:= xHoch 6; have hu:1 ≤ U:=(multip 6).choose_spec.1; let H':= U*A^6*xz*c; have hU:0 ≤ H':=by unfold H' xz; have he:0≤ U:= zero_le_one.trans hu; positivity
 induction l using Nat.decreasingInduction generalizing i with
 | self=>
    let C:=term Q; have hp:= (multip 6).choose_spec.2 n Xₚ 1 P aₚ (i • x) (lifeH Q) (fun i j h=> congrArg Pastry.pane (p₀.term i j h)) c (eraF Q X p₀ z _ (e.2 i r)) (tile_c e i r) 6 le_rfl P.order_ge Y (fun _=>4*s*b) (fun i=>payφ _ p q t (f i)); change ‖_‖ ≤ ((7-6:ℕ):ℝ)*H'; norm_num1
    apply hp.trans; rw [prod_const,card_univ,Fintype.card_fin,mul_pow A b,←mul_assoc]; -- tune mul_pow used nested before? change
    unfold H' xz; rw [one_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one p q (Nat.succ_le_succ w')) (mul_nonneg (zero_le_one.trans hu) (pow_nonneg hs _))) hG
 | of_succ j L ih=>
    have hv(k :ℝ)(z:k∈Set.Icc (0:ℝ) 1):= Heir.along_deriv x Y k (ha _ L k z); have hf:∀ i:Fin (j+1),Footmark P X s b ((Fin.cons x Y: Fin (j+1) → tangD n) i):= Fin.cases (by simpa using v) (fun i=> by simpa using f i)
    have hK :0 ≤ ((7-(j+1):ℕ):ℝ)*H':=by positivity
    have he:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t:ℝ=> iteratedFDeriv ℝ j (term Q) (t • x) Y) (fun k u=>(hv k u).hasDerivWithinAt) (fun k u=> ih (Fin.cons x Y) hf k u) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) r
    rw [zero_smul,sub_zero, Real.norm_of_nonneg r.1] at he
    let D:= iteratedFDeriv ℝ j (term Q) 0 Y;
    have ht:‖D‖ ≤ H':= (ghostCoin p₀ z uX uH H w' Y f p q t (by omega)).trans (by unfold H'; gcongr; exact le_mul_of_one_le_left (by positivity) hu) -- tune
    apply (norm_le_norm_sub_add (iteratedFDeriv ℝ j (term Q) (i • x) Y) D).trans; apply (add_le_add (he.trans (mul_le_of_le_one_right hK r.2)) ht).trans_eq; rw [show 7-j=7-(j+1)+1 from (by omega), Nat.cast_add,Nat.cast_one,add_mul,one_mul] -- tune
-- composition in uses at any Scale sigma. 
omit p₀ z uX uH H w'
variable {E: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
structure LocalCurve (p:BudgetPoint) (V:Scree.Hub n)(F:E→ tangD n)(A:Set E)(s b:ℝ):Prop where
 smooth: ContDiffAt ℝ (6:WithTop ℕ∞) F 0
 home : Chamber V p (F 0)
 truck : Footmark p V s b (F 0)
 releases(k:ℕ) (v:k ≤6) (x:Fin k→E)(g:∀i,x i∈A) : Footmark p V s b (iteratedFDeriv ℝ k F 0 x) -- tune shadow
abbrev shapeCost (s:ℝ):ℝ:= 7*(xHoch 6*(4*s)^6)
def DevelopCost:=∑ k∈range 7, (Fintype.card (OrderedFinpartition k) : ℝ)
include p₀ z uX uH H w'
set_option maxHeartbeats 120000 in
lemma value_N (F:E→ tangD n)(E':Set E)(t:1 ≤ s)(p:0 ≤ b)(q:b≤1)(l: LocalCurve P X F E' s b): ContDiffAt ℝ (6:WithTop ℕ∞) (term Q∘F) 0 ∧ ∀ m ≤ 6,∀ (x:Fin m→E), (∀ i,x i∈ E')→ ‖iteratedFDeriv ℝ m (term Q ∘ F) 0 x‖≤ DevelopCost*shapeCost s*b^(w+1)*c:=by
 have hτ: 0≤ c:= skim p₀ z; have he:pingS P.threshold Xₚ (increment 1 (F 0)):=by simpa only [one_smul] using l.home.2 1 (by simp)
 have hb: ContDiffAt ℝ (6:WithTop ℕ∞) (term Q) (F 0):=(stirring 1 (F 0) (fun U V h=>congrArg Pastry.pane (p₀.term _ _ h)) _ (eraF _ _ p₀ z _ he)).of_le (Nat.cast_le.mpr P.order_ge) -- tune cast
 refine ⟨hb.comp 0 l.smooth,fun m k x hX=>?_⟩; let U:=xHoch 6; have hp:0 ≤ U:=zero_le_one.trans (multip 6).choose_spec.1
 rw [iteratedFDeriv_comp hb l.smooth (by exact_mod_cast k),FormalMultilinearSeries.taylorComp,_root_.sum_apply];
 apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun i=> shapeCost s *b^(w+1)*c) _).trans
 · have ht: 0≤ shapeCost s*b^(w+1)*c:=by unfold shapeCost; unfold U at hp; positivity -- tune
   rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc DevelopCost (shapeCost s) (b^(w+1)),mul_assoc DevelopCost (shapeCost s * b^(w+1)) c] -- tune grouping
   apply mul_le_mul_of_nonneg_right _ ht; unfold DevelopCost; exact single_le_sum (f:=fun i=> (↑(Fintype.card (OrderedFinpartition i)):ℝ)) (fun _ _=>by positivity) (mem_range.mpr (show m<7 from by omega))
 intro i _; let V(j:Fin i.length):= iteratedFDeriv ℝ (i.partSize j) F 0 (x∘i.emb j); have hL := loam_money p₀ z uX uH H w' (F 0) p q t l.truck l.home V (fun j=> l.releases _ ((i.partSize_le j).trans k) _ fun t=>hX _) (i.length_le.trans k) 1 (by simp);
 rw [one_smul] at hL; refine (show _ from hL.trans ?_); -- tune
 have ht: 0≤xHoch 6*(4*s)^6*b^(w+1)*c:=by change 0≤ U*(4*s)^6*b^(w+1)*c; positivity
 apply (mul_le_mul_of_nonneg_right (show ((7-i.length:ℕ):ℝ) ≤7 from (by exact_mod_cast (Nat.sub_le .. : 7-i.length ≤7))) ht).trans_eq; unfold shapeCost; ring
end Axon
end YM.CF.TableF
end
