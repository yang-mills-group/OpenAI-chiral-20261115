import YM.SU5.SatinWard.Resolution.Merritt
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open Maxwell.Free
namespace PSE
open LitCurrent Surplus Next.Rank Next.Rank.Spindle
section W_era
local notation "J" => H
open LitCurrent Surplus Next.Rank.Spindle
variable {x y:Cover}{μ Q R X:ℝ}{d:Gaia}(z:Addressing x y d μ R Q){A B:ℕ}
include H
private lemma sept (K S:PlaqAxes)(Q:ℝ): ∃ C:ℝ,1 ≤ C ∧ ∀ {x y:Cover}{R X:ℝ}{d:Gaia},1≤ X → X ≤ R → 3≤ ‖d‖ → ‖d‖≤Q → ‖patchF (x-y) R-d‖ ≤ 1/X → ∀ (i j:Sage)(s:ℕ), Disp X C ((R:ℂ)^4 * W s ((x,K),i) ((y,S),j)) ((sch (G:=SU.group) i j:ℂ)*specter K S d):=by
 obtain ⟨a,b,u⟩:= sharpDisp H K S (Q+1) 0 (by norm_num); obtain ⟨k,v,p,f⟩:= housing K S (Q:=Q+1); let Z:=a+k; have hz: k ≤ Z:= le_add_of_nonneg_left (zero_le_one.trans b)
 refine ⟨Z,v.trans hz,fun {x y R X d} h e u1 u2 u3 i j s=>?_⟩
 let g:=patchF (x-y) R
 have hm: ‖g-d‖≤1:=u3.trans ((div_le_one (by linarith only [h])).2 h)
 have he:=abs_norm_sub_norm_le g d|>.trans hm; have hA:2≤ ‖g‖:=by linarith only [u1,(abs_le.mp he).1]
 have hY: ‖g‖≤ Q+1:=by linarith only [u2,(abs_le.mp he).2]
 have hr:1≤R:=h.trans e
 obtain ⟨q,t⟩:=u R hr (zero_le_one.trans hr) s (x-y) g hA hY (by simp [g]); let E':=(R:ℂ)^4*wObj (W s) K S (x-y); let σ:=specter K S
 have hu:d∈ plinth (Q+1):=(peak_iff ..).mpr ⟨by linarith only [u1],by linarith only [u2]⟩
 have ht: Disp X Z E' (σ d):=by
    refine ⟨zero_le_one.trans (v.trans hz),(p _ hu).trans hz,(norm_sub_le_norm_sub_add_norm_sub _ (σ g) _).trans (le_trans ?_ (Eq.le (show a/X+k/X= _ from by rw [←add_div])))⟩
    apply add_le_add (t.trans (div_le_div_of_nonneg_left (zero_le_one.trans b) (by positivity) e)) (((f _ ((peak_iff ..).mpr ⟨by linarith only [hA],hY⟩) _ hu).trans (mul_le_mul_of_nonneg_left u3 (zero_le_one.trans v))).trans_eq _); ring
 let K':=(sch (G:=SU.group) i j:ℂ); rw [show (W s _ _:ℂ)= K'*wObj (W s) K S (x-y) from H.pigment K S i j s x y,mul_left_comm]; exact (ht.increase K').mono (mul_le_of_le_one_left ht.nn (sch_s i j)) (zero_le_one.trans h)
omit H
private lemma endWide (o:Cover)(x:Cover)(p:x∈pavilion o B) : ‖scape (x-o)‖ ≤2*B:=by
 let W:= x-o; have h:‖shaftX W‖ ≤B:= (pi_norm_le_iff_of_nonneg (show (0:ℝ)≤ B from Nat.cast_nonneg B)).2 fun i:Axis=> by
    have h:= (pav_v ..).mp p i; change |(((x i-o i):ℤ):ℝ)|≤B; exact_mod_cast (show |x i-o i|≤ (B:ℤ) from abs_le.mpr (by omega))
 exact (Onyx.moor_z _).trans (by linarith)
abbrev gradeLight (z:Addressing x y d μ R Q) (X:ℝ)(B:ℕ):Prop:= 1 ≤ X ∧ X ≤ R ∧ 3 ≤ ‖d‖ ∧ (μ+2*B+4)*X ≤ R
abbrev loomTaxF (B:ℕ)(x:Cover)(u:Sheds B):Face ℤ:= (u.1.val.1+x,u.1.val.2)
lemma scoured (z:Addressing x y d μ R Q)(t:gradeLight z X B)(u:Sheds B)(A:PlaqAxes)(p:Fin 4): ‖patchF ((loomTaxF B x u).1-(cornerT A y p).p.1) R-d‖≤1/X:=by
 let a:= (loomTaxF B x u).1; let b:= (cornerT A y p).p.1
 have h:=z.pLease; let f(g:Cover):=scape g; let Y:=R⁻¹ • (f (a-x)-f (b-y)); have ht:patchF (a-b) R= patchF (x-y) R + Y:=by unfold Y patchF f; rw [←scape_sub,←smul_add,←scape_add]; congr 2; abel
 have he:‖Y‖ ≤(2*B+4)/R:=by
    unfold Y; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity:0≤R⁻¹)]; apply (mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (endWide (B:=B) _ _ (show a∈pavilion x B from Finset.mem_image_of_mem _ (faceOrigin u.1))) (endPaid _ _ (ends_corner ..)))) (by positivity)).trans_eq; ring
 rw [ht,add_sub_right_comm]; obtain ⟨o,p,b,g⟩:=t; apply ((norm_add_le ..).trans (add_le_add z.meters he)).trans; rw [←add_div, ←add_assoc, div_le_div_iff₀ (by linarith) (by linarith), one_mul]; exact g -- he ph notation
include H
local notation "A'"=> Sheds
lemma saturno (Q:ℝ):∃ C:ℝ,1≤C ∧∀{x y μ R B X d}(z:Addressing x y d μ R Q), gradeLight z X B →∀ (u:A' B)(A:PlaqAxes)(p:Fin 4)(j:Sage)(s:ℕ), Disp X C ((R:ℂ)^4* (W s (loomTaxF B x u,u.2) ((cornerT A y p).p,j):ℂ)) (chordF u A j d):=by
 choose b h z using fun v:PlaqAxes × PlaqAxes=> sept H v.1 v.2 Q; let C:=∑ v:PlaqAxes×PlaqAxes,b v; have hp(v): b v ≤ C:=single_le_sum (fun i _=> zero_le_one.trans (h i)) (mem_univ _); refine ⟨C,(h (lowLow,lowLow)).trans (hp _), fun {x y μ R B X d'} p1 z1 u A p j s=>?_⟩
 let e:= z (plumI u,A) z1.1 z1.2.1 z1.2.2.1 p1.sizes (scoured p1 z1 u A p) u.2 j s; exact e.mono (hp _) (zero_le_one.trans z1.1)
noncomputable abbrev seamZ (W:HorizonLens→ HorizonLens→ℝ)(x y:Cover)(i j:A' B) (n:Fin 3)(c:CupCoin)(s:Sage):ℂ:= nextSea W (loomTaxF B x i) (loomTaxF B x j) (cornerT (foilA n) y c.1).p (cornerT (foilB n) y c.2).p i.2 j.2 s s
lemma saddle (Q:ℝ):∃ C:ℝ, 0≤C ∧∀{x y μ R B X d}(z:Addressing x y d μ R Q), gradeLight z X B →∀ (u v:A' B)(n:Fin 3)(p:CupCoin)(i:Sage)(s:ℕ), Disp X C ((R:ℂ)^8*seamZ (W s) x y u v n p i) (luteP B u v n i d):=by
 obtain ⟨C,v,y⟩:= saturno H Q; refine ⟨3*C*C+3*C*C,by positivity,fun {x w μ R B X d} z h u v n p i s=>?_⟩
 let K:=fun (u:Sheds B) (F:PlaqAxes × Fin 4)=> y z h u F.1 F.2 i s
 let S:=(foilA n,p.1); let T:=(foilB n,p.2); let Wq:=K u S; unfold seamZ; let e:=((K u S).times (K v T) h.1).plus ((K u T).times (K v S) h.1)
 refine Eq.subst (motive:=fun k=>Disp X _ k (luteP B u v n i d)) ?_ e; unfold nextSea; unfold S T; push_cast; ring
omit H
noncomputable def sundown (W:HorizonLens→HorizonLens→ℝ)(x y:Cover)(i j:Sheds B):ℂ:= (∑ n:Fin 3,coeff2 1 1 n*(∑ c:CupCoin,(1/16:ℂ)*∑ l:Sage,seamZ W x y i j n c l))
noncomputable abbrev raygiven(B:ℕ)(G:Sheds B→ Sheds B→ℂ)(W:HorizonLens→ HorizonLens→ℝ)(x y:Cover):ℂ:= ∑ i:Sheds B,∑ j:Sheds B, G i j *Complex.I* sundown W x y i j
include H
lemma winLight (Q D:ℝ):∃ C:ℝ,0≤C ∧ ∀{x y μ R B X d}(z:Addressing x y d μ R Q), gradeLight z X B → ∀ (s:ℕ)(G:Sheds B→ Sheds B→ℂ), (∑ i:Sheds B,∑ j:Sheds B, ‖G i j‖)≤D → Disp X C ((R:ℂ)^8*raygiven B G (W s) x y) (concLead B G d):=by
 obtain ⟨C,b,v⟩:= saddle H Q; let o:=∑ _i:Sage,C; let w:=∑ _c:CupCoin,‖(1/16:ℂ)‖*o; let C₀:=∑ i:Fin 3,‖coeff2 1 1 i‖*w
 have hC:0≤C₀:=by unfold C₀ w o; positivity
 refine ⟨C₀*|D|,by positivity,fun {x y μ R B X d} z h s G k=>?_⟩
 let f(i j:A' B):=(R:ℂ)^8* sundown (W s) x y i j; let g(i j:A' B):=∑ n:Fin 3, coeff2 1 1 n* ∑ l:Sage,luteP B i j n l d
 have hw(i j:Sheds B): Disp X C₀ (f i j) (g i j):=by
    unfold f sundown; rw [mul_sum]; unfold g; apply Disp.SumD; intro n _; rw [mul_left_comm]; apply Disp.increase
    rw [mul_sum (a:=(R:ℂ)^8)]; let V:= ∑ l:Sage,luteP B i j n l d; rw [show ∑ l:Sage,luteP B i j n l d= ∑ _t:CupCoin,(1/16:ℂ)* V from ?_]; swap; · rw [sum_const,card_univ,nsmul_eq_mul]; unfold CupCoin; change V=(↑(Fintype.card (Fin 4×Fin 4)):ℂ)* _; rw [Fintype.card_prod]; simp -- might leaves
    apply Disp.SumD; intro c _; rw [mul_left_comm,mul_sum (a:=(R:ℂ)^8)]; exact (Disp.SumD univ fun l _=> v z h i j n c l s).increase _
 unfold raygiven; simp_rw [mul_sum,mul_left_comm ((R:ℂ)^8) (_*Complex.I)]; unfold concLead
 refine (Disp.SumD univ (fun i _=> Disp.SumD univ (fun j _=> (hw i j).increase (G i j * Complex.I)))).mono ?_ (zero_le_one.trans h.1); simp_rw [norm_mul,Complex.norm_I,mul_one, ←sum_mul]; rw [mul_comm C₀]; exact mul_le_mul_of_nonneg_right (k.trans (le_abs_self _)) hC
#print axioms winLight
end W_era
end PSE
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
