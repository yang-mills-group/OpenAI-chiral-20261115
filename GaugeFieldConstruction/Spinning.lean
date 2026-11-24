import GaugeFieldConstruction.LodgerM
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix
namespace Simmer
variable {E F G:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
variable {f:E→ F} {g:F→ G}
/- p=(leading order). Van derivatives below & at p imply x^(p+1) bounds -/
lemma supplyT (f:E→F)(d:ℕ)(H:ContDiffAt ℝ (↑(d+1:ℕ)) f 0) (p:∀ k≤ d, iteratedFDeriv ℝ k f 0=0): ∃ v b:ℝ,0<v∧1≤b∧∀ i:E,‖i‖ ≤ v → ‖f i‖ ≤ b * ‖i‖^(d+1):=by
 -- induction on derivatives
 suffices W:∀ {k j:ℕ},j+k=d+1→ ∃ b v:ℝ,1≤b∧0<v∧∀ x:E,‖x‖ ≤v→ ‖iteratedFDeriv ℝ j f x‖ ≤ b*‖x‖^k by
    obtain ⟨b,v,h,z,k⟩:= W (k:=d+1) (zero_add _); refine ⟨v,b,z,h,fun i v=> ?_⟩; simpa using k i v
 intro k; induction k with
 | zero =>
    intro j h; rw [add_zero] at h; subst j
    let Z:= iteratedFDeriv ℝ (d+1) f; have hp: ContinuousAt (fun i=>‖Z i‖) 0:= (H.continuousAt_iteratedFDeriv le_rfl).norm -- tune
    let B:= 1+ ‖Z 0‖; have he:∀ᶠ i in 𝓝 (0:E),‖Z i‖≤ B:=hp.eventually (ge_mem_nhds (by unfold B; linarith)) -- ≤ name le? tune
    obtain ⟨u,v,w⟩:= Metric.mem_nhds_iff.mp (show {i:E|‖Z i‖ ≤ B} ∈ 𝓝 0 from he); refine ⟨B,u/2,le_add_of_nonneg_right (norm_nonneg _),half_pos v,fun x hx=>?_⟩; rw [pow_zero,mul_one]; apply w; rw [Metric.mem_ball,dist_zero_right]; linarith
 | succ k ih=>
    intro j h; let Z:=iteratedFDeriv ℝ j f; let X:= d+1; obtain ⟨b,v,t,l,H'⟩:= ih (j:=j+1) (by omega)
    have hd:∀ᶠ i in 𝓝 (0:E),DifferentiableAt ℝ Z i:= (H.eventually (by simp)).mono fun _ w=> w.differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (by omega : j<d+1))
    obtain ⟨r,F,W⟩:= Metric.mem_nhds_iff.mp (show {i:E| DifferentiableAt ℝ Z i}∈𝓝 0 from hd)
    refine ⟨b,min v (r/2),t,lt_min l (half_pos F),fun x U=>?_⟩; let Q:=Metric.closedBall (0:E) ‖x‖; have he(i)(g:i∈Q):‖i‖ ≤ ‖x‖:=by simpa only [Q,Metric.mem_closedBall,dist_zero_right] using g
    have hx(i)(g:i∈Q): DifferentiableAt ℝ Z i:= W (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact lt_of_le_of_lt ((he i g).trans ((le_min_iff.mp U).2)) (by linarith)))
    have hf(i)(g:i∈Q): ‖fderiv ℝ Z i‖ ≤ b* ‖x‖^k:=by unfold Z; rw [norm_fderiv_iteratedFDeriv]; apply (H' _ ((he _ g).trans ((le_min_iff.mp U).1))).trans; gcongr; exact he _ g
    have hm:‖Z x-Z 0‖ ≤ b* ‖x‖^k*‖x-0‖:= Convex.norm_image_sub_le_of_norm_fderiv_le hx hf (convex_closedBall _ _) (show (0:E)∈Q by simp [Q]) (show x∈Q by simp [Q]); rw [show Z 0=0 from p j (by omega),sub_zero,sub_zero,mul_assoc,←pow_succ] at hm; exact hm
section
variable (f:E→ F)(Υ:ContDiffAt ℝ 2 f 0)
lemma sv (x y:E):iteratedFDeriv ℝ 2 f 0 ![x,y]= fderiv ℝ (fderiv ℝ f) 0 x y:=by rw [iteratedFDeriv_two_apply]; rfl
include Υ
lemma DuoΦ (p:∀ x:E,iteratedFDeriv ℝ 2 f 0 (fun _=>x)=0) : iteratedFDeriv ℝ 2 f 0=0:=by
    let K:=fderiv ℝ (fderiv ℝ f) 0; have he(x:E):(fun _:Fin 2=> x)=![x,x]:=by funext i; fin_cases i <;>rfl
    have hm(x):K x x=0:= (sv f ..).symm.trans (he x ▸ p x) -- tune order
    have hx(u v): K u v=K v u:= Υ.isSymmSndFDerivAt (by simp) u v -- tune
    apply ContinuousMultilinearMap.ext; intro i; have hh:=hm (i 0+i 1); simp only [map_add,_root_.add_apply,hm,hx (i 1) (i 0),add_zero,zero_add] at hh; have hp: K (i 0) (i 1)=0:=by -- no nsmul conflict
       exact smul_right_injective _ (by norm_num:(2:ℝ)≠0) (by change (2:ℝ) • _=(2:ℝ) • (0:F); simp [two_smul,hh])
    rw [iteratedFDeriv_two_apply]; exact hp
end
variable {u:E→ G}{D:E→L[ℝ] F}{Z:F→L[ℝ]E}
abbrev Cook (k:ℕ)(u:E→G)(Z:F→L[ℝ]E)(i:F):G:= (Nat.factorial k:ℝ)⁻¹ • iteratedFDeriv ℝ k u 0 (fun _=>Z i)
-- Assert F zero & gradient equality.C polynomial identical jets through k with cooked plant.Ax. Equality by second B line reps.
lemma Serum_0 (n:ℕ∞ω)(p:ContDiffAt ℝ n f 0)(m: Genre):ContDiffAt ℝ n (Cook m.orderB u Z ∘ f) 0:=by
 let K:=Z∘f; have h:ContDiffAt ℝ n K 0:= Z.contDiff.contDiffAt.comp 0 p
 cases m with
 | pure=> simp only [Cook, Function.comp_def,Genre.orderB,iteratedFDeriv_zero_apply]; apply contDiffAt_const -- tune
 | mixed=>
    have hx:(Cook Genre.mixed.orderB u Z) ∘f= fun i=> (fderiv ℝ u 0) (K i):=by funext i; unfold Cook; change (Nat.factorial 1:ℝ)⁻¹ • iteratedFDeriv ℝ 1 u 0 _=_; rw [iteratedFDeriv_one_apply]; simp [K]
    rw [hx]; exact (fderiv ℝ u 0).contDiff.contDiffAt.comp 0 h
 | gauge=>
    let v:=fderiv ℝ (fderiv ℝ u) 0
    have hx:(Cook Genre.gauge.orderB u Z) ∘f= fun i=> (Nat.factorial 2:ℝ)⁻¹ • v (K i) (K i):=by funext i; change _ • iteratedFDeriv ℝ 2 u 0 _= _; rw [iteratedFDeriv_two_apply]; rfl -- tune
    rw [hx]; exact contDiffAt_const.smul ((v.contDiff.contDiffAt.comp 0 h).clm_apply h)
lemma Serum (w: Genre)(p:ContDiffAt ℝ 2 f 0)(v:f 0=0)(z: HasFDerivAt f D 0)(hu:ContDiffAt ℝ 2 u 0) (u0:∀ k<w.orderB,iteratedFDeriv ℝ k u 0=0)(h:∀ i:E,Cook w.orderB u Z (D i)= (Nat.factorial w.orderB:ℝ)⁻¹ • iteratedFDeriv ℝ w.orderB u 0 (fun _=>i)) : ∀ k≤ w.orderB, iteratedFDeriv ℝ k (u-Cook w.orderB u Z ∘ f) 0=0:=by
 let V:=u-Cook w.orderB u Z ∘ f; let Y:= Cook w.orderB u Z ∘ f
 let A:=Z ∘ f; let e(i):=Z (D i); have hA:HasFDerivAt A (Z ∘L D) 0:= Z.hasFDerivAt.comp 0 z; have hv:A 0=0:=by unfold A; rw [comp_apply,v,map_zero]
 have hx: ContDiffAt ℝ ((2:ℕ):ℕ∞ω) A 0:= Z.contDiff.contDiffAt.comp 0 p
 have hZ:ContDiffAt ℝ ((2:ℕ):ℕ∞ω) Y 0:=Serum_0 _ p _; intro k he;
 cases w -- recompute dependent Y etc.
 · rw [Nat.eq_zero_of_le_zero (show k ≤ 0 from he)]; apply ContinuousMultilinearMap.ext; intro i; rw [iteratedFDeriv_zero_apply]; simp [Function.comp_apply,Cook, Genre.orderB]
 · let X:= fderiv ℝ u 0; have hp: Y=X ∘ A := funext fun i=> by unfold Y Cook; change (Nat.factorial 1:ℝ)⁻¹ • iteratedFDeriv ℝ 1 u 0 _ = _; rw [iteratedFDeriv_one_apply]; unfold X A; simp
   have hY:DifferentiableAt ℝ Y 0:=hZ.differentiableAt (by norm_num)
   have H(i):X (e i)= X i:=by
      have he:= h i; unfold Cook at he; change (Nat.factorial 1:ℝ)⁻¹ • iteratedFDeriv ℝ 1 u 0 (fun _=> e i)= (Nat.factorial 1:ℝ)⁻¹ • iteratedFDeriv ℝ 1 u 0 (fun _=> i) at he; simpa [iteratedFDeriv_one_apply,X] using he -- tune
   change k≤ 1 at he; change iteratedFDeriv ℝ k (u-Y) _=_; interval_cases k
   · apply ContinuousMultilinearMap.ext; intro i; have hf: u 0=0:=by rw [←(show iteratedFDeriv ℝ 0 u 0 i=u 0 from iteratedFDeriv_zero_apply ..),u0 0 (by decide)]; rfl -- tune unspecified empty
     rw [iteratedFDeriv_zero_apply,Pi.sub_apply,hf,hp,comp_apply,hv,map_zero,sub_zero]; rfl
   rw [iteratedFDeriv_sub_apply (hu.of_le (by norm_num)) (hZ.of_le (by norm_num))]; apply sub_eq_zero.mpr; apply ContinuousMultilinearMap.ext; intro i; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,hp,(X.hasFDerivAt.comp 0 hA).fderiv]; exact (H (i 0)).symm
 -- 2 prove through. 
 let K:= fderiv ℝ (fderiv ℝ u) 0; let g:ℝ:=(Nat.factorial 2:ℝ)⁻¹; have hp:Y= g • fun i=> K (A i) (A i):=by funext i; unfold Y Cook; change g • iteratedFDeriv ℝ 2 u 0 _= g•_; rw [iteratedFDeriv_two_apply]; rfl
 change k≤ 2 at he; change iteratedFDeriv ℝ k (u-Y) _ = _; interval_cases k
 · rw [iteratedFDeriv_sub_apply (hu.of_le (by norm_num)) (hZ.of_le (by norm_num)),u0 0 (by decide)]; have hf: iteratedFDeriv ℝ 0 Y 0=0:=by apply ContinuousMultilinearMap.ext; intro i; rw [iteratedFDeriv_zero_apply,hp,Pi.smul_apply]; change g • K (A 0) (A 0) = 0; rw [hv,map_zero,smul_zero]
   rw [hf,sub_zero]
 · rw [iteratedFDeriv_sub_apply (hu.of_le (by norm_num)) (hZ.of_le (by norm_num)),u0 1 (by decide)]; have hf: fderiv ℝ Y 0=0:=by
      rw [hp]; let ht:= (K.hasFDerivAt.comp 0 hA).clm_apply hA; rw [show fderiv ℝ (g • fun i=> K (A i) (A i)) 0=_ from (ht.const_smul g).fderiv]; -- tune
      ext i; simp [comp_apply,hv]
   rw [show iteratedFDeriv ℝ 1 Y 0=0 from (by ext i; rw [iteratedFDeriv_one_apply,hf]; rfl),sub_zero]
 let V:=u-Y; refine DuoΦ _ (hu.sub hZ) (fun i:E=>?_); let ξ:=![i,i]; rw [show (fun _:Fin 2=>i)=ξ from (by ext1 i; fin_cases i<;>rfl),iteratedFDeriv_sub_apply (hu.of_le (by norm_num)) (hZ.of_le (by norm_num)),ContinuousMultilinearMap.sub_apply]; apply sub_eq_zero.mpr
 let q:= K (e i) (e i); have ht: K i i=q:=by
    have he:= h i; apply smul_right_injective _ (show g≠0 from inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne')); change g • K i i = g • K _ _; unfold Cook at he; change g • iteratedFDeriv ℝ 2 u 0 (fun _=> _) = g • iteratedFDeriv ℝ 2 u 0 _ at he; rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply] at he; exact he.symm
 have he: iteratedFDeriv ℝ 2 Y 0 ξ=g • (q+q):=by
    rw [hp,iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ ((2:ℕ):ℕ∞ω) (fun i:E=> K (A i) (A i)) (0:E) from (K.contDiff.contDiffAt.comp 0 hx).clm_apply hx),ContinuousMultilinearMap.smul_apply,HushP.hessian_B A A i i 0 K hx hx hv hv,hA.fderiv]; try rfl
 rw [he, sv]; change _; exact ht.trans (by unfold g q; norm_num [Nat.factorial]; module) -- tune type
end Simmer
end ArtCart
end MastTin
end YM.CF.XGarden
end
