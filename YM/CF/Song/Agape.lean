import YM.CF.Moen.Stave
import YM.CF.Haro.Weight
import YM.CF.Exa.Unload
set_option quotPrecheck false
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Branch Laic
open Skye Precision
open Jet Scree
variable {n:Side}
abbrev SpaceM:Submodule ℝ (Op Slot) where
 carrier:={z|Mind z}
 add_mem':=fun {x y} (p:Mind x)(g:Mind y)=> show Mind (x+y) from ⟨fun i=>by rw [mul_add, p.firm,g.firm,add_mul],by rw [star_add,p.adj,g.adj],by rw [cc_add,p.realV,g.realV]⟩
 zero_mem':=show Mind 0 from ⟨fun i=>by simp,star_zero _,cc_zero⟩
 smul_mem':=fun i v (h:Mind v)=>show Mind (i • v) from ⟨fun j=>by rw [Matrix.mul_smul,Matrix.smul_mul, h.firm],by simp [star_smul,h.adj],by rw [cc_rsmul,h.realV]⟩
abbrev ΘS(r:ℝ):= Moen.Space.rangeB SpaceM r
abbrev riseV{r:ℝ}(x: ΘS r):Op Slot:=x.val.val
abbrev Lens (U :ℝ):Prop:=∀ (j m:ℕ)(M:Male)(W:Momentum→ Pal)(Y:Cover→Pal)(a:ℝ),1≤j→1 ≤ m→Reads Y W→RailP m Y a→AxisP W→ let Z:=zeus j M W; Mind Z∧‖Z‖ ≤ U*a∧ NullW (potion j M (fun p=>W p-waveB Z))
lemma nova:∃ C:ℝ, 0<C∧ Lens C:=excels
open Exa
-- linear recoil before L continuum.Aperture proof
variable (S:Finset (Hub n))(p : RG.BudgetPoint){r w v h:ℝ}
lemma crown_H (i:Cover)(F:Op (Single n))(b:ℝ): loft (b • F) i=b • loft F i:=by
 unfold loft; split; swap; exact (smul_zero _).symm
 unfold Haro.tapH; have hp:matPH (b • F) 0 (wrap n i)=b • matPH F 0 (wrap n i):=by -- defeq entries love index
    unfold matPH; ext; rfl
 rw [hp,smul_comm (Rush.wind (0:Site n) _),smul_comm _ b]
lemma coreF (v: Momentum)(z: ℝ)(F:Op (Single n)): heroP (z • F) v=z • heroP F v:=by unfold heroP; rw [Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [crown_H,smul_comm]
lemma pedal(C D:Pal):spaX (C+D) 0=spaX C 0+spaX D 0:=by ext i j; unfold spaX spot; change (C _ _+D _ _)+(C _ _+D _ _)=(C _ _+C _ _)+(D _ _+D _ _); abel -- tune
lemma pedal_r(C:Pal)(z:ℝ):spaX (z • C) 0=z • spaX C 0:=by ext i j; unfold spaX spot; change z • C _ _ + z • C _ _= z • (C _ _+C _ _); rw [smul_add] -- tune
variable (k:ℕ)(u:1≤k)(M: Male) -- Male open
include u
lemma θS :Continuous (fun F:Op (Single n)=> zeus k M (heroP F)):=by
 let L(F:Op (Single n))(p:ℝ):=potion k M (heroP F) (bout 0 p)
 have he(F):DifferentiableAt ℝ (L F) 0:=by
    have hp:DifferentiableAt ℝ (fun p:ℝ=> heroP F (bout 0 p)) 0:=by unfold heroP; apply DifferentiableAt.fun_sum; intro j _; unfold Laurent.mode Tap.bout; fun_prop
    let h:= (barox k u M 0).differentiableAt; exact (((differentiableAt_const 1).sub h).mul hp).mul h
 let T: Op (Single n)→ₗ[ℝ] Op Slot :=
   { toFun:=fun F=>zeus k M (heroP F)
     map_add':=fun i j=>by
       have hp:L (i+j)= L i+L j:=by
          funext x; unfold L potion; let v:=bout 0 x; rw [show heroP (i+j) (bout _ _)=heroP i v+heroP j v from ?_, mul_add,add_mul]; rfl; apply eq_add_of_sub_eq; rw [←Exa.weights,add_sub_cancel_right]
       change spaX (deriv (L _) 0) 0=spaX (deriv (L _) 0) 0+spaX (deriv (L _) 0) 0; rw [hp,deriv_add (he i) (he j),pedal]
     map_smul':=fun r F=>by
       have hp:L (r • F)= fun x:ℝ=>r • L F x:=by funext x; unfold L potion; rw [coreF,Matrix.mul_smul,Matrix.smul_mul]
       change spaX (deriv (L _) 0) 0=r • spaX (deriv (L _) 0) 0; rw [hp]; change spaX (deriv (r • L F) 0) 0=_; rw [((he F).hasDerivAt.const_smul r).deriv,pedal_r] }
 exact T.continuous_of_finiteDimensional
omit u
open Pastry
lemma orbP (x y:Cipher n):orbitPH (x+y)=orbitPH x+orbitPH y:=by ext; change Prism.portB (x.val+y.val) _ _= _; rw [Prism.portB,act_add,inner_add_right]; rfl
lemma mark_T (F G:RegBudget n):StackL (F+G) S=StackL F S+StackL G S:=by unfold StackL; simp_rw [Pi.add_apply,orbP,sum_add_distrib]
lemma seatC:Continuous (orbitPH (i:=Single n)):=by
 let T:FC (Pastry.LeanV (Single n))→ₗ[ℂ] Op (Single n):=
   { toFun:=fun f=> Matrix.of fun x y=> Prism.portB f (true,x) (false,y)
     map_add':=fun x y=>by ext; simp only [Matrix.of_apply,Prism.portB,act_add,inner_add_right]; rfl
     map_smul':=fun m x=>by ext; simp only [Matrix.of_apply,Prism.portB,act_smul,inner_smul_right]; rfl }
 exact T.continuous_of_finiteDimensional.comp continuous_subtype_val
lemma axeK(S': RegBudget n)(k:Lens v)(uS:IncX (fun _=>True) S' p w h)(s:liveB S)(pW:1≤w)(b:1 ≤ p.power)(j:ℕ)(u:1 ≤ j):let W:=heroP (StackL S' S); AxisP W ∧ Mind (zeus j M W) ∧‖zeus j M W‖≤ v*((4:ℝ)^p.power*((2:ℝ)^p.power*(16*h)/w^2)):=by
 intro W; obtain ⟨A,C,D⟩:= uS.weight; let Tx(i:Hub n):= p.mass i.val.2 (A i); have hv(i:Hub n):0 ≤ A i:=by obtain ⟨b,s,x,g⟩:= (C i).worth; apply le_trans _ g; apply sum_nonneg; intro j _; exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by linarith) _)) (s j)
 have ht(j:Hub n): A j≤ Tx j:=le_mul_of_one_le_left (hv j) (Real.one_le_exp (mul_nonneg p.exponent_pos.le (by positivity)))
 have he:(∑ i∈ S,A i)≤ Fintype.card (Site n)*(16*h):=by
    refine le_trans ((sum_le_sum fun i _=> ht i).trans (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _=> (hv i).trans (ht i)))) ?_; rw [←sum_fiberwise_of_maps_to (s:=univ) (g:=fun i:Hub n=> i.val.1) (t:=univ) (fun i _=>mem_univ _)]
    refine le_trans (sum_le_sum (fun i _=>show (∑ j: Hub n with j.val.1=i,Tx j)≤h from ?_)) ?_; swap
    · rw [sum_const,card_univ,nsmul_eq_mul]; change ((Fintype.card (Seat n)):ℝ)*h ≤_ -- rw not def?
      simp [More,Seat,site_card]; nlinarith
    rw [sum_filter]; unfold Tx; simpa only [eq_comm] using D i
 obtain ⟨hp,x,z,c⟩:= silver S' S s (Kred S' S uS) A _ _ (fun i _=>C i) (zero_lt_one.trans_le pW) he
 let x:= k j p.power M W (loft (StackL S' S)) _ u b (ladL _) z hp; exact ⟨hp,x.1,x.2.1⟩
variable (Z Q:ΘS r→ RegBudget n)(uZ:∀ i, IncX (fun _=>True) (Z i) p w h)(cZ:∀ X,Continuous fun i:ΘS r=> Z i X 1)
include cZ uZ u
lemma treeK (C:ℝ)(uC:Lens C)(s:liveB S)(hu:0 < r)(ht:1 ≤ w)(he:1 ≤ p.power) (hv:C*((4:ℝ)^p.power*((2:ℝ)^p.power*(16*h)/w^2)) ≤ r)(ℓ:∀ i:ΘS r, StackL (Q i) S= -(plankP n (riseV i))) : ∃ i:ΘS r, NullW (potion k M (heroP (StackL (Z i+Q i) S))):=by
 let V(i:ΘS r):= heroP (StackL (Z i) S); have hp(i):= axeK S p M (Z i) uC (uZ i) s ht he k u -- tune
 let f(i:ΘS r):ΘS r:= ⟨⟨zeus k M (V i),(hp i).2.1⟩,(hp i).2.2.trans hv⟩; have hx:Continuous f:=by
    refine Continuous.subtype_mk (Continuous.subtype_mk ((θS (n:=n) k u M).comp ?_) _) _; change Continuous fun i: ΘS r=> StackL (Z i) S; unfold StackL; exact continuous_finsetSum _ (fun j _=> seatC.comp (cZ j))
 obtain ⟨x,w⟩:=Moen.Space.bow hu f hx; refine ⟨x,?_⟩; rw [mark_T,ℓ,←sub_eq_add_neg]; exact Exa.crownZ _ _ _ _ u M (hp x).1 (congrArg riseV w.symm)
end YM.CF.Haro
