import GaugeFieldConstruction.SocorroQ
import GaugeFieldConstruction.WhelmQ
import GaugeFieldConstruction.WallabyQ
import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.BootHearthJ
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4200
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace WallsQ
variable {w:ℕ}{K:Calibration}{o:Cover}{m d:Side}
-- maximum over ANY value satisfying scored definition (not requiring color constants initial locations), empty profit 0. List enumeration.X
local instance (d:Side):NeZero (2*d.val):= ⟨(mul_pos (by decide) d.property).ne'⟩
local notation "DK"=> dialQ d
variable {C:Type} [Fintype C][Nonempty C]{L:Loom (K.c m)}{E:Mark (K.c m)→ℂ}{Price:ℝ}
variable (D:Metered K m L E Price)
variable {col:C → Cover}{mtr:C→Family K}{S:C→Finset Cover}{A:C→ℝ}{u:C→ℝ}
variable (p₀: ∀ i,0 ≤ A i) (hu:∀ i, 0 < u i)
variable (e:∀ i:C, InTest K true (S i) false (mtr i)) (c:∀ i:C, pay (mtr i) (A i)) (h:∀ i,PipeQ K w o (col i) (S i))
variable {x:dialQ d→C}{M:dialQ d→Family K}
variable {Ω:List (dialQ d)}(l:useinQ Ω)
def TwistΦQ (Ω:List (dialQ d)) (E:Mark (K.c m)→ℂ)(u:C→ℝ)(w:ℕ)(o:Cover)(col:C → Cover)(mtr:C→Family K)(x:dialQ d→C) : Set ℝ := {r| r=0 ∨∃ M:dialQ d→Family K,tentPegQ w o K col mtr d x M ∧ r=listFeeQ Ω E u x M}
def MintΦQ (Ω:List (dialQ d)) (E:Mark (K.c m)→ℂ)(u:C→ℝ)(w:ℕ)(o:Cover)(col:C → Cover)(mtr:C→Family K)(x:dialQ d→C):ℝ:= sSup (TwistΦQ Ω E u w o col mtr x)
local notation "θx"=> TwistΦQ Ω E u w o col mtr
local notation "Θx"=> MintΦQ Ω E u w o col mtr
local notation "Fv"=> listFeeQ Ω E u
local notation "Hi" t:max=> E ((t:Family K) m)
include D hu e h c
lemma QuartzPayQ (p:tentPegQ w o K col mtr d x M)(L:List (dialQ d)): TestFamily K true (L.map M).prod ∧ pay (L.map M).prod (L.map (A∘x)).prod:=by
 induction L with
 | nil=>exact ⟨aux_test (S:=∅) InTest.one,pay_unit⟩
 | cons i l ih=>
    obtain ⟨_,_,t⟩:=p i; obtain ⟨_,q,_⟩:= t.lives (e _) (h _)
    exact ⟨(aux_test q).mul ih.1,pay_mul (t.cash (c _)) ih.2⟩
lemma mint_h (x:dialQ d→ C): BddAbove (TwistΦQ Ω E u w o col mtr x):=by
 let β:= Real.exp (Price*(m.val:ℝ)^4)*(Ω.map (A ∘x)).prod
 let f:=(Ω.map (u ∘x)).prod; refine ⟨max 0 (β/f),?_⟩; rintro a (rfl | ⟨M,t,rfl⟩); exact le_max_left ..
 obtain ⟨hz,v⟩:= QuartzPayQ D hu e c h t Ω -- tune
 exact le_max_of_le_right (div_le_div_of_nonneg_right (bill D hz _ v) (List.prod_nonneg (by intro i g; obtain ⟨k,v,rfl⟩:=List.mem_map.mp g; exact (hu _).le)))
lemma mint_nn (x:dialQ d→ C): 0 ≤ MintΦQ Ω E u w o col mtr x:= le_csSup (mint_h D hu e c h x) (Or.inl rfl)
lemma mint_b (p:tentPegQ w o K col mtr d x M): listFeeQ Ω E u x M ≤ MintΦQ Ω E u w o col mtr x:= le_csSup (mint_h D hu e c h x) (Or.inr ⟨M,p,rfl⟩)
variable (z:CatellaQ K w o d (K.c m))
include z l
lemma crestQ (x:dialQ d→ C)(j:Axis)(v:ℤ):(MintΦQ Ω E u w o col mtr x)^2≤MintΦQ Ω E u w o col mtr (reflectQ d j v x)*MintΦQ Ω E u w o col mtr (reflectQ d j (v+d.val) x):=by
 let t:=reflectQ d j v x; let r:= reflectQ d j (v+d.val) x; let U:= (Θx) t*(Θx) r; have HT(L:dialQ d→C):0≤ (Θx) L:=mint_nn D hu e c h _
 have hg: 0 ≤ U:=mul_nonneg (HT _) (HT _); rw [show (Θx) (reflectQ d j v x)*_ = Real.sqrt U^2 from (Real.sq_sqrt hg).symm]; refine pow_le_pow_left₀ (HT _) (csSup_le ⟨0,Or.inl rfl⟩ (fun a k=>?_)) _
 rcases k with rfl|⟨M,p,rfl⟩; exact Real.sqrt_nonneg _
 have ha: ∃ s j':ℤ,(s=v∨s=v+d.val) ∧ planeQ w o j s=Heat.gaugeShift K.B j':=by
    rcases z.2.2 j v with ⟨y,g⟩|⟨y,g⟩; exact ⟨_,_,Or.inl rfl,g⟩; exact ⟨_,_,Or.inr rfl,g⟩
 obtain ⟨s,y,pt,g⟩:=ha; obtain ⟨U',V,X,Y,χ⟩:= pennyQ D hu e h p l z j v _ rfl s y pt g
 apply (pow_le_pow_iff_left₀ (by unfold listFeeQ; exact div_nonneg (norm_nonneg _) (List.prod_nonneg (by intro i b; obtain ⟨k,t,rfl⟩:=List.mem_map.mp b; exact (hu _).le))) (Real.sqrt_nonneg U) (n:=2) (by decide)).mp
 rw [Real.sq_sqrt hg]
 exact χ.trans (mul_le_mul (mint_b D hu e c h X) (mint_b D hu e c h Y) (by unfold listFeeQ; apply div_nonneg (norm_nonneg _); exact List.prod_nonneg (by intro i b; obtain ⟨k,t,rfl⟩:=List.mem_map.mp b; exact (hu _).le)) (HT _))
-- Ov value envelope 1
lemma tasselQ (H:∀ i:C,∀ V:dialQ d→Family K,(∀ t,TwigQ K w o (col i) (mtr i) d t (V t)) → ‖E ((Ω.map V).prod m)‖ ≤ (u i)^Ω.length) (p:tentPegQ w o K col mtr d x M): ‖E ((Ω.map M).prod m)‖ ≤(Ω.map (u∘x)).prod:=by
 have rope(X:dialQ d→ C):0< (Ω.map (u∘X)).prod:= List.prod_pos (by intro i b; obtain ⟨k,t,rfl⟩:=List.mem_map.mp b; exact hu _)
 apply (div_le_one (rope x)).mp; change (Fv) x M≤ 1
 obtain ⟨j,hj,pj⟩:=Finset.exists_max_image (univ) (Θx) ⟨x,mem_univ x⟩
 refine (mint_b D hu e c h p).trans ((pj _ (mem_univ _)).trans ?_)
 by_contra! t'; let Z:=fun x:dialQ d→C=> (Θx) j=(Θx) x
 have ht:Melon d Z:=by
    constructor; intro α hα b u; let V:= reflectQ d b u α; let Y':=reflectQ d b (u+d.val) α; let f:=(Θx) j
    have hk:= crestQ D hu e c h l z α b u; change (Θx) α^2 ≤ (Θx) V*(Θx) Y' at hk; rw[← show _=_ from hα] at hk
    apply le_antisymm _ (pj _ (mem_univ _)); by_contra! v'
    have h0:0 ≤ (Θx) V:= mint_nn D hu e c h _
    have he: (Θx) V*(Θx) Y' < f*f:= lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pj _ (mem_univ _)) h0) (mul_lt_mul_of_pos_right v' (by linarith))
    rw[sq] at hk; exact he.not_ge hk
 obtain ⟨i',v⟩:=sheetQ ht j rfl; let z:dialQ d→C:= fun _=>i'; apply t'.not_ge; rw[show _ =(Θx) z from v]; refine csSup_le ⟨0,Or.inl rfl⟩ ?_; rintro a (rfl|⟨M,t,rfl⟩); norm_num
 have H':Ω.map (u∘ z)= Ω.map (fun _=> u i'):=rfl
 have hp:(Ω.map (u∘ z)).prod=(u i')^Ω.length:=by rw [H']; simp -- tune
 apply (div_le_one (rope z)).mpr; rw[hp]; exact H _ _ t
#print axioms tasselQ
#check List.prod_nonneg
end WallsQ
end YM.CF.Buffered.Afterglow.Tower.SlabMark
end
