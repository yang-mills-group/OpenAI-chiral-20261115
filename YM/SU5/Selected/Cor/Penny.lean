import YM.SU5.Selected.Cor.Fashion
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
-- The turnout on actual small fields. `r` number. No Cov star defect assumption. 
namespace Mezz
open Mint Numeric
open Stencil (pace pval pulseNode heatize)
open Caste Payroll
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
variable {N:Side} {T:Type}[Fintype T][DecidableEq T]
lemma reel_g {t d:Type*}[LinearOrder t][Fintype t][Fintype d][DecidableEq d](R:UNI t)(A B:WRect t d)(P Q:Op t)(e:twist R P=Q){a b γ δ:ℝ}(h:Payroll P A B a b γ δ) : Payroll Q (R.val*A) (R.val*B) a b γ δ := by
 refine ⟨(rent_v ..).trans_le h.tribute,(rent_v ..).trans_le h.cost,?_,?_⟩; · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,←Matrix.mul_assoc R.valᴴ, show R.valᴴ* R.val=1 from R.property.1,Matrix.one_mul]; exact h.gram
 rw [←peels_m P Q R e]; exact (rent_v ..).trans_le h.seat
lemma undo_polo {t d:Type*}[Fintype t][LinearOrder t][Fintype d][DecidableEq d](R:UNI t)(P: UNI d)(X Y: WRect t d) (h:X*P.val= R.val*Y): (R⁻¹).val*X=Y*(P⁻¹).val:=by
 let K:Op d:= (P⁻¹).val; let U:Op t:=(R⁻¹).val; have hp:P.val*K=1:=P.property.2; have hw:U*R.val=1:=R.property.1; calc
    _=U *((X*P.val)*K):=by rw [Matrix.mul_assoc,hp,Matrix.mul_one]
    _= _:= by rw [h,Matrix.mul_assoc,←Matrix.mul_assoc U,hw,Matrix.one_mul]

variable (A:Mezz)(P:Society T)(b:Bool)(i:A.Lot)(X Z:Coast→ Wq A.marks)(C:ℝ) {M:Tulip.Male}{w t:ℕ}
local notation "C₀"=> cutM (Tset N)
local notation "P₀" => park N A.Broad
local notation "B₀" => park N A.Core
local notation "q₀" => A.Tack P
local notation "η" => Tender.levyH A.D (billR C)
local notation "ψ" => Tender.tightH A.D (billR C)
local notation "R'" => billR C
local notation "a₁" => A.pole (N:=N) P
variable (c:Caste (N:=N) A M C (Tender.tightH A.D (billR C)) w X Z) (f: A.Lot→pulseNode)
local notation "T₀" => A.maturing P X Z C c
include c
abbrev ℒ (u:Pane N): WRect (Single N) (A.Tack P):= @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (accept A P true X Z C u) (Mint.lower (f ∘ Prod.fst)) -- borrowed notation
abbrev ℛ (u:Pane N): WRect (Single N) (A.Tack P):= @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (fillV A P X Z C u) (Mint.upper (f ∘ Prod.fst))
local notation "FL"=> ℒ A P X Z C f -- args $include c? def include takes effect for theorem not def
local notation "FR"=> ℛ A P X Z C f
#print ℒ
private lemma letter_left (V:Fields N) (g:Seat N→ SU.E) (h:Agrees P₀ V.1 V.2) : let r:= P.arm (g (wrap (More N) (A.grape i.1 true))); Station.portionG (FL (gauge g V.2)) i*r.val=(tradew N g).val * (T₀).fLow i (f i) V:= by -- notation parentheses
 intro r; let Q:= gauge g V.2; let D:=tradew N g; change Mint.takeO i (FL (gauge g V.2)) * r.val = _; rw [Mint.takeL]; unfold Station.fLow mixt_a; rw [Matrix.add_mul,Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Caste.accept, re_yoke,re_yoke]; -- may need unfold ℒ
 have he(b):A.pole P i true b X Z C Q*r.val= D.val* ((T₀).low i b V):=by rw [polo A P i true b X Z C c g,age_low,aura A P i true b X Z C c V.1 V.2 ?_]; exact Lattice.agrees_mono h (image_subset_image ((A.yard_core _ _ c.value).trans A.Core_subset)) -- note agrees_mono expects Set.Subset
 rw [he,he]

private lemma letter_high (V:Fields N) (g:Seat N→ SU.E)(h:Agrees P₀ V.1 V.2): let r:= P.arm (g (wrap (More N) (A.grape i.1 false))); C₀*Station.portionG (FR (gauge g V.2)) i*r.val=(tradew N g).val*(T₀).fHigh i (f i) V:=by
 intro r; let Q:= gauge g V.2; let D:=tradew N g; change C₀* Mint.takeO i (FR (gauge g V.2))* r.val= _; rw [show C₀* takeO i (FR (gauge g V.2))= takeO i (C₀ * FR (gauge g V.2)) from Matrix.mul_assoc .. |>.symm]; unfold ℛ; rw [← Matrix.mul_assoc,show @HMul.hMul _ _ (Matrix (Single N) (Bool × (A.Tack P)) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid C₀ (fillV A P X Z C (gauge g V.2))= _ from Caste.reign A P X Z C c (gauge g V.2), Mint.takeU,accept,re_yoke,re_yoke]; unfold Station.fHigh mixt_b; rw [Matrix.smul_mul,Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,Matrix.mul_add,Matrix.mul_smul];
 have he(b): A.pole P i false b X Z C Q*r.val=D.val*((T₀).high i b V):=by rw [polo A P i false b X Z C c g,age_high,aura A P i false b X Z C c V.1 V.2 ?_]; exact Lattice.agrees_mono h (image_subset_image ((A.yard_core _ _ c.value).trans A.Core_subset))
 rw [he,he]

variable (r:1 ≤ C){δ γ:ℝ}(d:0< δ) (v:Brace.Sparkle N δ M 4) (wnd:Winter 4 δ N γ t (Tender.tightH A.D (billR C))) (u:t ≤ A.W)(l:0<γ)
private lemma symbols_coat (V:Fields N) {g:Seat N→SU.E}{i:Op (Single N)} : True:= trivial -- unused
include v d r u l wnd
lemma casted (V:Fields N) (a:Guard V.2 δ)(h:Agrees P₀ V.1 V.2) (g:Seat N→SU.E) (p:Rightful P₀ (gauge g V.2) 1 (min γ (threshD A C))):
    ∃ F Z, Station.Turnout (B₀) η η (billR C) 4 M (T₀) V f F Z:=by
 let W:= gauge g V.2; let L:= FL W; let Q:= FR W; let E:=1-spar 4 M W; let C':=(tradew N g); let g':= g⁻¹; let F:= (tradew N g'); let a':=a.cov g; have he1: F=C'⁻¹:= Silks.trade_invL g; have he:twist F E=1-spar 4 M V.2:=by rw [he1]; unfold E W; rw [v.covary V.2 g a,map_sub,map_one]; rw [show (C')⁻¹=star C' from rfl]; rw [twist_inv C']
 have ht:Payroll E L Q 1 R' η η:=by
    let f':A.Tack P→pulseNode:= f∘ Prod.fst; have hp:= (visit_now A P X Z C c r wnd u d.le W a' p l).office _ _ _ _ _ _ _ _ _ (Mint.vote f') (Mint.lower_pay f') (Mint.upper_pay f'); refine hp.mono _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;> linarith -- reducibility η
 let X': WRect _ (q₀):= F.val*L; let Z': WRect _ (q₀):=F.val*Q; have hz:=reel_g _ _ _ _ _ he ht
 refine ⟨X',Z', ?_, ?_⟩ -- nesting .Turnout fields
 · constructor
   · exact sparkleT ((take_hold A P true X Z C c W).times (Mint.lower (f∘Prod.fst))) (gauge_frost B₀ g')
   · exact sparkleT ((sera A P X Z C c W).times (Mint.upper (f∘Prod.fst))) (gauge_frost B₀ g')
   · apply parlance (hand true C₀) _ F _ (show hand true C₀ * L=L from ?_); swap
     · unfold L ℒ; rw [←Matrix.mul_assoc,take_angle A P true X Z C c];
     change twist _ (hand true C₀)= hand true C₀; unfold F; rw [handAgainst,gauge_frostT]
   · exact hz.tribute
   · exact hz.cost
   · exact hz.gram
   exact hz.seat
 intro i; let D(b):= P.arm (g (wrap (More N) (A.grape i.1 b))); let D' := (D true)⁻¹; let H' := (D false)⁻¹; have hd(b): ((D b)⁻¹).val.det=1:=by change ((D b).valᴴ).det=1; rw [Matrix.det_conjTranspose, show (D b).val.det=1 from P.arm_d _, star_one];
 refine ⟨D'.val,H'.val,hd true,hd false, ?_, ?_⟩
 · have hr:=undo_polo C' (D true) (Station.portionG L i) ((T₀).fLow i (f i) V) (letter_left A P i X Z C c f V g h); unfold X' Station.portionG; rw [Matrix.mul_assoc,he1]; exact hr
 have hr:=undo_polo C' (D false) (C₀ * Station.portionG Q i) ((T₀).fHigh i (f i) V) (letter_high A P i X Z C c f V g h); rw [←he1] at hr; change C₀ * Station.portionG (F.val*Q) i=_; unfold Station.portionG; rw [Matrix.mul_assoc,←peels_m C₀ _ F (gauge_frostT ..)]; exact hr
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms casted
