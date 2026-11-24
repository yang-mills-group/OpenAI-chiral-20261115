import YM.SU5.Selected.Cairn.Cloud
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint Mezz Silks
namespace Giant
open Stencil (pval pulseNode heatize)
variable (A:Giant) {N:Side} (Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T](P:Society T)(b:Bool)(i:A.Block)(f:A.Block→pulseNode)
variable {M:Tulip.Male}{δ γ C:ℝ}(e: A.Pride Z C δ γ M N) (q:A.tokenS<N.val)
local notation "L₀"=>stable A Z P b C e q
local notation "B₀"=> park N A.Broad
local notation "T₀"=> park N A.Core
local notation "Y" => cutM (Tset N)
local notation "Wₑ" => wrap (More N)
noncomputable def leftG(U:Pane N): WRect (Single N) (A.Sing P):= @HMul.hMul _ _ (Matrix (Single N) (A.Sing P) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (filmL A P b C U) (Mint.lower (f∘Prod.fst)) -- guard for defeq
noncomputable def highG(U:Pane N): WRect (Single N) (A.Sing P):= @HMul.hMul _ _ (Matrix (Single N) (A.Sing P) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (filmV A Z P C M U) (Mint.upper (f ∘Prod.fst))
local notation "η"=> A.sampleW
local notation "Hg"=> coastCap C
local notation "X"=> leftG A P b f (C:=C)
local notation "Λ" => highG A Z P f (C:=C) (M:=M) -- check f arg order
include e q
variable (U:Fields N)(g:Seat N→SU.E)
local notation "V" u:max=> gauge g u
-- support agreement U1 original, U2 repair
lemma moveL (h:Agrees B₀ U.1 U.2): let K:= P.arm (g (Wₑ (A.anchorX b))); Station.portionG ((X) (V U.2)) i * K.val= (tradew N g).val* (L₀).fLow i (f i) U:=by
 intro K; let t:=gauge g U.2; change Mint.takeO i _ * K.val = _; unfold leftG; rw [Mint.takeL]; unfold Station.fLow mixt_a; simp only [Matrix.add_mul,Matrix.mul_add,Matrix.mul_smul, Matrix.smul_mul]; rw [uptime,uptime,A.evenL P b q C U.1 U.2 (agrees_mono h (image_subset_image ((A.nudge.trans A.portS).trans A.portT)))]; rw [show K= _ from rfl]; exact congrArg₂ (·+·) (congrArg (fun t:WRect (Single N) P.Club=> (↑(pval (f i)):ℂ)^(11:ℕ) • t) (A.aweL P b U.2 i C true g)) (A.aweL P b U.2 i C false g)
lemma moveU (h:Agrees B₀ U.1 U.2): let K:=P.arm (g (Wₑ (A.anchorY))); Y* Station.portionG ((Λ) (V U.2)) i*K.val= (tradew N g).val* (L₀).fHigh i (f i) U:=by
 intro K; let t:=gauge g U.2; let H:= (Λ) t; change _ * takeO i H * K.val=_; rw [show Y * takeO i H=takeO i (Y * ((Λ) (gauge g U.2))) from Matrix.mul_assoc .. |>.symm]; unfold highG; rw [← Matrix.mul_assoc,show @HMul.hMul _ _ (Matrix (Single N) (Bool × A.Sing P) ℂ) Matrix.instHMulOfFintypeOfMulOfAddCommMonoid Y (filmV A Z P C M (gauge g U.2))=_ from snow A Z P (gauge g U.2) e,Mint.takeU]; unfold Station.fHigh mixt_b; simp only [Matrix.add_mul,Matrix.mul_add,Matrix.mul_smul,Matrix.smul_mul]; rw [downtime,downtime,A.evenR Z P e.crop q C U.1 U.2 (agrees_mono h (image_subset_image ((A.nut.trans A.portS).trans A.portT)))]; congr 1; exact congrArg₂ (·+·) (congrArg (fun t:WRect (Single N) P.Club=> (↑(pval (f i)):ℂ) • t) (A.aweR Z P U.2 i C true g)) (A.aweR Z P U.2 i C false g)
variable (c:1≤C)(d:0≤δ)(v:Brace.Sparkle N δ M 4)(wnd: Winter 4 δ N γ A.debt.val A.snowLine) (s:0< γ) (w:Clear A.rank A.debt.val (coastCap C))
include c d v wnd s w
lemma coverL (a:Guard U.2 δ)(h:Agrees (park N A.Broad) U.1 U.2) (p: Rightful (park N A.Broad) (gauge g U.2) 1 (min γ (A.bath (C:=C)))) :
 ∃ F Z,Station.Turnout (T₀) η η Hg 4 M (L₀) U f F Z:=by
 let W:= gauge g U.2; let L:= (X) W; let Q:= (Λ) W; let E:=1-spar 4 M W; let C':=(tradew N g); let g':= g⁻¹; let F:= (tradew N g'); let a':=a.cov g; have he1: F=C'⁻¹:= Silks.trade_invL g; have he:twist F E=1-spar 4 M U.2:=by rw [he1]; unfold E W; rw [v.covary U.2 g a,map_sub,map_one]; rw [show (C')⁻¹=star C' from rfl]; rw [twist_inv C']
 have ht:Payroll E L Q 1 Hg η η:=by
    let f':A.Sing P→pulseNode:= f∘ Prod.fst; have hg:= (glacier A Z P b e q c w wnd W a' s d p).office _ _ _ _ _ _ _ _ _ (Mint.vote f') (Mint.lower_pay f') (Mint.upper_pay f'); refine hg.mono _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ <;> linarith
 let X': WRect _ (A.Sing P):= F.val*L; let Z': WRect _ (A.Sing P):=F.val*Q; have hz:=Mezz.reel_g _ _ _ _ _ he ht
 refine ⟨X',Z', ?_, ?_⟩
 · constructor
   · exact sparkleT (((floraN A P b C W).grows (modes_monotone (image_subset_image (A.nudge.trans A.portS)))).times (Mint.lower (f∘Prod.fst))) (gauge_frost T₀ g')
   · exact sparkleT ((floraH A Z P C M W).times (Mint.upper (f∘Prod.fst))) (gauge_frost T₀ g')
   · apply parlance (hand true Y) _ F _ (show hand true Y * L=L from ?_); swap
     · unfold L leftG; rw [←Matrix.mul_assoc,flora_pitch A P b C W];
     change twist _ (hand true Y)= hand true Y; unfold F; rw [handAgainst,gauge_frostT]
   · exact hz.tribute
   · exact hz.cost
   · exact hz.gram
   exact hz.seat
 intro i; let D(b':Bool):= P.arm (g (Wₑ (if b' then A.anchorX b else A.anchorY))); let D' := (D true)⁻¹; let H' := (D false)⁻¹; have hd(b): ((D b)⁻¹).val.det=1:=by change ((D b).valᴴ).det=1; rw [Matrix.det_conjTranspose, show (D b).val.det=1 from P.arm_d _, star_one];
 refine ⟨D'.val,H'.val,hd true,hd false, ?_, ?_⟩
 · have hr:=undo_polo C' (D true) (Station.portionG L i) ((L₀).fLow i (f i) U) (moveL A Z P b i f e q U g h); unfold X' Station.portionG; rw [Matrix.mul_assoc,he1]; exact hr
 have hr:=undo_polo C' (D false) (Y * Station.portionG Q i) ((L₀).fHigh i (f i) U) (moveU A Z P b i f e q U g h); rw [←he1] at hr; change Y * Station.portionG (F.val*Q) i=_; unfold Station.portionG; rw [Matrix.mul_assoc,←peels_m Y _ F (gauge_frostT ..)]; exact hr
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms coverL
#print axioms moveL
#print axioms moveU
#check @glacier
