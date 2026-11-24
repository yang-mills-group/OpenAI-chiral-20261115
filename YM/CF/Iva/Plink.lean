import YM.CF.Iva.Spin
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Iva
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
variable {E: Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{x:E} {k:ℕ}
variable{n:Type*}[LinearOrder n][Fintype n]
local notation "Z₀"=> LeanV n
open Rue Font
variable{u v:ℂ}
-- payments.Anal duo
variable (f g:E→↥(Dough n))(F F' G H: E → ↥(Dough n))(c d:ℝ)
abbrev PearL(n:Type*)[LinearOrder n][Fintype n](x:ℝ):=Pastry.hollow (n:=n) (Complex.exp (x:ℂ))
local notation "Q"=> PearL n c
local notation "U"=> PearL n d
abbrev dial (n:Type*)[Fintype n][LinearOrder n](k:ℕ) := naked (n:=n) (steel k (Real.exp 1)) -- instance order issue
abbrev plink (n:Type*)[Fintype n][LinearOrder n](k:ℕ) (a:ℝ):=naked (n:=n) (steel k (2*a))
lemma pearl{a:ℝ}(h:|c| ≤ a)(p:a ≤ 1): Rigid (fun _=> PearL n c) k x (dial n k) ∧ Rigid (fun _=>PearL n c-1) k x (plink n k a):=by
 have ht:‖Complex.exp c‖≤Real.exp 1:=by rw [Complex.norm_exp,Complex.ofReal_re]; exact Real.exp_monotone ((le_abs_self c).trans (h.trans p))
 have hz:‖Complex.exp ↑c-1‖ ≤ 2*a:=by rw [←Complex.ofReal_exp,show (1:ℂ)= (1:ℝ) from rfl,←Complex.ofReal_sub,Complex.norm_real]; exact (Real.abs_exp_sub_one_le (h.trans p)).trans (mul_le_mul_of_nonneg_left h (by norm_num))
 have hv:PearL n c-1=Pastry.hollow (n:=n) (Complex.exp ↑c-1):=by apply Subtype.ext; change _ • (1:FC n) - 1 = _ • (1:FC n); rw [sub_smul, one_smul]
 rw [hv]; exact ⟨peels (Jet.allows_const _ ht),peels (Jet.allows_const _ hz)⟩ -- hc amp
lemma pearl0 (i:E) (n:Type*)[LinearOrder n][Fintype n]: Rigid (fun _=> (0: Dough n)) k i 0:=Woody.empty _
variable {a b:ℝ}
variable (hx: |c|≤ a)(hp:a≤1)(hg:|d|≤b)(hr:b≤1)
variable {T S T' S': Raid n}(hw:Rigid F k x T)(hy:Rigid F' k x T)(he:Rigid (fun x=> F x+F' x) k x S)(hw':Rigid G k x T')(hy':Rigid H k x T')(he':Rigid (fun x=> G x+H x) k x S')
include hx hp hw hy he
abbrev bondG (F:E→↥(Dough n))(u:ℝ):= fun y=> (PearL n u-1) + PearL n u * F y
abbrev solo (k:ℕ)(W:Raid n):=skirt (dial n k) W
lemma lone_c: Rigid (fun y=> (bondG F c y -(Q-1))+(bondG F' c y -(Q-1))) k x (solo k S) :=by refine (((pearl (x:=x) (n:=n) (k:=k) c hx hp).1).pairP he).germ ?_; filter_upwards with y; exact congrArg Subtype.val (by unfold bondG; ring : Q*(F y + F' y)=_)
include hg hr hw' hy' he'
abbrev duet (k:ℕ)(a b:ℝ)(T S T' S':Raid n):=(((skirt (plink n k b) (solo k S)) + skirt (plink n k a) (solo k S'))+skirt (solo k T) (solo k T'))+ skirt (solo k T) (solo k T')
lemma duet_c: Rigid (fun y=> (bondG F c y*bondG G d y-(Q-1)*(U-1)) + (bondG F' c y*bondG H d y -(Q-1)*(U-1))) k x (duet k a b T S T' S'):=by
 obtain ⟨t,t'⟩:=pearl (x:=x) (n:=n) (k:=k) c hx hp; obtain ⟨u,u'⟩:=pearl (x:=x) (n:=n) (k:=k) d hg hr
 refine ((( (u'.pairP (t.pairP he)).addP (t'.pairP (u.pairP he')) ).addP ((t.pairP hw).pairP (u.pairP hw')) ).addP ((t.pairP hy).pairP (u.pairP hy'))).germ ?_; filter_upwards with i; exact congrArg Subtype.val (by unfold bondG; ring : (( (U-1)*(Q*(F i+F' i))+(Q-1)*(U*(G i+H i))) +(Q* F i)*(U*G i)) + (Q*F' i)*(U*H i)=_)
end YM.CF.Iva
