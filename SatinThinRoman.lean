import SatinThinTrees
import SatinThinCrystal
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis.Head.Etch
variable (i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
open Again Buffered.Afterglow.Tower.SlabMark
variable {A b z U u:ℝ} {m j:ℕ} (p:f ≤ r)(x:r ≤ v)(l:List (Site (side Y i f)))
-- coordinates card independent of v support width
lemma growingM (p:f≤v): (side Y i f).val ≤ (side Y i v).val:=by
 induction p with | refl=> rfl | step t ih=> apply le_trans ih; refine le_trans (Nat.le_mul_of_pos_right _ P.R.L.property) ?_; exact ((Vale.apt (Y.ir i) P.block P.R.L _).exact_size).ge -- orientation (.ge of eq?)
lemma hailW{U ε:ℝ}(q:0<ε)(p:0≤ U)(u:U*(16/ε)≤(side Y i v).val)(t:j≤ (More (side Y i v)).val^4) : Tower.SlabMark.iceRate Y v i*U^j≤ ε^j:=by
 let a:=U/ε; have hp:U ≤ Real.exp a*ε:=(div_le_iff₀ q).mp ((le_add_of_nonneg_right (zero_le_one' ℝ)).trans (Real.add_one_le_exp _)); apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p hp _) (Real.exp_pos _|>.le))
 let n:= side Y i v; let M: ℝ:= n.val; rw [mul_pow,←Real.exp_nat_mul,←mul_assoc]; rw [←Real.exp_add]; have hx: (j:ℝ) ≤ M^4*16:=by apply le_trans (Nat.cast_le.mpr t); change ((((n.val*2)^4:ℕ):ℝ))≤_; unfold M; push_cast; linarith
 have hz: a*16 ≤ M:=by
    apply le_trans ?_ u; exact le_of_eq (by unfold a; ring)
 have hv:a≥ 0:=div_nonneg p q.le; have h': -(M^5)+ j*a ≤0:=by nlinarith only [mul_le_mul_of_nonneg_right hx hv,mul_le_mul_of_nonneg_right hz (by positivity:0 ≤ M^4)]
 exact mul_le_of_le_one_left (pow_nonneg q.le _) (Real.exp_le_one_iff.mpr h')
local notation "ε"=> meterC (hat L P.x f)
local notation "Uα"=> gapMark Y i k b z p x
abbrev owedF (P:Preparation)(f:ℕ)(A:ℝ)(m:ℕ):= (slotFee P f)^m*Real.exp (8*A*m+1)
local notation "qG"=> owedF P f A m
-- approximation cost license. tolerance comparison independent height v & count. 
local notation "gξ"=> repeatD P ℓ (RootBook Y i k f).p.B
local notation "Kξ"=> plusAgain P.block (gξ)
lemma oval (l:List (Site (side Y i f)))(g:Ferry Y v i k): Envelope (l.map (gapMark Y i k b z p x)).prod:= (receipt_word (fun i'=> (message_support Y i k b z p x i' g.depth g.enters).2) l (S:=univ) fun _ _=> subset_univ _).env
lemma compass_clock (V:ShelterCost c Y f i k) (h:ReadDensity Y i k A p x b z u)(t1:d+plusAgain P.block (repeatD P ℓ (RootBook Y i k f).p.B)≤(side Y i f).val)(t2:14*meterC (hat L P.x f)*(((4*(d+Kξ):ℕ):ℝ))^4 ≤1)
 (H:Real.exp 1 ≤ P.x)(g:Ferry Y v i k)(a:IcePlot Y v i k)(t0: U*(16/owedF P f A m)≤ (side Y i v).val)
 (T:outdoor (rural (RootBook Y i k f).p.B) l)(F:l.length=m)(X:∀ x', ‖(l.map (gapMark Y i k b z p x)).prod x'‖≤ U) -- x shadows fix
 (Y':∀ i':Axis,cows i' (upperRoll l) d): ‖Journey.compass Y i k v (l.map Uα).prod‖ ≤ 3*qG:=by
 let n:= side Y i f; let B:=side Y i v; let Z:=solder Y i k g.depth v; let T':=Journey.compass Y i k v; let E:=Uα; let W L':=(List.map E L').prod; let V':= slotFee P f; let D':=qG
 have hk: 0 ≤ U:= (norm_nonneg ((W l) (1,1))).trans (X _); obtain ⟨_,_,p',m',_⟩:= V.load.health; have v':0<V':=p'; have t':0<D':= mul_pos (pow_pos v' _) (Real.exp_pos _); have he:∀ {j L'}, j≤(More B).val^4→(∀ t:Fields B,‖(W L') t‖≤ U^j)→ ‖T' (W L')-Z (W L')‖≤ D'^j:=fun {j L'} t Yk=> (a _ (W L') _ (oval Y i k p x L' g) Yk).trans (hailW Y i t' hk t0 t)
 obtain ⟨y,J,hG,hJ,cn,ym,a',v,hℕ⟩:=renewed (p:=E) (graceful_clock Y i k p x H g (RootBook Y i k f).p.B) l T Y' t1 X
 have hp:J ≤ (More B).val^4:= v.trans (pow_le_pow_left' (Nat.mul_le_mul_right 2 (growingM Y i (p.trans x))) _)
 let Yx:=4*(d+Kξ); have hy: sites n ≤ (J:ℝ)*(Yx:ℝ)^4:=by unfold sites; exact_mod_cast hℕ
 let aε:= ε; have ha:0 ≤ aε:=v'.le.trans m'; have hb:14*aε*(Yx:ℝ)^4≤1:=t2
 have h₀: ‖T' (W y)‖≤ D'^J:=by
    refine (gap_ticket Y i k p x y V h hG).trans ?_; rw [hJ,F]; change (slotFee P f)^(J*m)*Real.exp (4*A*(↑(2*(J*m)):ℝ)+14*aε*sites n)≤ ((slotFee P f)^m*Real.exp (8*A*m+1))^J; rw [mul_pow,←Real.exp_nat_mul, ←pow_mul, Nat.mul_comm J m]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg p'.le _); push_cast; apply Real.exp_monotone; nlinarith only [mul_le_mul_of_nonneg_left hy ha,mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) J)]
 have htp: ‖Z (W l)‖ ≤ 2*D':=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (n:=J) a'.ne').mp; apply ym.trans; refine ((norm_le_norm_sub_add (Z (W y)) (T' (W y))).trans (add_le_add ((norm_sub_rev ..).trans_le (he hp cn)) h₀)).trans ?_; change D'^J + D'^J ≤ (2*D')^J; rw [mul_pow 2 D',←two_mul]; refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg t'.le _); exact (show (2:ℝ)=2^1 from pow_one _|>.symm).trans_le (pow_le_pow_right₀ (by norm_num) a')
 have hc: ‖T' (W l)-Z (W l)‖ ≤ D':=by simpa using (he (Nat.le_trans (Nat.succ_le_iff.mpr a') hp : 1 ≤ (More B).val^4) (L':=l) (by simpa using X)) -- X alias
 exact ((norm_le_norm_sub_add (T' (W l)) (Z (W l))).trans (add_le_add hc htp)).trans_eq (by ring)
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.compass_clock
