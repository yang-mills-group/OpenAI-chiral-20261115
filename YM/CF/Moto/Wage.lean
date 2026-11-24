import YM.CF.Hype.Axis
import YM.CF.Moto.Blade
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> LeanV (Single Kx)
open Hove Oath
local notation "QΦ"=> Rock Kx
variable (Pp: Op (Single (mid N B)))(U':InkD (mid N B))(o:Site (mid N B))(p q:Rock (mid N B))
abbrev Φrap (M:Side)(i:Site M)(l:ℕ):Scree.Hub M:=⟨(Cube.node i,Lattice.halo l {Cube.node i}),halo_subset _ _ (mem_singleton_self _)⟩
def cashF (Z:Op (Single (mid N B)))(V: Pane (mid N B)): FC (LeanV (Single Kx)):=∑ i:QΦ,∑ j:QΦ,cars_P i j V (boxM Z i j)
abbrev pay_Y (Z:Op (Single (mid N B)))(V:Pane (mid N B)):Cipher (mid N B):=⟨cashF Z V, Flour.sum _ (fun i _=> Flour.sum _ fun j _ => (show Flour univ _ from Flour.sum _ (fun a (_:a∈(univ:Finset SU.Slot))=> Flour.sum _ fun b (_:b∈(univ:Finset SU.Slot)) =>(Flour.putPut univ (mem_univ (true,(i,a))) (mem_univ (false,(j,b)))).smul _)))⟩ -- tune type i nested
lemma bail_m(U:Pane (mid N B)): crumb (pay_Y Pp U).val ∅=0:=by
 change crumb (cashF Pp U) _= _; unfold cashF cars_P lineY; simp_rw [crumb_sum]
 exact sum_eq_zero fun i _=>sum_eq_zero fun j _=>sum_eq_zero fun a _=>sum_eq_zero fun b _=>urn_drop (i,a) (j,b) ∅ (by rintro t; have h:=congrArg Finset.card t; simp [Haro.tray] at h) _
lemma hail_K : Haro.orbitPH (pay_Y Pp 1)= Pp:=by
 have hf: cashF Pp 1=∑ i:Single Kx,∑ j:Single Kx,Pp i j • gateY i j:=by
    unfold cashF; simp_rw [roll_P,lineY]; conv_rhs=> rw [Fintype.sum_prod_type]
    conv_rhs=> arg 2; ext; arg 2; ext; rw [Fintype.sum_prod_type]
    congr 1; funext i; rw [sum_comm (s:=(univ:Finset QΦ)) (t:=(univ:Finset SU.Slot))]; rfl -- tune conv layout
 ext i j
 let T:=Haro.tray i j; rw [orbitPH,Matrix.of_apply,Prism.port_eq, if_neg]; swap; · simp
 have hx: crumb (cashF Pp 1) T= crumb (Pp i j • gateY i j) T:=by
    rw [hf]; simp_rw [crumb_sum]; rw [sum_eq_single i]; swap; · intro k _ v; exact sum_eq_zero (fun l _=>urn_drop _ _ _ (fun h=> v (Prod.mk.inj (tray_in (a₁:=(k,l)) (a₂:=(i,j)) h.symm)).1) _)
    rotate_left; · simp
    rw [sum_eq_single j]; intro k _ q; exact urn_drop _ _ _ (fun h=> q (Prod.mk.inj (tray_in (a₁:=(i,k)) (a₂:=(i,j)) h.symm)).2) _; simp
 change handY i j * crumb (cashF Pp 1) T= _; rw [hx,Oath.reel,crumb_scale,crumb_scale,Pastry.chip, if_pos rfl,mul_one,mul_left_comm,handY, parity_sq,mul_one] -- tune
variable (Xp:BudgetPoint)(u:v>0)(h:ℕ)
local notation "VΦ"=> Φrap (mid N B) o (10*h)
local notation "yΦ"=> (VΦ).val.2
variable (d:ℝ)(w:Fit o Xp.power h d Pp)
local notation "qG"=> node o
include w
lemma marks(P:p=p)(v:boxM Pp p q ≠0): separation qG (posG p)≤2*h∧ separation qG (posG q)≤2*h:=by
 by_contra u; refine v (Matrix.ext fun i j=>?_) -- contradiction target False
 by_contra l; have ht:= (w.2.2 (p,i) (q,j) l); rw [show posG p=node p.1 from rfl, show posG q=node q.1 from rfl, ζdist, ζdist] at u; exact u ⟨Nat.mul_le_mul_left _ ht.1, Nat.mul_le_mul_left _ ht.2⟩
lemma ħ_S (V:0 ≤ h): Shrine (mid N B) yΦ (cashF Pp):=by
 refine Shrine.yearT _ _ _ fun i (_:i∈(univ:Finset QΦ))=> Shrine.yearT _ _ _ fun j (_:j∈(univ:Finset QΦ))=>?_
 let S:=boxM Pp i j; by_cases z:S=0
 · have he(U):cars_P i j U (boxM Pp i j)=0:=by rw [show boxM _ _ _= _ from z]; exact thaw_v U i j
   simp_rw [he]; exact Shrine.emptyT _ _
 obtain ⟨hp,u⟩:= marks Pp o i j Xp h d w rfl z
 refine car_S i j S yΦ (fun f=> Moto.cap_c _ f w.2.1 i j) (show reelQ _ _ ⊆ Lattice.halo (10*h) {qG} from (visit_p _ _ _ (2*h) hp u).trans (Corona.halo_mono (by omega) (Subset.refl _))) (halo_spec.mpr ⟨_,mem_singleton_self _,hp.trans (by omega)⟩) (halo_spec.mpr ⟨_,mem_singleton_self _,u.trans (by omega)⟩) -- qT course
omit w
local notation "Ξ"=> radiusB x
variable (K₀:ℕ)(Ω:Gala Xp.power k K₀ x 3)(vP:16*h≤ K₀*(1+radiusB x))
local notation "pLine"=> (Feu.lineP Xp qG yΦ (radiusB x))
local notation "QL"=> boxM Pp p q
local notation "T_"=> manifest k Pp p q
lemma blink_z (z:boxM Pp p q=0) (U:Pane (mid N B)) : cars_P p q U (boxM Pp p q)=0 ∧ manifest k Pp p q=0:=by
 have hz: Oath.bow Pp p q=0:=by unfold Oath.bow; simp_rw [show ∀ i j:SU.Slot,Pp (p,i) (q,j)=0 from Matrix.ext_iff.mpr z]; simp
 rw [z]; exact ⟨thaw_v U p q,by unfold manifest; rw [hz,mul_zero]; simp⟩
include w Ω vP
lemma hoop_P (U:Pane (mid N B)) : Woody k (fun v:tangD (mid N B)=> cars_P p q (Vmove x U (pLine v)) QL) 0 T_:=by
 by_cases l:QL=0; · simp_rw [(blink_z (k:=k) Pp p q l _).1,(blink_z (k:=k) Pp p q l U).2]; exact Woody.empty _
 obtain ⟨z,t⟩:= marks Pp o p q Xp h d w rfl l; let Z:= shiftH (posG p) (posG q); have he:Z.length≤K₀*(1+radiusB x):=by have hp:=Font.short (posG p) (posG q); have hx:= separation_triangle (posG p) qG (posG q); rw [separation_comm _ qG] at hx; unfold Z; omega
 let Q:=boxM Pp p q; let M:=pLine; let A:=Oath.bow Pp p q; have hh:0 ≤ A:=by unfold A Oath.bow; positivity
 have hm:‖Q‖ ≤ Haro.horn*A:=Haro.soft 1 _ hh (fun i j=> (single_le_sum (fun j (_:j∈(univ:Finset SU.Slot))=> norm_nonneg (_:ℂ)) (mem_univ j)).trans (single_le_sum (fun i (_:i∈(univ:Finset SU.Slot))=>sum_nonneg (fun j _=> norm_nonneg (_:ℂ))) (mem_univ i)))
 let f(v:tangD (mid N B)):= Haro.taxi (Vmove x U (M v)) p q Q; have hp: Allows k f 0 (wheel_l k*(Haro.horn*A)*3):= leaf_h (fun _:tangD (mid N B)=> Q) _ (allows_const _ hm) (Ω U M (vscale Xp qG yΦ _ (VΦ).property) _ Z he) -- ht
 let g(u v:SU.Slot)(z:tangD (mid N B)):=f z u v; have hz(u v:SU.Slot): Pence k (g u v) 0 (γD k*A):= by unfold γD; rw [show ((k+1:ℝ)*wheel_l k* Haro.horn)*3*A = (k+1:ℝ)*(wheel_l k*(Haro.horn*A)*3) from (by ring)]; exact Rue.bare_p _ _ (cape_l _ hp u v)
 have hu(u v:SU.Slot): Woody k (fun p':tangD Kx=> g u v p' •gateY (p,u) (q,v)) 0 (Pi.single (Haro.tray (p,u) (q,v)) (γD k*A)):=by
    let r:Single (mid N B):=(p,u); let s: Single (mid N B):=(q,v); let M':=Haro.tray r s; let y:=handY r s
    refine ((Woody.chit M' (hz u v)).ride y (show ‖y‖=1 from (by simp [y,handY,parity]))).germ ?_; refine Eventually.of_forall fun i=>?_ ;change y • (g u v i • poke M')= _ ; rw [Oath.reel]; exact smul_comm ..
 apply (Woody.sumV (fun u _=> Woody.sumV (S:=univ) (fun v _=> hu u v))).germ; filter_upwards with v; unfold cars_P lineY; simp only [Finset.sum_apply]; rfl
end YM.CF.Moto
