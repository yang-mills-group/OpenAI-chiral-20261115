import YM.CF.Vp929.Canon.Lapis
import YM.CF.Fixed.Voltage.Grant
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
set_option quotPrecheck false
open Cycle929 Larch Bake Salt Trees Push.BetaTransport
open AnalyticBridge.VerifiedReset.Collection
variable {n:Side}{L:ℕ}{Q:BudgetPoint}{A h a c d v α σ C Λ β j w:ℝ}
local notation "D'"=> RegBudget n
local notation "V'"=> Skye.Seat n
local notation "Gξ"=> SU.group
local notation "Px"=> Lattice.PlaqAxes
local notation "φ"=> AnalyticBridge.VerifiedReset.petals
local notation "H_"=> AnalyticBridge.VerifiedReset.heads
local notation "Z_"=> AnalyticBridge.VerifiedReset.counter
local notation "Lρ"=> Cash.prominence Q
variable {R:PathData SU.group}{b:Clip}(u:Cease Q R b α v σ C Λ n) (T:Ids n) (g:1 ≤ h)
local notation "Fr"=> c
local notation "Θ_"=> ΘK T Q R b (-1)
local notation "ℓ1"=> (lite_b n Q R b (-1))
local notation "ℓ2"=> (lit_P n Q R b (-1))
local notation "μr"=> (rate_b Q b σ C α (-1))
local notation "μp"=> (rate_h Q b σ C α (-1))
local notation "Λr"=> (rate_μ Q b σ C v (-1))
local notation "Kp"=> Push.BetaTransport.kinetic
namespace QuiltB
variable {F:Scree.Hub n→ Scree.Hub n}(p:Extension L Q n F)
local notation "CR"=> creditR Q R b n
local notation "CT"=> creditT Q R b T
def packR (Q:BudgetPoint)(R:PathData SU.group)(b:Clip) (F:Scree.Hub n→ Scree.Hub n):RegBudget n:=writ_E (warp_E F (creditR Q R b n))

abbrev packF (Q:BudgetPoint)(R:PathData SU.group)(b:Clip)(L:ℕ) (F:Scree.Hub n→ Scree.Hub n)(T:Ids n):Cusp n:=writ_K (ridge_Q Q L F (creditR Q R b n)+creditT Q R b T)
abbrev shipA (Q:BudgetPoint)(L:ℕ)(b:Clip)(σ C α:ℝ):=cone_D Q.order Q.power*(Real.exp (Q.supportExponent*mstar L)* accountR Q b α σ C)
abbrev shipT (Q:BudgetPoint)(L:ℕ)(b:Clip)(σ C α v:ℝ):ℝ:= let W:= Extension.wagon L Q.order (Cash.prominence Q) Q.B (accountR Q b α σ C)+ accountT Q b v σ C; W+tray_H Q.order*W
structure Piece (Q:BudgetPoint)(h:ℝ)(R: PathData SU.group)(b:Clip)(X:RegBudget n)(Y:Cusp n)(x t s:ℝ): Prop where
 hire: IncX Utrue X Q h t
 cannon: Packed Q h (Cash.prominence Q) Y s
 zealed:ZealQ Y
 delivers : PackSale Q R b X Y x
structure Kit (Q:BudgetPoint)(h:ℝ)(R: PathData SU.group)(b:Clip)(L:ℕ)(X:RegBudget n)(Y:Cusp n)(x t s:ℝ):Prop extends Piece Q h R b X Y x t s where
 rest: ∀ i:Scree.Hub n,shortHub Q L i → X i=0
local notation "G_"=> packR Q R b F
local notation "P_"=> packF Q R b L F T
local notation "rS" => shipA Q L b σ C α
local notation "kS" => shipT Q L b σ C α v
include g u p T
lemma makeGauge: Kit Q h R b L (G_) P_ 1 rS kS :=by
 obtain ⟨r,w,l,e,t⟩:=creditTune u T g; have hx:= zero_le_one.trans g; exact ⟨⟨ scalar_sweep (p.convoy _ _ r hx) (scalar_warp l) hx, packed_scalar ((p.canopy _ _ r hx (by unfold Cash.prominence; linarith [Q.exponent_pos])).add w) (plus_veil (warp_veil l) e) hx, stead_m _,fieldCare u (enroll p t)⟩,fun i t=> p.oldS (creditR Q R b n) i t⟩
omit g u p T
variable {X X':RegBudget n}{Y Y':Cusp n}
variable {p' y x' v' k t t' r r':ℝ}
lemma home_fleet {v:Pane n}(p:pingS Q.threshold univ v):FleetS Q.threshold v:=by
 intro i; apply ne_of_lt; apply p; rw [disjoint_comm]; intro q; exact Finset.disjoint_left.mp q (show i.1∈touched i from List.mem_toFinset.mpr List.mem_cons_self) (mem_univ _)
lemma Piece.quiet (p: Piece Q h R b X Y A c d)(x:Orbit n)(h:pingS Q.threshold univ x.1): exponentL Q X x.1=moldV n (A*Kp R b Q x.1):=by
 have he:=p.delivers x (home_fleet h); have hg: fuelV Q Y x=0:=by simp [fuelV,homeFlag h,Palot.fuelH]
 rwa [hg,add_zero] at he
local notation "τq"=> transverse (s:=n) A
local notation "lp"=> AnalyticBridge.VerifiedReset.line
lemma Piece.recordTurn (p: Piece Q h R b X Y A c d)(q:tangD n): (fun z:ℝ=>∑ i:Scree.Hub n,unRl (X i) (lp q z)) =ᶠ[𝓝 0] A • (Kp R b Q ∘ lp q):=by
 filter_upwards [homeS q Q, exponent_track q Q X] with i u t; let Z:= lp q i; let V:Orbit n:= (Z,Classical.arbitrary (Ids n)); rw [←t, p.quiet V u,Taxi.mon_v,hullB]; rfl
include g
lemma Piece.kinSmooth (p: Piece Q h R b X Y 1 c d)(q:tangD n): ContDiffAt ℝ 2 (Kp R b Q ∘ lp q) 0:= by
 have hv:=p.recordTurn q; rw [one_smul] at hv; exact (ContDiffAt.sum (f:=fun i:Scree.Hub n=> unRl (X i) ∘ lp q) (s:=univ) (fun i _=> by simpa only [Nat.cast_ofNat] using rind (ask_piece (Q:=Utrue) g X p.hire i) g q)).congr_of_eventuallyEq hv.symm
lemma Piece.bT (p:Piece Q h R b X Y A c d)(q:ℝ) (u:ContDiffAt ℝ 2 (Kp R b Q ∘ lp (transverse (s:=n) q)) 0): gaugeTest q X Q= A*kineticC n R b Q q:=by
 let o:=transverse (s:=n) q
 have hp := (exponent_track o Q X).trans (p.recordTurn o); have he:= hp.iteratedDeriv_eq (n:=2); rw [iteratedDeriv_const_smul (show ContDiffAt ℝ (↑(2:ℕ):ℕ∞ω) _ _ by norm_num; exact u)] at he
 unfold gaugeTest kineticC; rw [he]; change _ * (A* _) = _; ring
omit g
lemma sale_scale (q:PackSale Q R b X Y A)(x:ℝ) : PackSale Q R b (x • X) (x • Y) (x*A):=by
 intro V r; rw [show exponentL Q (x • X) V.1=x • exponentL Q X V.1 from ?_, show fuelV Q (x • Y) V=x • fuelV Q Y V from ?_,←smul_add,q V r,←map_smul]; · rw [mul_assoc]; rfl
 · unfold fuelV; rw [Finset.smul_sum]; rfl
 unfold exponentL; rw [Finset.smul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [numb_b,numb_b]; unfold Vow.march; split; rfl; exact (smul_zero _).symm
lemma zeal_r (z:ZealQ Y)(x:ℝ): ZealQ (x • Y) := fun s V p X D t l=> Eq.trans (congrArg (x • ·) (z s V p X D t l)) (map_smul _ _ _).symm
lemma wagePack (p:Packed Q h a Y c)(x:ℝ): Packed Q h a (x • Y) (|x| * c):=by obtain ⟨v,p,g⟩:=p; refine ⟨|x| • v,⟨fun i=>mul_nonneg (abs_nonneg _) (p.1 i), fun i D e z=>(p.2 i D e z).rum x⟩, fun i=>?_⟩; rw [tall_s]; exact mul_le_mul_of_nonneg_left (g _) (abs_nonneg _)
lemma Piece.scale (q: Piece Q h R b X Y A c d)(x:ℝ) : Piece Q h R b (x • X) (x • Y) (x*A) (|x| *c) (|x| *d):= ⟨ Fixed.Voltage.crestV Q Utrue q.hire x, wagePack q.cannon x, zeal_r q.zealed x, sale_scale q.delivers x⟩
lemma Piece.add (q: Piece Q h R b X Y A c d)(p: Piece Q h R b X' Y' x' t r) : Piece Q h R b (X+X') (Y+Y') (A+x') (c+t) (d+r):=by
 refine ⟨ Ione.addT Q q.hire p.hire,q.cannon.add p.cannon, Cash.zealAdd q.zealed p.zealed,?_⟩; intro i x; rw [ripe_H Q i,Vow.toast i,add_mul,map_add,← q.delivers i x,←p.delivers i x]; abel
lemma Kit.scale (p:Kit Q h R b L X Y A c d)(x:ℝ) : Kit Q h R b L (x • X) (x • Y) (x*A) (|x| *c) (|x| *d):=⟨p.toPiece.scale x,fun i v=>by simp only [Pi.smul_apply,p.rest i v,smul_zero]⟩
end QuiltB
end Test
end YM.CF.Py.Rate
